use rustc_hir::def_id::{CrateNum, DefId, DefIndex};
use rustc_hir::{Constness, LangItem};
use rustc_index::bit_set::BitSet;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::mir::{Body, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, Ty, TyCtxt};
use rustc_mir_dataflow::lattice::MeetSemiLattice;
use rustc_mir_dataflow::Analysis;
use rustc_mir_dataflow::JoinSemiLattice;
use rustc_session::{declare_tool_lint, impl_lint_pass};

use crate::attribute::PreemptionCount as PreemptionCountAttr;
use crate::ctxt::AnalysisCtxt;
use crate::preempt_count::{
    dataflow::{AdjustmentBounds, AdjustmentBoundsOrError, AdjustmentComputation},
    PolyDisplay, TooGeneric,
};

// A description of how atomic context analysis works.
//
// This analysis can be treated as checking the preemption count, except that the check is
// performed in compile-time and the checking is not disabled when compiling an non-preemptible
// kernel.
//
// We assign all functions two properties, one is the current preemption count that it expects,
// and another is the adjustment to the preemption count that it will make. For example, the majority
// of functions would have an adjustment of zero, and either makes no expectation to the preemption
// count or requires it to be zero. Taking a spinlock would have an adjustment of 1, and releasing a
// spinlock would have an adjustment of -1.
//
// In the ideal world all of these properties can be inferred from the source code, however it obviously
// is not practical. The difficulty (apart from some complex control flow) arise from:
// * Rust calls into C functions
// * C calls into Rust functions
// * Indirect function calls
// * Generic functions
// * Recursion
//
// Generic functions are tricky because it makes it impossible for us to assign the properties to a
// generic function. For example, in the following code
// ```
// fn foo<T, F: FnOnce() -> T>(f: F) -> T {
//     f()
// }
// ```
// the property of `foo` depends on `F`. If `F` takes a spinlock, e.g. `let guard = foo(|| spinlock.lock())`,
// then `foo` will have an adjustment of 1. But `F` could well be a no-op function and thus `foo` should
// have an adjustment of 0. One way around this would be to work with monomorphized function only, but that
// can require a lot of redundant checking since most functions should have a fixed context property regardless
// of the type parameters. The solution to the generic function would be to try infer the properties of a function
// without generic parameters substituted, and then if the check fails or encountered a type parameter (like `F`
// in the example above), we would bail out and try to re-check the function with substituted type parameters.
//
// The first three categories are more fundamental, because the indirection or FFI makes us unable to infer
// properties in the compile-time. We would therefore have to make some assumptions: all functions are considered
// to make no adjustments to the preemption count, and all functions have no expectations on the preemption count.
// If the functions do not satisfy the expectation, then escape hatch or manual annotation would be required.
// This assumption also means that when a function pointer is *created*, it must also satisfy the assumption.
// Similarly, as using traits with dynamic dispatch is also indirection, we would require explicit markings on
// trait method signatures.
//
// Now finally, recursion. If we want to properly handle recursion, then we are effectively going to find a fixed
// point globally in a call graph. This is not very practical, so we would instead require explicit markings on
// these recursive functions, and if unmarked, assume these functions to make no adjustments to the preemption
// count and have no expectations on the preemption count.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub struct ExpectationRange {
    pub lo: u32,
    pub hi: Option<u32>,
}

impl ExpectationRange {
    fn top() -> Self {
        Self { lo: 0, hi: None }
    }

    fn single_value(v: u32) -> Self {
        Self {
            lo: v,
            hi: Some(v + 1),
        }
    }

    fn is_empty(&self) -> bool {
        if let Some(hi) = self.hi {
            self.lo >= hi
        } else {
            false
        }
    }
}

impl MeetSemiLattice for ExpectationRange {
    fn meet(&mut self, other: &Self) -> bool {
        let mut changed = false;
        if self.lo < other.lo {
            self.lo = other.lo;
            changed = true;
        }

        match (self.hi, other.hi) {
            (_, None) => (),
            (None, Some(_)) => {
                self.hi = other.hi;
                changed = true;
            }
            (Some(a), Some(b)) => {
                if a > b {
                    self.hi = Some(b);
                    changed = true;
                }
            }
        }

        changed
    }
}

impl std::fmt::Display for ExpectationRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.lo, self.hi) {
            (lo, None) => write!(f, "{}..", lo),
            (lo, Some(hi)) if lo >= hi => write!(f, "unsatisfiable"),
            (lo, Some(hi)) if lo + 1 == hi => write!(f, "{lo}"),
            (lo, Some(hi)) => write!(f, "{}..{}", lo, hi),
        }
    }
}

impl std::ops::Add<AdjustmentBounds> for ExpectationRange {
    type Output = Self;

    fn add(self, rhs: AdjustmentBounds) -> Self::Output {
        Self {
            lo: match rhs.lo {
                None => 0,
                Some(bound) => saturating_add(self.lo, bound),
            },
            hi: self
                .hi
                .zip(rhs.hi)
                .map(|(hi, bound)| saturating_add(hi, bound - 1)),
        }
    }
}

impl std::ops::Sub<AdjustmentBounds> for ExpectationRange {
    type Output = Self;

    fn sub(self, rhs: AdjustmentBounds) -> Self::Output {
        Self {
            lo: match rhs.lo {
                None => 0,
                Some(bound) => saturating_add(self.lo, -bound),
            },
            hi: match (self.hi, rhs.hi) {
                (None, _) => None,
                (_, None) => Some(0),
                (Some(hi), Some(bound)) => Some(saturating_add(hi, 1 - bound)),
            },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Encodable, Decodable)]
pub struct FunctionContextProperty {
    /// Range of preemption count that the function expects.
    ///
    /// Since the preemption count is a non-negative integer, the lower bound is just represented using a `u32`
    /// and "no expectation" is represented with 0; the upper bound is represented using an `Option<u32>`, with
    /// `None` representing "no expectation". The upper bound is exclusive so `(0, Some(0))` represents an
    /// unsatisfiable condition.
    pub expectation: ExpectationRange,
    pub adjustment: i32,
}

impl Default for FunctionContextProperty {
    fn default() -> Self {
        FunctionContextProperty {
            expectation: ExpectationRange::top(),
            adjustment: 0,
        }
    }
}

fn saturating_add(x: u32, y: i32) -> u32 {
    let (res, overflow) = x.overflowing_add(y as u32);
    if overflow == (y < 0) {
        res
    } else if overflow {
        u32::MAX
    } else {
        0
    }
}

declare_tool_lint! {
    pub klint::ATOMIC_CONTEXT,
    Deny,
    ""
}

enum ResolveResult<'tcx> {
    Ok(Instance<'tcx>),
    TooGeneric,
    IndirectCall,
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)))]
    fn drop_preempt_count_expectation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<ExpectationRange, TooGeneric> {
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no expectation.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(ExpectationRange::top());
        }

        match ty.kind() {
            ty::Closure(_, substs) => (),

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(list) => (),

            ty::Adt(def, _) => {
                // For Adts, we first try to not use any of the substs and just try the most
                // polymorphic version of the type.
                let poly_param_env = cx.param_env_reveal_all_normalized(def.did());
                let poly_substs =
                    cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, def.did()));
                let poly_poly_ty = poly_param_env.and(cx.tcx.mk_ty(ty::Adt(*def, poly_substs)));
                if poly_poly_ty != poly_ty {
                    if let Ok(expectation) = cx.drop_preempt_count_expectation(poly_poly_ty) {
                        return Ok(expectation);
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.
            }

            ty::Dynamic(..) => {
                cx.sess.warn(format!(
                    "klint cannot yet check drop of dynamically sized `{}`",
                    PolyDisplay(&poly_ty)
                ));
                return Ok(ExpectationRange::top());
            }

            ty::Array(elem_ty, size) => {
                let size = size.try_eval_usize(cx.tcx, param_env).ok_or(TooGeneric);
                if size == Ok(0) {
                    return Ok(ExpectationRange::top());
                }

                let param_and_elem_ty = param_env.and(*elem_ty);
                let elem_adj = cx.drop_adjustment(param_and_elem_ty)?;
                let elem_exp = cx.drop_preempt_count_expectation(param_and_elem_ty)?;
                if elem_adj == 0 {
                    return Ok(elem_exp);
                }

                // TODO: deal with this case without using the MIR based logic.
            }

            ty::Slice(elem_ty) => {
                // We can assume adjustment here is 0 otherwise the adjustment calculation
                // logic would have complained.
                return cx.drop_preempt_count_expectation(param_env.and(*elem_ty));
            }

            _ => return Err(TooGeneric),
        }

        // Do not call `resolve_drop_in_place` because we need param_env.
        let drop_in_place = cx.require_lang_item(LangItem::DropInPlace, None);
        let substs = cx.intern_substs(&[ty.into()]);
        let instance = ty::Instance::resolve(cx.tcx, param_env, drop_in_place, substs)
            .unwrap()
            .unwrap();

        assert!(matches!(
            instance.def,
            ty::InstanceDef::DropGlue(_, Some(_))
        ));

        if cx.eval_stack.borrow().contains(&instance) {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(ExpectationRange::top());
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        cx.eval_stack.borrow_mut().push(instance);
        let result = cx
            .compute_property(param_env, instance)
            .map(|x| x.expectation);

        // Recursion encountered.
        if let Some(&recur) = cx
            .query_cache::<drop_preempt_count_expectation>()
            .borrow()
            .get(&poly_ty)
        {
            match (result, recur) {
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(exp), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        ty.ty_adt_def()
                            .map(|x| cx.def_span(x.did()))
                            .unwrap_or_else(|| cx.def_span(instance.def_id())),
                        "dropping this type causes recursion while also has preemption count expectation",
                    );
                    diag.note(format!("expectation inferred is {}", exp));
                    diag.note(format!("type being dropped is `{}`", ty));
                    diag.emit();
                }
            }
        }

        cx.eval_stack.borrow_mut().pop();
        result
    }
);

impl<'tcx> AnalysisCtxt<'tcx> {
    fn resolve_function(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<ResolveResult<'tcx>> {
        let func = match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(body, self.tcx);
                let callee_ty = instance
                    .subst_mir_and_normalize_erasing_regions(self.tcx, param_env, callee_ty);
                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    let func = ty::Instance::resolve(self.tcx, param_env, def_id, substs).unwrap();
                    match func {
                        Some(func) => func,
                        None => {
                            warn!("Resolving function {callee_ty} returns too generic");
                            return Some(ResolveResult::TooGeneric);
                        }
                    }
                } else {
                    self.tcx.sess.span_warn(
                        terminator.source_info.span,
                        "klint cannot yet check indirect function calls",
                    );
                    return Some(ResolveResult::IndirectCall);
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(body, self.tcx).ty;
                let ty = instance.subst_mir_and_normalize_erasing_regions(self.tcx, param_env, ty);

                // Do not call `resolve_drop_in_place` directly as it does double unwrap.
                let def_id = self.tcx.require_lang_item(LangItem::DropInPlace, None);
                let substs = self.tcx.intern_substs(&[ty.into()]);
                let func = ty::Instance::resolve(self.tcx, param_env, def_id, substs).unwrap();

                match func {
                    Some(func) => func,
                    None => {
                        warn!("Resolving drop of {ty:?} returns too generic");
                        return Some(ResolveResult::TooGeneric);
                    }
                }
            }
            _ => return None,
        };
        match func.def {
            ty::InstanceDef::Virtual(..) => {
                self.tcx.sess.span_warn(
                    terminator.source_info.span,
                    "klint cannot yet check indirect function calls",
                );
                Some(ResolveResult::IndirectCall)
            }
            _ => Some(ResolveResult::Ok(func)),
        }
    }

    pub fn resolve_function_property(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<Result<FunctionContextProperty, TooGeneric>> {
        match self.resolve_function(param_env, instance, body, terminator) {
            Some(ResolveResult::Ok(func)) => {
                Some(self.instance_preempt_count_property(param_env.and(func)))
            }
            Some(ResolveResult::TooGeneric) => Some(Err(TooGeneric)),
            Some(ResolveResult::IndirectCall) => Some(Ok(FunctionContextProperty {
                expectation: ExpectationRange::top(),
                adjustment: 0,
            })),
            None => None,
        }
    }

    fn ffi_property(&self, instance: Instance<'tcx>) -> FunctionContextProperty {
        let symbol = self.symbol_name(instance).name;

        // Skip LLVM intrinsics
        if symbol.starts_with("llvm.") {
            return Default::default();
        }

        match symbol {
            // Interfacing between libcore and panic runtime
            "rust_begin_unwind" => Default::default(),
            // Basic string operations depended by libcore.
            "memcmp" => Default::default(),

            // Memory allocations glues depended by liballoc.
            // Allocation functions may sleep.
            "__rust_alloc" | "__rust_alloc_zeroed" | "__rust_realloc" |
            "__rg_alloc" | "__rg_alloc_zeroed" | "__rg_realloc" => FunctionContextProperty {
                expectation: ExpectationRange::single_value(0),
                adjustment: 0,
            },

            // Deallocation function will not sleep.
            "__rust_dealloc" | "__rg_dealloc" => Default::default(),

            "spin_lock" => FunctionContextProperty {
                expectation: ExpectationRange::top(),
                adjustment: 1,
            },
            "spin_unlock" => FunctionContextProperty {
                expectation: ExpectationRange { lo: 1, hi: None },
                adjustment: -1,
            },
            "__cant_sleep" => FunctionContextProperty {
                expectation: ExpectationRange { lo: 1, hi: None },
                adjustment: 0,
            },
            "__might_sleep" | "msleep" => FunctionContextProperty {
                expectation: ExpectationRange::single_value(0),
                adjustment: 0,
            },
            _ => {
                warn!("Unable to determine property for FFI function `{}`", symbol);

                // Other functions, assume no context change for now.
                FunctionContextProperty {
                    expectation: ExpectationRange::top(),
                    adjustment: 0,
                }
            }
        }
    }

    fn report_adjustment_infer_error(
        &self,
        instance: Instance<'tcx>,
        body: &'tcx Body<'tcx>,
        results: &mut rustc_mir_dataflow::ResultsCursor<
            'tcx,
            'tcx,
            AdjustmentComputation<'tcx, 'tcx, '_>,
        >,
    ) {
        // First step, see if there are any path that leads to a `return` statement have `Top` directly.
        let mut return_bb = None;
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => (),
                _ => continue,
            }

            results.seek_to_block_start(b);
            // We can unwrap here because if this function is called, we know that no paths to `Return`
            // can contain `TooGeneric` or `Error` otherwise we would have returned early (in caller).
            if results.get().unwrap().is_single_value().is_some() {
                continue;
            }

            return_bb = Some(b);
            break;
        }

        // A catch-all error. MIR building usually should just have one `Return` terminator
        // so this usually shouldn't happen.
        let Some(return_bb) = return_bb else {
            self.tcx
                .sess
                .struct_span_err(
                    self.tcx.def_span(instance.def_id()),
                    "cannot infer preemption count adjustment of this function",
                )
                .emit();

            return;
        };

        // Find the deepest single-value block in the dominator tree.
        let mut first_problematic_block = return_bb;
        let dominators = body.basic_blocks.dominators();
        loop {
            let b = dominators.immediate_dominator(first_problematic_block);
            if b == first_problematic_block {
                // Shouldn't actually happen because the entry block should always have a single value.
                break;
            }

            results.seek_to_block_start(b);
            if results.get().unwrap().is_single_value().is_some() {
                break;
            }
            first_problematic_block = b;
        }

        // For this problematic block, try use a span that closest to the beginning of it.
        let span = body.basic_blocks[first_problematic_block]
            .statements
            .first()
            .map(|x| x.source_info.span)
            .unwrap_or_else(|| {
                body.basic_blocks[first_problematic_block]
                    .terminator()
                    .source_info
                    .span
            });

        let mut diag = self.tcx.sess.struct_span_err(
            span,
            "cannot infer preemption count adjustment at this point",
        );

        let mut count = 0;
        for mut prev_block in body.basic_blocks.predecessors()[first_problematic_block]
            .iter()
            .copied()
        {
            results.seek_to_block_end(prev_block);
            let mut end_adjustment = results.get().unwrap();
            results.seek_to_block_start(prev_block);
            let mut start_adjustment = results.get().unwrap();

            // If this block has made no changes to the adjustment, backtrack to the predecessors block
            // that made the change.
            while start_adjustment == end_adjustment {
                let pred = &body.basic_blocks.predecessors()[prev_block];

                // Don't continue backtracking if there are multiple predecessors.
                if pred.len() != 1 {
                    break;
                }
                let b = pred[0];

                // Don't continue backtracking if the predecessor block has multiple successors.
                let terminator = body.basic_blocks[b].terminator();
                let successor_count = terminator.successors().count();
                let has_unwind = terminator.unwind().map(|x| x.is_some()).unwrap_or(false);
                let normal_successor = successor_count - has_unwind as usize;
                if normal_successor != 1 {
                    break;
                }

                prev_block = b;
                results.seek_to_block_end(prev_block);
                end_adjustment = results.get().unwrap();
                results.seek_to_block_start(prev_block);
                start_adjustment = results.get().unwrap();
            }

            let terminator = body.basic_blocks[prev_block].terminator();
            let span = match terminator.kind {
                TerminatorKind::Goto { .. } => {
                    // Goto terminator of `if .. { .. } else { .. }` has span on the entire expression,
                    // which is not very useful.
                    // In this case we use the last statement's span instead.
                    body.basic_blocks[prev_block]
                        .statements
                        .last()
                        .map(|x| x.source_info)
                        .unwrap_or_else(|| terminator.source_info)
                        .span
                }
                _ => terminator.source_info.span,
            };

            let mut msg = match start_adjustment.is_single_value() {
                None => {
                    format!("preemption count adjustment is changed in the previous iteration of the loop")
                }
                Some(_) => {
                    format!(
                        "preemption count adjustment is {:?} after this",
                        end_adjustment
                    )
                }
            };

            match count {
                0 => (),
                1 => msg = format!("while {}", msg),
                _ => msg = format!("and {}", msg),
            }
            count += 1;
            diag.span_note(span, msg);
        }
        diag.emit();
    }

    #[instrument(skip_all, fields(instance=%instance), ret)]
    pub fn compute_property(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
    ) -> Result<FunctionContextProperty, TooGeneric> {
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(Default::default()),
            // No drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(Default::default()),
            _ => (),
        }

        // Use annotation if available.
        let def_id = instance.def_id();
        let annotation = self.preemption_count_annotation(def_id);
        let mut adjustment = annotation.adjustment;
        let mut expectation = annotation.expectation;
        if adjustment.is_some() || expectation.is_some() {
            info!(
                "adjustment {:?} and expectation {:?} from annotation",
                adjustment, expectation
            );
        }

        assert!(crate::monomorphize_collector::should_codegen_locally(
            self.tcx, &instance
        ));

        let mir = match instance.def {
            ty::InstanceDef::DropGlue(def_id, Some(ty)) => self.tcx.arena.alloc(
                crate::mir::drop_shim::build_drop_shim(self.tcx, def_id, param_env, ty),
            ),
            ty::InstanceDef::Item(def_id) => self.analysis_mir(def_id.did),
            _ => self.analysis_instance_mir(instance.def),
        };

        info!(?instance);
        // rustc_middle::mir::pretty::write_mir_fn(
        //     self.tcx,
        //     mir,
        //     &mut |_, _| Ok(()),
        //     &mut std::io::stderr(),
        // )
        // .unwrap();
        let mut analysis_result = AdjustmentComputation {
            checker: self,
            body: mir,
            param_env,
            instance,
        }
        .into_engine(self.tcx, mir)
        .dead_unwinds(&BitSet::new_filled(mir.basic_blocks.len()))
        .iterate_to_fixpoint()
        .into_results_cursor(mir);

        // Gather adjustments.
        if !annotation.unchecked || adjustment.is_none() {
            let mut adjustment_infer = AdjustmentBoundsOrError::default();
            for (b, data) in rustc_middle::mir::traversal::reachable(mir) {
                match data.terminator().kind {
                    TerminatorKind::Return => {
                        adjustment_infer.join(&analysis_result.results().entry_set_for_block(b));
                    }
                    _ => (),
                }
            }
            let adjustment_infer = adjustment_infer.into_result()?;

            let adjustment_infer = if adjustment_infer.is_empty() {
                // Diverging function, any value is fine, use the default 0.
                0
            } else if let Some(v) = adjustment_infer.is_single_value() {
                v
            } else {
                self.report_adjustment_infer_error(instance, mir, &mut analysis_result);
                0
            };

            // If inferred value is not consistent with the annotation, report an error.
            if let Some(adjustment) = adjustment {
                if adjustment != adjustment_infer {
                    let mut diag = self.tcx.sess.struct_span_err(
                        self.tcx.def_span(instance.def_id()),
                        format!("function annotated to have preemption count adjustment of {adjustment}"),
                    );
                    diag.note(format!("but the adjustment inferred is {adjustment_infer}"));
                    diag.emit();
                }
            } else {
                adjustment = Some(adjustment_infer);
            }
        }

        // Gather expectations.
        if !annotation.unchecked || expectation.is_none() {
            let mut expectation_infer = ExpectationRange::top();
            for (b, data) in rustc_middle::mir::traversal::reachable(mir) {
                if data.is_cleanup {
                    continue;
                }

                match self.resolve_function_property(param_env, instance, mir, data.terminator()) {
                    Some(Ok(prop)) => {
                        let adj = analysis_result
                            .results()
                            .entry_set_for_block(b)
                            .into_result()?;

                        // We need to find a range that for all possible values in `adj`, it will end up in a value
                        // that lands inside `prop.expectation`.
                        //
                        // For example, if adjustment is `0..`, and range is `0..1`, then the range we want is `0..0`,
                        // i.e. an empty range, because no matter what preemption count we start with, if we apply an
                        // adjustment >0, then it will be outside the range.
                        let mut expected = prop.expectation - adj;
                        expected.meet(&expectation_infer);
                        if expected.is_empty() {
                            // This function will cause the entry state to be in an unsatisfiable condition.
                            // Generate an error.
                            let (kind, drop_span) = match data.terminator().kind {
                                TerminatorKind::Drop { place, .. } => {
                                    ("drop", Some(mir.local_decls[place.local].source_info.span))
                                }
                                _ => ("call", None),
                            };
                            let span = data.terminator().source_info.span;
                            let mut diag = self.tcx.sess.struct_span_err(
                                span,
                                format!(
                                    "this {kind} expects the preemption count to be {}",
                                    prop.expectation
                                ),
                            );

                            if let Some(span) = drop_span {
                                diag.span_label(span, "the value being dropped is declared here");
                            }

                            diag.note(format!(
                                "but the possible preemption count at this point is {}",
                                expectation_infer + adj
                            ));
                            diag.emit();

                            // For failed inference, revert to the default.
                            expectation_infer = ExpectationRange { lo: 0, hi: None };

                            // Stop processing other calls in this function to avoid generating too many errors.
                            break;
                        }
                        expectation_infer = expected;
                    }
                    Some(Err(TooGeneric)) => return Err(TooGeneric),
                    None => (),
                }
            }

            // If inferred value is not consistent with the annotation, report an error.
            if let Some(expectation) = expectation {
                let mut expectation_intersect = expectation_infer;
                expectation_intersect.meet(&expectation);
                if expectation_intersect != expectation {
                    let mut diag = self.tcx.sess.struct_span_err(
                        self.tcx.def_span(instance.def_id()),
                        format!(
                            "function annotated to have preemption count expectation of {}",
                            expectation
                        ),
                    );
                    diag.note(format!(
                        "but the expectation inferred is {expectation_infer}"
                    ));
                    diag.emit();
                }
            } else {
                expectation = Some(expectation_infer);
            }
        }

        Ok(FunctionContextProperty {
            expectation: expectation.unwrap(),
            adjustment: adjustment.unwrap(),
        })
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)))]
    pub fn instance_preempt_count_property<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<FunctionContextProperty, TooGeneric> {
        let (param_env, instance) = poly_instance.into_parts();
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(Default::default()),
            ty::InstanceDef::DropGlue(_, Some(ty)) => {
                let adj = cx.drop_adjustment(param_env.and(ty))?;
                let exp = cx.drop_preempt_count_expectation(param_env.and(ty))?;
                return Ok(FunctionContextProperty {
                    expectation: exp,
                    adjustment: adj,
                });
            }
            _ => (),
        }

        let identity_param_env = cx
            .param_env_reveal_all_normalized(instance.def_id())
            .with_constness(Constness::NotConst);
        let identity =
            cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, instance.def_id()));
        let mut generic = false;
        if !cx.trait_of_item(instance.def_id()).is_some() {
            let identity_instance =
                identity_param_env.and(Instance::new(instance.def_id(), identity));
            generic = identity_instance == poly_instance;
            if !generic {
                info!(
                    "attempt generic version {} {:?} {:?}",
                    PolyDisplay(&identity_instance),
                    identity_instance,
                    poly_instance
                );
                match cx.instance_preempt_count_property(identity_instance) {
                    Ok(v) => return Ok(v),
                    Err(TooGeneric) => (),
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            return Ok(cx.ffi_property(instance));
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.sql_load::<instance_preempt_count_property>(poly_instance) {
                return p;
            }

            warn!(
                "Unable to compute property of non-local function {:?}",
                instance
            );
            return Ok(Default::default());
        }

        if cx.eval_stack.borrow().contains(&instance) {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(Default::default());
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        cx.eval_stack.borrow_mut().push(instance);
        let result = cx.compute_property(param_env, instance);

        // Recursion encountered.
        if let Some(recur) = cx
            .query_cache::<instance_preempt_count_property>()
            .borrow()
            .get(&poly_instance)
        {
            if result != *recur {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    "this function is recursive but carries no context specification",
                );
                if let Ok(property) = result {
                    diag.note(format!(
                        "adjustment is inferred to be {} and expectation is inferred to be {}",
                        property.adjustment, property.expectation
                    ));
                }
                diag.emit();
            }
        }

        if instance.def_id().is_local() && (generic || param_env.caller_bounds().is_empty()) {
            cx.sql_store::<instance_preempt_count_property>(poly_instance, result);
        }

        if cx.should_report_preempt_count(instance.def_id()) {
            let mut diag = cx.sess.diagnostic().struct_note_without_error(format!(
                "reporting preemption count for instance `{}`",
                PolyDisplay(&poly_instance)
            ));
            diag.set_span(cx.def_span(instance.def_id()));
            if let Ok(property) = result {
                diag.note(format!(
                    "adjustment is inferred to be {} and expectation is inferred to be {}",
                    property.adjustment, property.expectation
                ));
            } else {
                diag.note("inference failed because this function is too generic");
            }
            diag.emit();
        }

        cx.eval_stack.borrow_mut().pop();
        result
    }
);

impl crate::ctxt::PersistentQuery for instance_preempt_count_property {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}

pub struct AtomicContext<'tcx> {
    cx: AnalysisCtxt<'tcx>,
}

impl<'tcx> AtomicContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            cx: AnalysisCtxt::new(tcx),
        }
    }
}

impl_lint_pass!(AtomicContext<'_> => [ATOMIC_CONTEXT]);

impl<'tcx> AnalysisCtxt<'tcx> {
    fn preemption_count_annotation_fallback(&self, def_id: DefId) -> PreemptionCountAttr {
        match self.crate_name(def_id.krate).as_str() {
            // Happens in a test environment where build-std is not enabled.
            "core" | "alloc" | "std" => (),
            _ => {
                warn!(
                    "Unable to retrieve preemption count annotation of non-local function {:?}",
                    def_id
                );
            }
        }
        Default::default()
    }
}

memoize!(
    pub fn preemption_count_annotation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: DefId,
    ) -> PreemptionCountAttr {
        let Some(local_def_id) = def_id.as_local() else {
            if let Some(v) = cx.sql_load::<preemption_count_annotation>(def_id) {
                return v;
            }
            return cx.preemption_count_annotation_fallback(def_id);
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.klint_attributes(hir_id).iter() {
            match attr {
                crate::attribute::KlintAttribute::PreemptionCount(pc) => {
                    return *pc;
                }
                _ => (),
            }
        }

        Default::default()
    }
);

impl crate::ctxt::PersistentQuery for preemption_count_annotation {
    type LocalKey<'tcx> = DefIndex;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key.krate, key.index)
    }
}

memoize!(
    pub fn should_report_preempt_count<'tcx>(cx: &AnalysisCtxt<'tcx>, def_id: DefId) -> bool {
        let Some(local_def_id) = def_id.as_local() else { return false };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.klint_attributes(hir_id).iter() {
            match attr {
                crate::attribute::KlintAttribute::ReportPreeptionCount => return true,
                _ => (),
            }
        }

        false
    }
);

impl<'tcx> LateLintPass<'tcx> for AtomicContext<'tcx> {
    fn check_crate(&mut self, _: &LateContext<'tcx>) {
        // Do this before hand to ensure that errors, if any, are nicely sorted.
        for &def_id in self.cx.mir_keys(()) {
            let _ = self.cx.preemption_count_annotation(def_id.to_def_id());
        }
    }

    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        _hir_id: rustc_hir::HirId,
    ) {
        let def_id = cx.tcx.hir().body_owner_def_id(body.id());

        // Building MIR for `fn`s with unsatisfiable preds results in ICE.
        if crate::util::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let identity = cx.tcx.erase_regions(InternalSubsts::identity_for_item(
            self.cx.tcx,
            def_id.into(),
        ));
        let instance = Instance::new(def_id.into(), identity);
        let _ = self.cx.instance_preempt_count_property(
            self.cx
                .param_env_reveal_all_normalized(def_id)
                .with_constness(Constness::NotConst)
                .and(instance),
        );
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            crate::monomorphize_collector::MonoItemCollectionMode::Eager,
        )
        .0;

        for mono_item in mono_items {
            if let MonoItem::Fn(instance) = mono_item {
                self.cx
                    .instance_preempt_count_property(ParamEnv::reveal_all().and(instance))
                    .expect("monomorphized function should not be too generic");
            }
        }

        self.cx.encode_mir();

        for &def_id in self.cx.mir_keys(()) {
            let annotation = self.cx.preemption_count_annotation(def_id.to_def_id());
            self.cx
                .sql_store::<preemption_count_annotation>(def_id.to_def_id(), annotation);
        }
    }
}
