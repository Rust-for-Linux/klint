use std::cell::{Cell, RefCell};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_hir::LangItem;
use rustc_index::bit_set::BitSet;
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::mir::mono::MonoItem;
use rustc_mir_dataflow::JoinSemiLattice;
use rustc_session::{declare_tool_lint, impl_lint_pass};

use rustc_middle::mir::{BasicBlock, Body, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, SubstsRef, TyCtxt};
use rustc_mir_dataflow::{fmt::DebugWithContext, Analysis, AnalysisDomain};
use rustc_span::DUMMY_SP;

// A description of how atomic context analysis works.
//
// This analysis can be treated as checking the preemption count, except that the check is
// performed in compile-time and the checking is not disabled when compiling an non-preemptible
// kernel.
//
// We assign all functions two properties, one is the current preemption count that it expects,
// and another is the adjustment to the preemption count that it will make. For example, the majority
// of functions would have an adjustment of zero, and either makes no assumption to the preemption
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
// to make no adjustments to the preemption count, and all functions have no assumptions on the preemption count.
// If the functions do not satisfy the assumption, then escape hatch or manual annotation would be required.
// This assumption also means that when a function pointer is *created*, it must also satisfy the assumption.
// Similarly, as using traits with dynamic dispatch is also indirection, we would require explicit markings on
// trait method signatures.
//
// Now finally, recursion. If we want to properly handle recursion, then we are effectively going to find a fixed
// point globally in a call graph. This is not very practical, so we would instead require explicit markings on
// these recursive functions, and if unmarked, assume these functions to make no adjustments to the preemption
// count and have no assumptions on the preemption count.

struct PreemptionCountRange {
    lo: u32,
    hi: Option<u32>,
}

impl std::fmt::Display for PreemptionCountRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(hi) = self.hi {
            write!(f, "{}..{}", self.lo, hi)
        } else {
            write!(f, "{}..", self.lo)
        }
    }
}

/// Bounds of adjustments.
///
/// Conceptually this only needs a lower bound and an upper bound, but if we encounter code like this
/// ```ignore
/// while foo() {
///    enter_atomic();
/// }
/// ```
/// then the bounds will be `0..inf`, and the dataflow analysis will essentially never converge.
///
/// To avoid this we would only allow each bound to be changed once, and upon multiple change we would
/// instantly relax the bound to unbounded, which is not precise but will help the analysis converge.
#[derive(Clone, Copy, PartialEq, Eq)]
struct AdjustmentBounds {
    /// Lower bound of the adjustment, inclusive.
    lo: Option<i32>,
    /// Upper bound of the adjustment, exclusive.
    hi: Option<i32>,
}

impl AdjustmentBounds {
    fn is_empty(&self) -> bool {
        self.lo == Some(0) && self.hi == Some(0)
    }

    fn unbounded() -> Self {
        AdjustmentBounds { lo: None, hi: None }
    }

    fn offset(&self, offset: i32) -> Self {
        AdjustmentBounds {
            lo: self.lo.map(|x| x + offset),
            hi: self.hi.map(|x| x + offset),
        }
    }

    fn single_value(&self) -> Option<i32> {
        match *self {
            AdjustmentBounds {
                lo: Some(x),
                hi: Some(y),
            } if x + 1 == y => Some(x),
            _ => None,
        }
    }
}

impl Default for AdjustmentBounds {
    fn default() -> Self {
        Self {
            lo: Some(0),
            hi: Some(0),
        }
    }
}

impl std::fmt::Debug for AdjustmentBounds {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.lo, self.hi) {
            (Some(x), Some(y)) if x + 1 == y => write!(f, "{}", x),
            (Some(x), Some(y)) => write!(f, "{}..{}", x, y),
            (Some(x), None) => write!(f, "{}..", x),
            (None, Some(y)) => write!(f, "..{}", y),
            (None, None) => write!(f, ".."),
        }
    }
}

impl JoinSemiLattice for AdjustmentBounds {
    fn join(&mut self, other: &Self) -> bool {
        if other.is_empty() {
            return false;
        }

        if self.is_empty() {
            *self = *other;
            return true;
        }

        let mut changed = false;
        match (self.lo, other.lo) {
            // Already unbounded, no change needed
            (None, _) => (),
            // Same bound, no change needed
            (Some(a), Some(b)) if a == b => (),
            // Both bounded, but with different bounds (and both negative). To ensure convergence, relax to unbounded.
            (Some(a), Some(b)) if a < 0 && b < 0 => {
                self.lo = None;
                changed = true;
            }
            // Already have lower bound
            (Some(a), Some(b)) if a < b => (),
            // Adjust bound
            _ => {
                self.lo = other.lo;
                changed = true;
            }
        }

        match (self.hi, other.hi) {
            // Already unbounded, no change needed
            (None, _) => (),
            // Same bound, no change needed
            (Some(a), Some(b)) if a == b => (),
            // Both bounded, but with different bounds (and both positive). To ensure convergence, relax to unbounded.
            (Some(a), Some(b)) if a > 0 && b > 0 => {
                self.hi = None;
                changed = true;
            }
            // Already have upper bound
            (Some(a), Some(b)) if a > b => (),
            // Adjust bound
            _ => {
                self.hi = other.hi;
                changed = true;
            }
        }
        changed
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FunctionContextProperty {
    /// Range of preemption count that the function expects.
    ///
    /// Since the preemption count is a non-negative integer, the lower bound is just represented using a `u32`
    /// and "no assumption" is represented with 0; the upper bound is represented using an `Option<u32>`, with
    /// `None` representing "no assumption". The upper bound is exclusive so `(0, Some(0))` represents an
    /// unsatisfiable condition.
    assumptions: (u32, Option<u32>),
    adjustment: i32,
}

impl Default for FunctionContextProperty {
    fn default() -> Self {
        FunctionContextProperty {
            assumptions: (0, None),
            adjustment: 0,
        }
    }
}

struct AdjustmentComputation<'tcx, 'checker> {
    tcx: TyCtxt<'tcx>,
    checker: &'checker AtomicContext<'tcx>,
    body: &'tcx Body<'tcx>,
    instance: Instance<'tcx>,
    too_generic: Cell<bool>,
    min_entry_state: Cell<u32>,
    max_entry_state: Cell<Option<u32>>,
}

impl DebugWithContext<AdjustmentComputation<'_, '_>> for AdjustmentBounds {}

impl<'tcx> AnalysisDomain<'tcx> for AdjustmentComputation<'tcx, '_> {
    // The number here indicates the offset in relation to the function's entry point.
    type Domain = AdjustmentBounds;

    const NAME: &'static str = "atomic context";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        Default::default()
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        *state = AdjustmentBounds {
            lo: Some(0),
            hi: Some(1),
        };
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

fn saturating_sub(x: u32, y: i32) -> u32 {
    saturating_add(x, -y)
}

impl<'tcx> Analysis<'tcx> for AdjustmentComputation<'tcx, '_> {
    fn apply_statement_effect(
        &self,
        _state: &mut Self::Domain,
        _statement: &rustc_middle::mir::Statement<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
    }

    fn apply_terminator_effect(
        &self,
        state: &mut Self::Domain,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        let Some(cur_state) = state.lo else { return };

        let prop =
            match self
                .checker
                .resolve_function_property(self.instance, self.body, terminator)
            {
                Some(Some(v)) => v,
                Some(None) => {
                    // Too generic, need to bail out and retry after monomorphization.
                    *state = AdjustmentBounds::unbounded();
                    // Set flag to indicate that the analysis result is not reliable and don't generate errors.
                    self.too_generic.set(true);
                    return;
                }
                None => return,
            };

        let new_min_entry_state = std::cmp::max(
            self.min_entry_state.get(),
            saturating_sub(prop.assumptions.0, cur_state),
        );
        let new_max_entry_state = match (self.max_entry_state.get(), prop.assumptions.1) {
            (Some(x), Some(v)) => Some(std::cmp::min(x, saturating_sub(v, cur_state))),
            (Some(x), None) => Some(x),
            (None, Some(v)) => Some(saturating_sub(v, cur_state)),
            (None, None) => None,
        };

        if new_max_entry_state.is_some() && new_min_entry_state >= new_max_entry_state.unwrap() {
            // This function will cause the entry state to be in an unsatisfiable condition.
            // Generate an error.
            let span = terminator.source_info.span;
            let mut builder = self.tcx.sess.struct_span_err(
                span,
                format!(
                    "this function expects the preemption count to be in range {}",
                    PreemptionCountRange {
                        lo: prop.assumptions.0,
                        hi: prop.assumptions.1,
                    }
                ),
            );

            builder.note(format!(
                "but the possible preemption count at this function call is {}",
                PreemptionCountRange {
                    lo: saturating_add(self.min_entry_state.get(), cur_state),
                    hi: self
                        .max_entry_state
                        .get()
                        .map(|v| saturating_add(v, cur_state)),
                }
            ));

            builder.emit();
        }

        self.min_entry_state.set(std::cmp::max(
            self.min_entry_state.get(),
            saturating_sub(prop.assumptions.0, cur_state),
        ));
        if let Some(v) = prop.assumptions.1 {
            self.max_entry_state.set(match self.max_entry_state.get() {
                Some(x) => Some(std::cmp::min(x, saturating_sub(v, cur_state))),
                None => Some(saturating_sub(v, cur_state)),
            });
        }
        *state = state.offset(prop.adjustment);
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_mir_dataflow::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}

declare_tool_lint! {
    pub klint::ATOMIC_CONTEXT,
    Deny,
    ""
}

enum EvaluationStatus<T> {
    Complete(T),
    TooGeneric,
    Evaluating,
}

pub struct AtomicContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    cache: RefCell<FxHashMap<Instance<'tcx>, EvaluationStatus<FunctionContextProperty>>>,
}

enum ResolveResult<'tcx> {
    Ok(Instance<'tcx>),
    TooGeneric,
    IndirectCall,
}

impl<'tcx> AtomicContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            cache: RefCell::new(FxHashMap::default()),
        }
    }

    fn resolve_function(
        &self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<ResolveResult<'tcx>> {
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(body, self.tcx);
                let callee_ty = instance.subst_mir(self.tcx, &callee_ty);
                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    let func =
                        ty::Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), def_id, substs)
                            .unwrap();
                    match func {
                        Some(func) => Some(ResolveResult::Ok(func)),
                        None => Some(ResolveResult::TooGeneric),
                    }
                } else {
                    Some(ResolveResult::IndirectCall)
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(body, self.tcx).ty;
                let ty = instance.subst_mir(self.tcx, &ty);

                // Do not call `resolve_drop_in_place` directly as it does double unwrap.
                let def_id = self.tcx.require_lang_item(LangItem::DropInPlace, None);
                let substs = self.tcx.intern_substs(&[ty.into()]);
                let func =
                    ty::Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), def_id, substs)
                        .unwrap();

                match func {
                    Some(func) => Some(ResolveResult::Ok(func)),
                    None => Some(ResolveResult::TooGeneric),
                }
            }
            _ => None,
        }
    }

    fn resolve_function_property(
        &self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<Option<FunctionContextProperty>> {
        match self.resolve_function(instance, body, terminator) {
            Some(ResolveResult::Ok(func)) => match self.property(func) {
                Some(v) => Some(Some(v)),
                None => Some(None),
            },
            Some(ResolveResult::TooGeneric) => Some(None),
            Some(ResolveResult::IndirectCall) => Some(Some(FunctionContextProperty {
                assumptions: (0, None),
                adjustment: 0,
            })),
            None => None,
        }
    }

    pub fn ffi_property(&self, symbol: &str) -> FunctionContextProperty {
        match symbol {
            "enter_atomic" => FunctionContextProperty {
                assumptions: (0, None),
                adjustment: 1,
            },
            "leave_atomic" => FunctionContextProperty {
                assumptions: (1, None),
                adjustment: -1,
            },
            "require_atomic" => FunctionContextProperty {
                assumptions: (1, None),
                adjustment: 0,
            },
            "require_not_atomic" => FunctionContextProperty {
                assumptions: (0, Some(1)),
                adjustment: 0,
            },
            _ => {
                // dbg!(symbol);
                // Other functions, assume no context change for now.
                FunctionContextProperty {
                    assumptions: (0, None),
                    adjustment: 0,
                }
            }
        }
    }

    pub fn property(&self, instance: Instance<'tcx>) -> Option<FunctionContextProperty> {
        // First try to resolve the instance with the identity substs.
        let identity = InternalSubsts::identity_for_item(self.tcx, instance.def_id());
        if instance.substs != identity {
            match self.property(Instance::new(instance.def_id(), identity)) {
                Some(v) => return Some(v),
                None => (),
            }
        }

        // Look up from cache.
        if let Some(v) = self.cache.borrow_mut().get_mut(&instance) {
            return match v {
                EvaluationStatus::Complete(v) => Some(*v),
                EvaluationStatus::TooGeneric => None,
                EvaluationStatus::Evaluating => {
                    // Recursion encountered.
                    *v = EvaluationStatus::Complete(Default::default());
                    Some(Default::default())
                }
            };
        }

        self.cache
            .borrow_mut()
            .insert(instance, EvaluationStatus::Evaluating);
        let result = self.compute_property(instance);
        // Insert into cache, even if the result is `None`, so we don't need to repeat evaluation later.
        match self.cache.borrow_mut().insert(
            instance,
            match result {
                Some(v) => EvaluationStatus::Complete(v),
                None => EvaluationStatus::TooGeneric,
            },
        ) {
            Some(EvaluationStatus::Evaluating) => (),
            _ => {
                if result != Some(Default::default()) {
                    let mut diag = self.tcx.sess.struct_span_err(
                        self.tcx.def_span(instance.def_id()),
                        "this function is recursive but carries no context specification",
                    );
                    diag.note(format!("Inferred as {:?}", result));
                    diag.emit();
                }
                return Some(Default::default());
            }
        }
        result
    }

    fn report_adjustment_infer_error(
        &self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        analysis_result: &rustc_mir_dataflow::ResultsCursor<
            'tcx,
            'tcx,
            AdjustmentComputation<'tcx, '_>,
        >,
    ) {
        // First step, see if there are any path that leads to a `return` statement have `Top` directly.
        // If so, just report this.
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => (),
                _ => continue,
            }

            let result = analysis_result.results().entry_set_for_block(b);
            if result.single_value().is_some() {
                continue;
            }

            let mut first_problematic_block = b;

            // Find out the first problematic block that causes `FlatSet::Top`.
            // Not using MIR basic block traversal here because we only want to traverse basic blocks that could reach this
            // return statement (we don't care about diverging control flow).
            let mut visited = BitSet::new_empty(body.basic_blocks.len());
            let mut stack = vec![b];
            while let Some(b) = stack.pop() {
                if !visited.insert(b) {
                    continue;
                }

                let result = analysis_result.results().entry_set_for_block(b);
                if result.single_value().is_none() {
                    first_problematic_block = b;
                    stack.extend(body.basic_blocks.predecessors()[b].iter().copied());
                }
            }

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
                "cannot infer preemption count adjustment at this point in function",
            );
            let mut count = 0;
            for prev_block in body.basic_blocks.predecessors()[first_problematic_block]
                .iter()
                .copied()
            {
                let terminator = body.basic_blocks[prev_block].terminator();

                // Compute the preemption count from this predecessor block.
                // This value is the entry state, so we need to re-apply the adjustment.
                let adjustment = analysis_result
                    .results()
                    .entry_set_for_block(prev_block)
                    .single_value()
                    .map(
                        |v| match self.resolve_function_property(instance, body, terminator) {
                            Some(Some(prop)) => v + prop.adjustment,
                            Some(None) => unreachable!(),
                            None => v,
                        },
                    );

                let mut msg = match adjustment {
                    None => {
                        format!("preemption count adjustment is changed in the previous iteration of the loop")
                    }
                    Some(v) => {
                        format!("preemption count adjustment is {v} after this")
                    }
                };

                match count {
                    0 => (),
                    1 => msg = format!("while {}", msg),
                    _ => msg = format!("and {}", msg),
                }
                count += 1;
                diag.span_note(
                    body.basic_blocks[prev_block].terminator().source_info.span,
                    msg,
                );
            }
            diag.emit();
            return;
        }

        // A catch-all error. MIR building usually should just have one `Return` terminator
        // so this usually shouldn't be reached.
        self.tcx
            .sess
            .struct_span_err(
                self.tcx.def_span(instance.def_id()),
                "cannot infer preemption count adjustment of this function",
            )
            .emit();
    }

    pub fn compute_property(&self, instance: Instance<'tcx>) -> Option<FunctionContextProperty> {
        if self.tcx.is_foreign_item(instance.def_id()) {
            let name = self.tcx.def_path_str(instance.def_id());
            return Some(self.ffi_property(&name));
        }

        if !crate::monomorphize_collector::should_codegen_locally(self.tcx, &instance) {
            return Some(Default::default());
        }

        // dbg!(instance);
        let mir = self.tcx.instance_mir(instance.def);
        // dbg!(mir);
        let analysis_result = AdjustmentComputation {
            tcx: self.tcx,
            checker: self,
            body: mir,
            instance,
            too_generic: Cell::new(false),
            min_entry_state: Cell::new(0),
            max_entry_state: Cell::new(None),
        }
        .into_engine(self.tcx, mir)
        .iterate_to_fixpoint()
        .into_results_cursor(mir);

        let analysis = analysis_result.analysis();

        if analysis.too_generic.get() {
            // self.tcx
            //     .sess
            //     .struct_span_warn(
            //         self.tcx.def_span(instance.def_id()),
            //         format!("function too generic ({:?})", instance),
            //     )
            //     .emit();
            return None;
        }

        // Gather assumptions.
        let mut min_entry_state = analysis.min_entry_state.get();
        let mut max_entry_state = analysis.max_entry_state.get();
        if max_entry_state.is_some() && min_entry_state >= max_entry_state.unwrap() {
            self.tcx
                .sess
                .struct_span_err(
                    self.tcx.def_span(instance.def_id()),
                    "cannot infer context assumption for function",
                )
                .emit();

            // For failed inference, revert to the default.
            min_entry_state = 0;
            max_entry_state = None;
        }

        // Gather adjustments.
        let mut adjustment = AdjustmentBounds::default();
        for (b, data) in rustc_middle::mir::traversal::reachable(mir) {
            match data.terminator().kind {
                TerminatorKind::Return => {
                    adjustment.join(analysis_result.results().entry_set_for_block(b));
                }
                _ => (),
            }
        }

        let adjustment = if adjustment.is_empty() {
            // Diverging function, any value is fine, use the default 0.
            0
        } else if let Some(v) = adjustment.single_value() {
            v
        } else {
            self.report_adjustment_infer_error(instance, mir, &analysis_result);
            0
        };

        // self.tcx
        //     .sess
        //     .struct_span_warn(
        //         self.tcx.def_span(instance.def_id()),
        //         format!(
        //             "function checked with {:?}, {}, {instance:?}",
        //             (min_entry_state, max_entry_state),
        //             adjustment
        //         ),
        //     )
        //     .emit();

        Some(FunctionContextProperty {
            assumptions: (min_entry_state, max_entry_state),
            adjustment: adjustment,
        })
    }
}

impl_lint_pass!(AtomicContext<'_> => [ATOMIC_CONTEXT]);

impl<'tcx> LateLintPass<'tcx> for AtomicContext<'tcx> {
    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        _: rustc_hir::HirId,
    ) {
        let def_id = cx.tcx.hir().body_owner_def_id(body.id());

        // Building MIR for `fn`s with unsatisfiable preds results in ICE.
        if crate::util::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let identity = InternalSubsts::identity_for_item(self.tcx, def_id.into());
        let instance = Instance::new(def_id.into(), identity);
        self.property(instance);
    }
}
