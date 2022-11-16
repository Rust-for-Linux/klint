use std::cell::Cell;

use rustc_hir::def_id::LocalDefId;
use rustc_hir::LangItem;
use rustc_index::bit_set::BitSet;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::mir::{BasicBlock, Body, Terminator, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, TyCtxt};
use rustc_mir_dataflow::lattice::MeetSemiLattice;
use rustc_mir_dataflow::JoinSemiLattice;
use rustc_mir_dataflow::{fmt::DebugWithContext, Analysis, AnalysisDomain};
use rustc_serialize::{Decodable, Encodable};
use rustc_session::{declare_tool_lint, impl_lint_pass};

use crate::ctxt::AnalysisCtxt;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub struct PreemptionCountRange {
    pub lo: u32,
    pub hi: Option<u32>,
}

impl PreemptionCountRange {
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

impl MeetSemiLattice for PreemptionCountRange {
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

impl std::fmt::Display for PreemptionCountRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.lo, self.hi) {
            (lo, None) => write!(f, "{}..", lo),
            (lo, Some(hi)) if lo + 1 == hi => write!(f, "{lo}"),
            (lo, Some(hi)) => write!(f, "{}..{}", lo, hi),
        }
    }
}

impl std::ops::Add<AdjustmentBounds> for PreemptionCountRange {
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

impl std::ops::Sub<AdjustmentBounds> for PreemptionCountRange {
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

    fn is_single_value(&self) -> Option<i32> {
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Encodable, Decodable)]
pub struct FunctionContextProperty {
    /// Range of preemption count that the function expects.
    ///
    /// Since the preemption count is a non-negative integer, the lower bound is just represented using a `u32`
    /// and "no assumption" is represented with 0; the upper bound is represented using an `Option<u32>`, with
    /// `None` representing "no assumption". The upper bound is exclusive so `(0, Some(0))` represents an
    /// unsatisfiable condition.
    assumption: PreemptionCountRange,
    adjustment: i32,
}

impl Default for FunctionContextProperty {
    fn default() -> Self {
        FunctionContextProperty {
            assumption: PreemptionCountRange::top(),
            adjustment: 0,
        }
    }
}

struct AdjustmentComputation<'tcx, 'checker> {
    checker: &'checker AnalysisCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    instance: Instance<'tcx>,
    too_generic: Cell<bool>,
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
        location: rustc_middle::mir::Location,
    ) {
        // Skip all unwinding paths.
        if self.body.basic_blocks[location.block].is_cleanup {
            return;
        }

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

enum ResolveResult<'tcx> {
    Ok(Instance<'tcx>),
    TooGeneric,
    IndirectCall,
}

impl<'tcx> AnalysisCtxt<'tcx> {
    fn resolve_function(
        &self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<ResolveResult<'tcx>> {
        let func = match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(body, self.tcx);
                let callee_ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    ty::ParamEnv::reveal_all(),
                    callee_ty,
                );
                if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                    let func =
                        ty::Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), def_id, substs)
                            .unwrap();
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
                let ty = instance.subst_mir_and_normalize_erasing_regions(
                    self.tcx,
                    ty::ParamEnv::reveal_all(),
                    ty,
                );

                // Do not call `resolve_drop_in_place` directly as it does double unwrap.
                let def_id = self.tcx.require_lang_item(LangItem::DropInPlace, None);
                let substs = self.tcx.intern_substs(&[ty.into()]);
                let func =
                    ty::Instance::resolve(self.tcx, ty::ParamEnv::reveal_all(), def_id, substs)
                        .unwrap();

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
            ty::InstanceDef::DropGlue(_, Some(v))
                if !v.is_sized(
                    self.tcx.at(terminator.source_info.span),
                    ty::ParamEnv::reveal_all(),
                ) =>
            {
                // Drop of DST will recreate a self-recursive
                self.tcx.sess.span_warn(
                    terminator.source_info.span,
                    format!("klint cannot yet check DST drop (type = {v})"),
                );
                Some(ResolveResult::IndirectCall)
            }
            _ => Some(ResolveResult::Ok(func)),
        }
    }

    fn resolve_function_property(
        &self,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
        terminator: &Terminator<'tcx>,
    ) -> Option<Option<FunctionContextProperty>> {
        match self.resolve_function(instance, body, terminator) {
            Some(ResolveResult::Ok(func)) => match self.function_context_property(func) {
                Some(v) => Some(Some(v)),
                None => Some(None),
            },
            Some(ResolveResult::TooGeneric) => Some(None),
            Some(ResolveResult::IndirectCall) => Some(Some(FunctionContextProperty {
                assumption: PreemptionCountRange::top(),
                adjustment: 0,
            })),
            None => None,
        }
    }

    fn ffi_property(&self, symbol: &str) -> FunctionContextProperty {
        match symbol {
            "enter_atomic" | "bindings::spin_lock" => FunctionContextProperty {
                assumption: PreemptionCountRange::top(),
                adjustment: 1,
            },
            "leave_atomic" | "bindings::spin_unlock" => FunctionContextProperty {
                assumption: PreemptionCountRange { lo: 1, hi: None },
                adjustment: -1,
            },
            "require_atomic" => FunctionContextProperty {
                assumption: PreemptionCountRange { lo: 1, hi: None },
                adjustment: 0,
            },
            "require_not_atomic" | "bindings::msleep" => FunctionContextProperty {
                assumption: PreemptionCountRange::single_value(0),
                adjustment: 0,
            },
            _ => {
                warn!(symbol);
                // dbg!(symbol);
                // Other functions, assume no context change for now.
                FunctionContextProperty {
                    assumption: PreemptionCountRange::top(),
                    adjustment: 0,
                }
            }
        }
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
            if result.is_single_value().is_some() {
                continue;
            }

            // Find the deepest single-value block in the dominator tree.
            let mut first_problematic_block = b;
            let dominators = body.basic_blocks.dominators();
            loop {
                let b = dominators.immediate_dominator(first_problematic_block);
                if b == first_problematic_block {
                    // Shouldn't actually happen because the entry block should always have a single value.
                    break;
                }

                let result = analysis_result.results().entry_set_for_block(b);
                if result.is_single_value().is_some() {
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
                let adjust_calc = |bb| {
                    let terminator = body.basic_blocks[bb].terminator();

                    // Compute the preemption count from this predecessor block.
                    // This value is the entry state, so we need to re-apply the adjustment.
                    (
                        analysis_result
                            .results()
                            .entry_set_for_block(bb)
                            .is_single_value(),
                        match self.resolve_function_property(instance, body, terminator) {
                            Some(Some(prop)) => prop.adjustment,
                            Some(None) => unreachable!(),
                            None => 0,
                        },
                    )
                };

                let mut adjustment = adjust_calc(prev_block);

                // If this block has made no changes to the adjustment, backtrack to the parent block
                // that made the change.
                while adjustment.1 == 0 {
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
                    adjustment = adjust_calc(prev_block);
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

                let mut msg = match adjustment.0 {
                    None => {
                        format!("preemption count adjustment is changed in the previous iteration of the loop")
                    }
                    Some(v) => {
                        format!(
                            "preemption count adjustment is {} after this",
                            v + adjustment.1
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

    #[instrument(skip_all, fields(instance=%instance), ret)]
    pub fn compute_property(&self, instance: Instance<'tcx>) -> Option<FunctionContextProperty> {
        // No Rust built-in intrinsics will mess with preemption count.
        match instance.def {
            ty::InstanceDef::Intrinsic(_) => return Some(Default::default()),
            _ => (),
        }

        // None indicates that we need to infer them.
        let mut adjustment = None;
        let mut assumption = None;

        // Use annotation if available.
        let def_id = instance.def_id();
        if let Some(local_def_id) = def_id.as_local() {
            (adjustment, assumption) = self.preemption_count_annotation(local_def_id);

            if adjustment.is_some() || assumption.is_some() {
                info!(
                    "adjustment {:?} and assumption {:?} from annotation",
                    adjustment, assumption
                );
            }
        }

        assert!(crate::monomorphize_collector::should_codegen_locally(
            self.tcx, &instance
        ));

        let mir = match instance.def {
            ty::InstanceDef::DropGlue(_, _) => self.analysis_instance_mir(instance.def),
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
        let analysis_result = AdjustmentComputation {
            checker: self,
            body: mir,
            instance,
            too_generic: Cell::new(false),
        }
        .into_engine(self.tcx, mir)
        .dead_unwinds(&BitSet::new_filled(mir.basic_blocks.len()))
        .iterate_to_fixpoint()
        .into_results_cursor(mir);

        let analysis = analysis_result.analysis();

        if analysis.too_generic.get() {
            warn!("function too generic");
            return None;
        }

        // Gather adjustments.
        if adjustment.is_none() {
            let mut adjustment_infer = AdjustmentBounds::default();
            for (b, data) in rustc_middle::mir::traversal::reachable(mir) {
                match data.terminator().kind {
                    TerminatorKind::Return => {
                        adjustment_infer.join(analysis_result.results().entry_set_for_block(b));
                    }
                    _ => (),
                }
            }

            let adjustment_infer = if adjustment_infer.is_empty() {
                // Diverging function, any value is fine, use the default 0.
                0
            } else if let Some(v) = adjustment_infer.is_single_value() {
                v
            } else {
                self.report_adjustment_infer_error(instance, mir, &analysis_result);
                0
            };

            adjustment = Some(adjustment_infer);
        }

        // Gather assumptions.
        if assumption.is_none() {
            let mut assumption_infer = PreemptionCountRange::top();
            for (b, data) in rustc_middle::mir::traversal::reachable(mir) {
                if data.is_cleanup {
                    continue;
                }

                match self.resolve_function_property(instance, mir, data.terminator()) {
                    Some(Some(prop)) => {
                        let adj = *analysis_result.results().entry_set_for_block(b);

                        // We need to find a range that for all possible values in `adj`, it will end up in a value
                        // that lands inside `prop.assumption`.
                        //
                        // For example, if adjustment is `0..`, and range is `0..1`, then the range we want is `0..0`,
                        // i.e. an empty range, because no matter what preemption count we start with, if we apply an
                        // adjustment >0, then it will be outside the range.
                        let mut expected = prop.assumption - adj;
                        expected.meet(&assumption_infer);
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
                                    prop.assumption
                                ),
                            );

                            if let Some(span) = drop_span {
                                diag.span_label(span, "the value being dropped is declared here");
                            }

                            diag.note(format!(
                                "but the possible preemption count at this point is {}",
                                assumption_infer + adj
                            ));
                            diag.emit();

                            // For failed inference, revert to the default.
                            assumption_infer = PreemptionCountRange { lo: 0, hi: None };

                            // Stop processing other calls in this function to avoid generating too many errors.
                            break;
                        }
                        assumption_infer = expected;
                    }
                    Some(None) => unreachable!(),
                    None => (),
                }
            }
            assumption = Some(assumption_infer);
        }

        Some(FunctionContextProperty {
            assumption: assumption.unwrap(),
            adjustment: adjustment.unwrap(),
        })
    }

    #[instrument(skip(self))]
    fn store_property(&self, instance: Instance<'tcx>, property: Option<FunctionContextProperty>) {
        let mut enc = crate::serde::EncodeContext::new(self.tcx);
        instance.encode(&mut enc);
        let instance_enc = enc.finish();

        let mut enc = crate::serde::EncodeContext::new(self.tcx);
        property.encode(&mut enc);
        let property_enc = enc.finish();

        self.sql_conn
            .execute(
                "INSERT OR REPLACE INTO function_context_property (instance, property) VALUES (?, ?)",
                rusqlite::params![
                    instance_enc,
                    property_enc,
                ],
            )
            .unwrap();
    }

    #[instrument(skip(self))]
    fn load_property(&self, instance: Instance<'tcx>) -> Option<Option<FunctionContextProperty>> {
        use rusqlite::OptionalExtension;

        let mut enc = crate::serde::EncodeContext::new(self.tcx);
        instance.encode(&mut enc);
        let instance_enc = enc.finish();

        let property_enc: Vec<u8> = self
            .sql_conn
            .query_row(
                "SELECT property FROM function_context_property WHERE instance = ?",
                rusqlite::params![instance_enc,],
                |row| row.get(0),
            )
            .optional()
            .unwrap()?;
        let mut dec = crate::serde::DecodeContext::new(self.tcx, &property_enc);
        let property = <Option<_>>::decode(&mut dec);
        Some(property)
    }
}

memoize! {
    fn function_context_property<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        instance: Instance<'tcx>,
    ) -> Option<FunctionContextProperty> {
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Some(Default::default()),
            _ => (),
        }

        // This will ICE, disable for now.
        if false {
            let mut identity = InternalSubsts::identity_for_item(cx.tcx, instance.def_id());
            if cx.trait_of_item(instance.def_id()).is_some() {
                // Ensure the `Self` generic arg is kept.
                identity = cx.intern_substs(
                    &std::iter::once(instance.substs[0])
                        .chain(identity[1..].iter().copied())
                        .collect::<Vec<_>>(),
                );
            }
            if instance.substs != identity {
                match cx.function_context_property(Instance::new(instance.def_id(), identity)) {
                    Some(v) => return Some(v),
                    None => (),
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            let name = cx.def_path_str(instance.def_id());
            return Some(cx.ffi_property(&name));
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.load_property(instance) {
                return p;
            }

            warn!(
                "Unable to compute property of non-local function {:?}",
                instance
            );
            return Some(Default::default());
        }

        if cx.eval_stack.borrow().contains(&instance) {
            // Recursion encountered.
            return Some(Default::default());
        }

        cx.eval_stack.borrow_mut().push(instance);
        let result = cx.compute_property(instance);

        // Recursion encountered.
        if cx.function_context_property.borrow().contains_key(&instance) {
            if result != Some(Default::default()) {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    "this function is recursive but carries no context specification",
                );
                diag.note(format!("Inferred as {:?}", result));
                diag.emit();
            }
        }

        cx.store_property(instance, result);

        cx.eval_stack.borrow_mut().pop();
        result
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

memoize! {
    fn preemption_count_annotation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> (Option<i32>, Option<PreemptionCountRange>) {
        let hir = cx.hir();
        let hir_id = hir.local_def_id_to_hir_id(def_id);
        for attr in hir.attrs(hir_id) {
            let Some(attr) = crate::attribute::parse_klint_attribute(cx.tcx, hir_id, attr) else { continue };
            match attr {
                crate::attribute::KlintAttribute::PreemptionCount {
                    adjustment,
                    assumption,
                } => {
                    return (adjustment, assumption);
                }
            }
        }
        (None, None)
    }
}

impl<'tcx> LateLintPass<'tcx> for AtomicContext<'tcx> {
    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        _hir_id: rustc_hir::HirId,
    ) {
        // This will ICE, disable for now.
        if true {
            return;
        }

        let def_id = cx.tcx.hir().body_owner_def_id(body.id());

        // Building MIR for `fn`s with unsatisfiable preds results in ICE.
        if crate::util::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let identity = InternalSubsts::identity_for_item(self.cx.tcx, def_id.into());
        let instance = Instance::new(def_id.into(), identity);
        self.cx.function_context_property(instance);
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            crate::monomorphize_collector::MonoItemCollectionMode::Eager,
        )
        .0;

        for mono_item in mono_items {
            if let MonoItem::Fn(instance) = mono_item {
                self.cx.function_context_property(instance);
            }
        }

        self.cx.encode_mir();
    }
}
