// SPDX-License-Identifier: MIT OR Apache-2.0

use std::collections::VecDeque;

use rustc_ast::Mutability;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CrateNum, DefId, LocalDefId};
use rustc_hir::intravisit as hir_visit;
use rustc_hir::{Expr, HirId, QPath, UnOp};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::mir::{self, CastKind, Operand, TerminatorKind};
use rustc_middle::ty::{
    GenericArgs, Instance, PseudoCanonicalInput, Ty, TyCtxt, TypeckResults, TypingEnv,
};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::Span;

use crate::ctxt::{AnalysisCtxt, PersistentQuery};
use crate::diagnostic::use_stack::{UseSite, UseSiteKind};

declare_tool_lint! {
    pub klint::BUILD_ASSERT_NOT_INLINED,
    Warn,
    "function depends on build_assert! but is not marked #[inline(always)]"
}

const PRIMARY_MESSAGE: &str = "this function depends on non-static values used by `build_assert!` and should be marked `#[inline(always)]`; otherwise its error path may fail to optimize away";

#[derive(Diagnostic)]
#[diag("{$primary}")]
struct BuildAssertNotInlined {
    #[primary_span]
    #[suggestion(
        "mark this function `#[inline(always)]`",
        code = "{inline_attr}",
        applicability = "machine-applicable"
    )]
    pub fn_span: Span,
    #[subdiagnostic]
    pub origin_note: Option<BuildAssertOriginNote>,
    pub primary: &'static str,
    pub inline_attr: String,
}

#[derive(Subdiagnostic)]
enum BuildAssertOriginNote {
    #[note("`build_assert!` uses non-static values here and relies on the surrounding call chain being inlined")]
    Direct {
        #[primary_span]
        span: Span,
    },
    #[note("this call passes non-static values into `{$callee}` which must be inlined for `build_assert!` to optimize away")]
    Propagated {
        #[primary_span]
        span: Span,
        callee: String,
    },
}

/// This lint is about the source-level contract of user-authored functions, so only
/// `#[inline(always)]` counts as satisfying it.
pub(crate) fn has_inline_always(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.codegen_fn_attrs(def_id).inline.always()
}

fn inline_always_suggestion(cx: &LateContext<'_>, fn_span: Span) -> String {
    let indent = cx
        .sess()
        .source_map()
        .indentation_before(fn_span)
        .unwrap_or_default();
    format!("#[inline(always)]\n{indent}")
}

pub(crate) fn emit_build_assert_not_inlined(
    cx: &LateContext<'_>,
    def_id: LocalDefId,
    origin: Option<RequirementOrigin>,
) {
    let fn_span = cx.tcx.def_span(def_id);
    let inline_attr = inline_always_suggestion(cx, fn_span.shrink_to_lo());
    let origin_note = match origin {
        Some(RequirementOrigin::Direct { span }) => Some(BuildAssertOriginNote::Direct { span }),
        Some(RequirementOrigin::Propagated { callee, call_span }) => {
            Some(BuildAssertOriginNote::Propagated {
                span: call_span,
                callee: cx.tcx.def_path_str(callee),
            })
        }
        None => None,
    };

    cx.emit_span_lint(
        BUILD_ASSERT_NOT_INLINED,
        fn_span,
        BuildAssertNotInlined {
            fn_span: fn_span.shrink_to_lo(),
            origin_note,
            primary: PRIMARY_MESSAGE,
            inline_attr,
        },
    );
}

// Hot MIR dataflow state is cloned and merged frequently on large crates. A tiny linear set keeps
// the common small-cardinality cases cheap and avoids the hash-table churn that showed up in perf
// for this lint.
#[derive(Clone, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SmallSet<T>(Vec<T>);

impl<T> Default for SmallSet<T> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T: Copy + Eq> SmallSet<T> {
    fn insert(&mut self, value: T) -> bool {
        if self.0.contains(&value) {
            return false;
        }
        self.0.push(value);
        true
    }

    fn extend<I>(&mut self, iter: I) -> bool
    where
        I: IntoIterator<Item = T>,
    {
        let mut changed = false;
        for value in iter {
            changed |= self.insert(value);
        }
        changed
    }

    fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a, T> IntoIterator for &'a SmallSet<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<T> IntoIterator for SmallSet<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BuildAssertCondition {
    /// Span of the original `build_assert!(...)` invocation in source.
    pub call_site: Span,
    /// Span of the first macro argument, i.e. the asserted condition.
    pub condition_span: Span,
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub enum ExprDependency {
    #[default]
    Constant,
    Param(SmallSet<usize>),
    Runtime,
}

impl ExprDependency {
    /// Record that an expression depends on one specific function parameter.
    pub fn param(index: usize) -> Self {
        let mut params = SmallSet::default();
        params.insert(index);
        Self::Param(params)
    }

    /// Merge dependencies from subexpressions. Any runtime component dominates; otherwise we keep
    /// the union of parameter indices that still matter to the value.
    pub fn combine<I>(dependencies: I) -> Self
    where
        I: IntoIterator<Item = ExprDependency>,
    {
        let mut params = SmallSet::default();

        for dependency in dependencies {
            match dependency {
                ExprDependency::Constant => {}
                ExprDependency::Param(dep_params) => {
                    params.extend(dep_params.iter().copied());
                }
                ExprDependency::Runtime => return ExprDependency::Runtime,
            }
        }

        if params.is_empty() {
            ExprDependency::Constant
        } else {
            ExprDependency::Param(params)
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RequirementOrigin {
    Direct { span: Span },
    Propagated { callee: DefId, call_span: Span },
}

#[derive(Clone, Default, PartialEq, Eq)]
pub(crate) struct LocalDirectDiagnosticSummary {
    pub(crate) direct_requirement_origin: Option<RequirementOrigin>,
}

#[derive(Clone, Default)]
struct LocalInterestSummary {
    has_direct_build_assert: bool,
    direct_callees: FxHashSet<LocalDefId>,
    external_callees: FxHashSet<DefId>,
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SemanticRequirementSummary {
    pub(crate) param_dependencies: SmallSet<usize>,
    has_local_runtime_dependency: bool,
    has_unknown_dependency: bool,
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SemanticFunctionSummary {
    pub(crate) requirement: SemanticRequirementSummary,
    return_dependency: ExprDependency,
}

#[derive(Clone, Default)]
struct MirLocalState<'tcx> {
    dependency: ExprDependency,
    fn_targets: SmallSet<PseudoCanonicalInput<'tcx, Instance<'tcx>>>,
    dyn_receiver_tys: SmallSet<Ty<'tcx>>,
}

impl SemanticRequirementSummary {
    pub(crate) fn requires_inline(&self) -> bool {
        self.has_local_runtime_dependency || !self.param_dependencies.is_empty()
    }
}

fn poly_instance_of_def_id<'tcx>(
    cx: &AnalysisCtxt<'tcx>,
    def_id: DefId,
) -> PseudoCanonicalInput<'tcx, Instance<'tcx>> {
    let poly_typing_env = TypingEnv::post_analysis(cx.tcx, def_id);
    let poly_args = cx.erase_and_anonymize_regions(GenericArgs::identity_for_item(cx.tcx, def_id));
    poly_typing_env.as_query_input(Instance::new_raw(def_id, poly_args))
}

fn local_build_assert_body_owners(cx: &AnalysisCtxt<'_>) -> Vec<LocalDefId> {
    cx.hir_crate_items(())
        .owners()
        .filter_map(|owner| {
            let def_id = owner.def_id;
            (is_reportable_fn(cx.tcx, def_id) && cx.tcx.hir_maybe_body_owned_by(def_id).is_some())
                .then_some(def_id)
        })
        .collect()
}

fn exported_build_assert_body_owners(cx: &AnalysisCtxt<'_>) -> Vec<LocalDefId> {
    cx.local_build_assert_candidate_functions()
        .into_iter()
        .filter(|&def_id| {
            cx.tcx.visibility(def_id).is_public() || cx.tcx.is_reachable_non_generic(def_id)
        })
        .collect()
}

memoize!(
    fn local_build_assert_interest_summaries<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
    ) -> FxHashMap<LocalDefId, LocalInterestSummary> {
        let build_assert = cx.get_klint_diagnostic_item(crate::symbol::build_assert);
        let mut summaries = FxHashMap::default();

        for def_id in local_build_assert_body_owners(cx) {
            let body = cx.tcx.hir_body_owned_by(def_id);
            let typeck = cx.tcx.typeck(def_id);
            let mut visitor = LocalInterestVisitor::new(cx.tcx, &typeck, build_assert);
            hir_visit::Visitor::visit_body(&mut visitor, body);
            summaries.insert(def_id, visitor.finish());
        }

        summaries
    }
);

memoize!(
    fn local_build_assert_candidate_functions<'tcx>(cx: &AnalysisCtxt<'tcx>) -> Vec<LocalDefId> {
        let interest = cx.local_build_assert_interest_summaries();
        let mut reverse_edges: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
        let mut candidates = FxHashSet::default();
        let mut worklist = VecDeque::new();

        for (&caller, summary) in &interest {
            // Seed only from proven local/external build_assert dependence. Unsupported indirect
            // calls stay out of the slice unless they are reached from one of these seeds, which
            // avoids reintroducing the broad false positives and whole-crate work we had before.
            let calls_external_build_assert =
                summary.external_callees.iter().copied().any(|def_id| {
                    cx.build_assert_summary_for_def_id(def_id)
                        .is_some_and(|summary| summary.requirement.requires_inline())
                });

            if summary.has_direct_build_assert || calls_external_build_assert {
                if candidates.insert(caller) {
                    worklist.push_back(caller);
                }
            }

            for &callee in &summary.direct_callees {
                reverse_edges.entry(callee).or_default().push(caller);
            }
        }

        while let Some(def_id) = worklist.pop_front() {
            for &caller in reverse_edges.get(&def_id).into_iter().flatten() {
                if candidates.insert(caller) {
                    worklist.push_back(caller);
                }
            }
        }

        let mut candidates: Vec<_> = candidates.into_iter().collect();
        candidates.sort_by_key(|&def_id| cx.tcx.def_span(def_id).lo());
        candidates
    }
);

memoize!(
    pub(crate) fn local_build_assert_semantic_summaries<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
    ) -> FxHashMap<LocalDefId, SemanticFunctionSummary> {
        let body_owners = cx.local_build_assert_candidate_functions();
        tracing::debug!(
            body_owner_count = body_owners.len(),
            "computing local build_assert semantic summaries"
        );
        let mut summaries = FxHashMap::default();
        for &def_id in &body_owners {
            summaries.insert(def_id, SemanticFunctionSummary::default());
        }

        // Recursive local call graphs are summarized with a monotone fixpoint over the candidate
        // slice instead of bouncing back through the public query path.
        loop {
            let mut changed = false;

            for &def_id in &body_owners {
                let poly_instance = poly_instance_of_def_id(cx, def_id.to_def_id());
                let Some(summary) = cx.exact_instance_build_assert_summary_with_local_summaries(
                    poly_instance,
                    Some(&summaries),
                ) else {
                    continue;
                };

                if summaries.get(&def_id) != Some(&summary) {
                    summaries.insert(def_id, summary);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        summaries
    }
);

memoize!(
    pub(crate) fn local_direct_build_assert_diagnostics<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
    ) -> FxHashMap<LocalDefId, LocalDirectDiagnosticSummary> {
        let build_assert = cx.get_klint_diagnostic_item(crate::symbol::build_assert);
        let mut diagnostics = FxHashMap::default();

        for (&def_id, summary) in &cx.local_build_assert_interest_summaries() {
            if !summary.has_direct_build_assert {
                continue;
            }
            let body = cx.tcx.hir_body_owned_by(def_id);
            let typeck = cx.tcx.typeck(def_id);
            let mut visitor = DirectBuildAssertVisitor::new(cx.tcx, &typeck, build_assert);
            hir_visit::Visitor::visit_body(&mut visitor, body);
            diagnostics.insert(def_id, visitor.finish());
        }

        diagnostics
    }
);

memoize!(
    pub(crate) fn local_build_assert_propagated_origin_diagnostic<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> Option<RequirementOrigin> {
        cx.exact_local_build_assert_propagated_origin(poly_instance_of_def_id(
            cx,
            def_id.to_def_id(),
        ))
    }
);

memoize!(
    pub(crate) fn instance_build_assert_summary<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,
    ) -> Option<SemanticFunctionSummary> {
        let instance = poly_instance.value;
        if !matches!(instance.def, rustc_middle::ty::InstanceKind::Item(_)) {
            return None;
        }

        if let Some(local_def_id) = instance.def_id().as_local() {
            if let Some(summary) = cx.exact_instance_build_assert_summary(poly_instance) {
                return Some(summary);
            }

            return cx
                .local_build_assert_semantic_summaries()
                .get(&local_def_id)
                .cloned();
        }

        cx.sql_load::<instance_build_assert_summary>(poly_instance)
            .flatten()
    }
);

impl PersistentQuery for instance_build_assert_summary {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    fn is_build_error_def(&self, def_id: DefId, build_error: Option<DefId>) -> bool {
        Some(def_id) == build_error || self.tcx.item_name(def_id) == crate::symbol::build_error
    }

    fn join_dependency(a: &ExprDependency, b: &ExprDependency) -> ExprDependency {
        ExprDependency::combine([a.clone(), b.clone()])
    }

    fn merge_mir_local_state_into(
        target: &mut MirLocalState<'tcx>,
        source: &MirLocalState<'tcx>,
    ) -> bool {
        // This is the hottest merge in the MIR analysis, so keep it in-place and field-wise to
        // avoid clone-heavy join logic.
        let dependency = Self::join_dependency(&target.dependency, &source.dependency);
        let dependency_changed = dependency != target.dependency;
        if dependency_changed {
            target.dependency = dependency;
        }

        let fn_targets_changed = target.fn_targets.extend(source.fn_targets.iter().copied());

        let dyn_receiver_tys_changed = target
            .dyn_receiver_tys
            .extend(source.dyn_receiver_tys.iter().copied());

        dependency_changed || fn_targets_changed || dyn_receiver_tys_changed
    }

    fn local_state_for_dependency(dependency: ExprDependency) -> MirLocalState<'tcx> {
        MirLocalState {
            dependency,
            ..Default::default()
        }
    }

    fn mir_fn_targets_from_operand(
        &self,
        typing_env: TypingEnv<'tcx>,
        operand: &mir::Operand<'tcx>,
    ) -> SmallSet<PseudoCanonicalInput<'tcx, Instance<'tcx>>> {
        let mut targets = SmallSet::default();

        let Operand::Constant(constant) = operand else {
            return targets;
        };
        let rustc_middle::ty::TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
            return targets;
        };
        let Some(instance) = Instance::resolve_for_fn_ptr(self.tcx, typing_env, *def_id, args)
        else {
            return targets;
        };
        targets.insert(typing_env.as_query_input(instance));
        targets
    }

    fn mir_dyn_receiver_tys_from_operand(
        &self,
        _body: &mir::Body<'tcx>,
        env: &[MirLocalState<'tcx>],
        operand: &mir::Operand<'tcx>,
    ) -> SmallSet<Ty<'tcx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => env
                .get(place.local.as_usize())
                .map(|state| state.dyn_receiver_tys.clone())
                .unwrap_or_default(),
            Operand::Constant(_) | Operand::RuntimeChecks(_) => SmallSet::default(),
        }
    }

    fn mir_place_state(
        &self,
        _body: &mir::Body<'tcx>,
        env: &[MirLocalState<'tcx>],
        place: mir::Place<'tcx>,
    ) -> MirLocalState<'tcx> {
        env.get(place.local.as_usize())
            .cloned()
            .unwrap_or_else(|| Self::local_state_for_dependency(ExprDependency::Runtime))
    }

    fn mir_operand_dependency(
        &self,
        body: &mir::Body<'tcx>,
        env: &[MirLocalState<'tcx>],
        operand: &mir::Operand<'tcx>,
    ) -> ExprDependency {
        match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.mir_place_state(body, env, *place).dependency
            }
            mir::Operand::Constant(constant) => match constant.const_.ty().kind() {
                rustc_middle::ty::TyKind::FnDef(def_id, _) if self.tcx.is_const_fn(*def_id) => {
                    ExprDependency::Constant
                }
                _ => ExprDependency::Constant,
            },
            mir::Operand::RuntimeChecks(_) => ExprDependency::Runtime,
        }
    }

    fn mir_rvalue_state(
        &self,
        typing_env: TypingEnv<'tcx>,
        body: &mir::Body<'tcx>,
        env: &[MirLocalState<'tcx>],
        rvalue: &mir::Rvalue<'tcx>,
    ) -> MirLocalState<'tcx> {
        match rvalue {
            mir::Rvalue::Use(operand)
            | mir::Rvalue::Repeat(operand, _)
            | mir::Rvalue::WrapUnsafeBinder(operand, _) => {
                let dependency = self.mir_operand_dependency(body, env, operand);
                let mut state = Self::local_state_for_dependency(dependency);
                if let Operand::Copy(place) | Operand::Move(place) = operand {
                    let source = self.mir_place_state(body, env, *place);
                    state.fn_targets = source.fn_targets;
                    state.dyn_receiver_tys = source.dyn_receiver_tys;
                } else {
                    state.fn_targets = self.mir_fn_targets_from_operand(typing_env, operand);
                }
                state
            }
            mir::Rvalue::UnaryOp(_, operand) | mir::Rvalue::Cast(_, operand, _) => {
                let dependency = self.mir_operand_dependency(body, env, operand);
                let mut state = Self::local_state_for_dependency(dependency);

                if let mir::Rvalue::Cast(
                    CastKind::PointerCoercion(pointer_coercion, _),
                    operand,
                    cast_ty,
                ) = rvalue
                {
                    use rustc_middle::ty::adjustment::PointerCoercion;

                    match pointer_coercion {
                        PointerCoercion::ReifyFnPointer(_) | PointerCoercion::UnsafeFnPointer => {
                            state.fn_targets =
                                self.mir_fn_targets_from_operand(typing_env, operand);
                        }
                        PointerCoercion::Unsize
                            if matches!(cast_ty.kind(), rustc_middle::ty::TyKind::Dynamic(..)) =>
                        {
                            match operand {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    let source_ty = place.ty(body, self.tcx).ty;
                                    state.dyn_receiver_tys.insert(source_ty);
                                }
                                Operand::Constant(_) | Operand::RuntimeChecks(_) => {}
                            }
                        }
                        _ => {}
                    }
                }

                state
            }
            mir::Rvalue::BinaryOp(_, box (lhs, rhs)) => {
                Self::local_state_for_dependency(ExprDependency::combine([
                    self.mir_operand_dependency(body, env, lhs),
                    self.mir_operand_dependency(body, env, rhs),
                ]))
            }
            mir::Rvalue::Ref(_, _, place)
            | mir::Rvalue::RawPtr(_, place)
            | mir::Rvalue::Discriminant(place)
            | mir::Rvalue::CopyForDeref(place) => self.mir_place_state(body, env, *place),
            mir::Rvalue::Aggregate(_, operands) => {
                Self::local_state_for_dependency(ExprDependency::combine(
                    operands
                        .iter()
                        .map(|operand| self.mir_operand_dependency(body, env, operand)),
                ))
            }
            mir::Rvalue::ThreadLocalRef(..) => {
                Self::local_state_for_dependency(ExprDependency::Constant)
            }
        }
    }

    fn project_semantic_dependencies(
        &self,
        actual_args: &[ExprDependency],
        params: &SmallSet<usize>,
    ) -> ExprDependency {
        ExprDependency::combine(params.iter().map(|&param_index| {
            actual_args
                .get(param_index)
                .cloned()
                .unwrap_or(ExprDependency::Runtime)
        }))
    }

    fn map_semantic_return_dependency(
        &self,
        summary: &SemanticFunctionSummary,
        actual_args: &[ExprDependency],
    ) -> ExprDependency {
        match &summary.return_dependency {
            ExprDependency::Constant => ExprDependency::Constant,
            ExprDependency::Param(params) => {
                self.project_semantic_dependencies(actual_args, params)
            }
            ExprDependency::Runtime => ExprDependency::Runtime,
        }
    }

    fn conservative_unknown_call_summary(&self) -> SemanticFunctionSummary {
        SemanticFunctionSummary {
            requirement: SemanticRequirementSummary {
                has_unknown_dependency: true,
                ..Default::default()
            },
            return_dependency: ExprDependency::Runtime,
        }
    }

    fn build_assert_summary_for_def_id_with_local_summaries(
        &self,
        def_id: DefId,
        local_summaries: Option<&FxHashMap<LocalDefId, SemanticFunctionSummary>>,
    ) -> Option<SemanticFunctionSummary> {
        if let Some(local_def_id) = def_id.as_local() {
            if let Some(local_summaries) = local_summaries
                && let Some(summary) = local_summaries.get(&local_def_id)
            {
                return Some(summary.clone());
            }
            return self
                .local_build_assert_semantic_summaries()
                .get(&local_def_id)
                .cloned();
        }

        self.instance_build_assert_summary(poly_instance_of_def_id(self, def_id))
    }

    fn build_assert_summary_for_def_id(&self, def_id: DefId) -> Option<SemanticFunctionSummary> {
        self.build_assert_summary_for_def_id_with_local_summaries(def_id, None)
    }

    fn join_build_assert_callee_summaries_with_local_summaries(
        &self,
        callee_targets: impl IntoIterator<Item = PseudoCanonicalInput<'tcx, Instance<'tcx>>>,
        local_summaries: Option<&FxHashMap<LocalDefId, SemanticFunctionSummary>>,
    ) -> Option<SemanticFunctionSummary> {
        let mut joined = SemanticFunctionSummary::default();
        let mut have_summary = false;

        for callee_target in callee_targets {
            let callee_summary = callee_target
                .value
                .def_id()
                .as_local()
                .and_then(|local_def_id| {
                    local_summaries.and_then(|summaries| summaries.get(&local_def_id).cloned())
                })
                .or_else(|| self.instance_build_assert_summary(callee_target))
                .or_else(|| {
                    self.build_assert_summary_for_def_id_with_local_summaries(
                        callee_target.value.def_id(),
                        local_summaries,
                    )
                })?;
            have_summary = true;
            joined.requirement.param_dependencies.extend(
                callee_summary
                    .requirement
                    .param_dependencies
                    .iter()
                    .copied(),
            );
            joined.requirement.has_local_runtime_dependency |=
                callee_summary.requirement.has_local_runtime_dependency;
            joined.requirement.has_unknown_dependency |=
                callee_summary.requirement.has_unknown_dependency;
            joined.return_dependency =
                Self::join_dependency(&joined.return_dependency, &callee_summary.return_dependency);
        }

        have_summary.then_some(joined)
    }

    fn propagated_origin_from_summary(
        &self,
        callee: DefId,
        call_span: Span,
        callee_summary: &SemanticFunctionSummary,
        actual_args: &[ExprDependency],
    ) -> Option<RequirementOrigin> {
        let propagated = self.project_semantic_dependencies(
            actual_args,
            &callee_summary.requirement.param_dependencies,
        );
        ((matches!(
            propagated,
            ExprDependency::Param(_) | ExprDependency::Runtime
        ) || callee_summary.requirement.has_local_runtime_dependency)
            && !callee_summary.requirement.has_unknown_dependency
            && !matches!(propagated, ExprDependency::Constant))
        .then_some(RequirementOrigin::Propagated { callee, call_span })
        .or_else(|| {
            callee_summary
                .requirement
                .has_local_runtime_dependency
                .then_some(RequirementOrigin::Propagated { callee, call_span })
        })
        .and_then(|origin| (!callee_summary.requirement.has_unknown_dependency).then_some(origin))
    }

    fn propagated_origin_from_callee_targets(
        &self,
        callee_targets: impl IntoIterator<Item = PseudoCanonicalInput<'tcx, Instance<'tcx>>>,
        call_span: Span,
        actual_args: &[ExprDependency],
    ) -> Option<RequirementOrigin> {
        for callee_target in callee_targets {
            let callee_summary = self
                .instance_build_assert_summary(callee_target)
                .or_else(|| self.build_assert_summary_for_def_id(callee_target.value.def_id()))?;
            if let Some(origin) = self.propagated_origin_from_summary(
                callee_target.value.def_id(),
                call_span,
                &callee_summary,
                actual_args,
            ) {
                return Some(origin);
            }
        }

        None
    }

    fn resolve_virtual_call_targets(
        &self,
        typing_env: TypingEnv<'tcx>,
        trait_method: DefId,
        generic_args: &'tcx GenericArgs<'tcx>,
        receiver: &mir::Operand<'tcx>,
        body: &mir::Body<'tcx>,
        env: &[MirLocalState<'tcx>],
        span: Span,
    ) -> FxHashSet<PseudoCanonicalInput<'tcx, Instance<'tcx>>> {
        let mut targets = FxHashSet::default();

        for receiver_ty in self.mir_dyn_receiver_tys_from_operand(body, env, receiver) {
            let concrete_self_ty = match receiver_ty.kind() {
                rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                _ => receiver_ty,
            };
            let args = GenericArgs::for_item(self.tcx, trait_method, |param, _| {
                if param.index == 0 {
                    concrete_self_ty.into()
                } else {
                    generic_args[param.index as usize]
                }
            });
            let instance =
                Instance::expect_resolve_for_vtable(self.tcx, typing_env, trait_method, args, span);
            targets.insert(typing_env.as_query_input(instance));
        }

        targets
    }

    pub(crate) fn exact_local_build_assert_propagated_origin(
        &self,
        poly_instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,
    ) -> Option<RequirementOrigin> {
        let PseudoCanonicalInput {
            typing_env,
            value: instance,
        } = poly_instance;
        let local_def_id = instance.def_id().as_local()?;

        if !matches!(instance.def, rustc_middle::ty::InstanceKind::Item(_))
            || self.tcx.hir_maybe_body_owned_by(local_def_id).is_none()
        {
            return None;
        }

        if self
            .call_stack
            .borrow()
            .iter()
            .any(|site| site.instance == poly_instance)
        {
            return None;
        }

        let body = self.analysis_instance_mir(instance.def);
        let build_error = self.get_klint_diagnostic_item(crate::symbol::build_error);
        let mut block_entries =
            vec![vec![MirLocalState::default(); body.local_decls.len()]; body.basic_blocks.len()];

        for arg_index in 0..body.arg_count {
            block_entries[mir::START_BLOCK.as_usize()][arg_index + 1] =
                Self::local_state_for_dependency(ExprDependency::param(arg_index));
        }

        self.call_stack.borrow_mut().push(UseSite {
            instance: poly_instance,
            kind: UseSiteKind::Other(
                self.def_span(instance.def_id()),
                "used while inferring build_assert propagated origin".into(),
            ),
        });

        let mut origin = None;
        let mut worklist = VecDeque::from([mir::START_BLOCK]);
        let mut queued = vec![false; body.basic_blocks.len()];
        queued[mir::START_BLOCK.as_usize()] = true;

        while let Some(bb) = worklist.pop_front() {
            queued[bb.as_usize()] = false;
            let data = &body.basic_blocks[bb];
            let mut env = block_entries[bb.as_usize()].clone();

            for statement in &data.statements {
                let mir::StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                env[place.local.as_usize()] = self.mir_rvalue_state(typing_env, body, &env, rvalue);
            }

            let terminator = data.terminator();
            let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                for succ in terminator.successors() {
                    let succ_entry = &mut block_entries[succ.as_usize()];
                    let mut succ_changed = false;
                    for (entry, current) in succ_entry.iter_mut().zip(env.iter()) {
                        succ_changed |= Self::merge_mir_local_state_into(entry, current);
                    }
                    if succ_changed && !queued[succ.as_usize()] {
                        queued[succ.as_usize()] = true;
                        worklist.push_back(succ);
                    }
                }
                continue;
            };

            let callee_ty = func.ty(body, self.tcx);
            let callee_ty = instance.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                typing_env,
                rustc_middle::ty::EarlyBinder::bind(callee_ty),
            );
            let actual_args: Vec<_> = args
                .iter()
                .map(|arg| self.mir_operand_dependency(body, &env, &arg.node))
                .collect();

            if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) = callee_ty.kind() {
                if self.is_build_error_def(*def_id, build_error) {
                    for succ in terminator.successors() {
                        let succ_entry = &mut block_entries[succ.as_usize()];
                        let mut succ_changed = false;
                        for (entry, current) in succ_entry.iter_mut().zip(env.iter()) {
                            succ_changed |= Self::merge_mir_local_state_into(entry, current);
                        }
                        if succ_changed && !queued[succ.as_usize()] {
                            queued[succ.as_usize()] = true;
                            worklist.push_back(succ);
                        }
                    }
                    continue;
                }

                let mut target_instances = FxHashSet::default();
                let fallback_def_id =
                    match Instance::try_resolve(self.tcx, typing_env, *def_id, generic_args)
                        .unwrap()
                    {
                        Some(callee_instance)
                            if !matches!(
                                callee_instance.def,
                                rustc_middle::ty::InstanceKind::Virtual(..)
                            ) =>
                        {
                            target_instances.insert(typing_env.as_query_input(callee_instance));
                            Some(callee_instance.def_id())
                        }
                        Some(Instance {
                            def: rustc_middle::ty::InstanceKind::Virtual(trait_method, _),
                            ..
                        }) if !args.is_empty() => {
                            target_instances = self.resolve_virtual_call_targets(
                                typing_env,
                                trait_method,
                                generic_args,
                                &args[0].node,
                                body,
                                &env,
                                terminator.source_info.span,
                            );
                            Some(trait_method)
                        }
                        Some(callee_instance) => Some(callee_instance.def_id()),
                        None => Some(*def_id),
                    };

                if origin.is_none() {
                    if let Some(def_id) = fallback_def_id
                        && let Some(summary) = self.build_assert_summary_for_def_id(def_id)
                    {
                        origin = self.propagated_origin_from_summary(
                            def_id,
                            terminator.source_info.span,
                            &summary,
                            &actual_args,
                        );
                    }

                    if origin.is_none() {
                        origin = self.propagated_origin_from_callee_targets(
                            target_instances.iter().copied(),
                            terminator.source_info.span,
                            &actual_args,
                        );
                    }
                }
            } else {
                let mut target_instances = FxHashSet::default();

                match func {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        target_instances = env[place.local.as_usize()]
                            .fn_targets
                            .iter()
                            .copied()
                            .collect();
                    }
                    Operand::Constant(constant) => {
                        if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) =
                            constant.const_.ty().kind()
                            && let Some(instance) = Instance::resolve_for_fn_ptr(
                                self.tcx,
                                typing_env,
                                *def_id,
                                generic_args,
                            )
                        {
                            target_instances.insert(typing_env.as_query_input(instance));
                        }
                    }
                    Operand::RuntimeChecks(_) => {}
                    _ => {}
                }

                if origin.is_none() {
                    origin = self.propagated_origin_from_callee_targets(
                        target_instances.iter().copied(),
                        terminator.source_info.span,
                        &actual_args,
                    );
                }
            }

            for succ in terminator.successors() {
                let succ_entry = &mut block_entries[succ.as_usize()];
                let mut succ_changed = false;
                for (entry, current) in succ_entry.iter_mut().zip(env.iter()) {
                    succ_changed |= Self::merge_mir_local_state_into(entry, current);
                }
                if succ_changed && !queued[succ.as_usize()] {
                    queued[succ.as_usize()] = true;
                    worklist.push_back(succ);
                }
            }
        }

        self.call_stack.borrow_mut().pop();
        origin
    }

    fn exact_instance_build_assert_summary_with_local_summaries(
        &self,
        poly_instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,
        local_summaries: Option<&FxHashMap<LocalDefId, SemanticFunctionSummary>>,
    ) -> Option<SemanticFunctionSummary> {
        let PseudoCanonicalInput {
            typing_env,
            value: instance,
        } = poly_instance;
        let local_def_id = instance.def_id().as_local()?;

        if !matches!(instance.def, rustc_middle::ty::InstanceKind::Item(_))
            || self.tcx.hir_maybe_body_owned_by(local_def_id).is_none()
        {
            return None;
        }

        if self
            .call_stack
            .borrow()
            .iter()
            .any(|site| site.instance == poly_instance)
        {
            return local_summaries
                .and_then(|summaries| summaries.get(&local_def_id).cloned())
                .or_else(|| {
                    self.local_build_assert_semantic_summaries()
                        .get(&local_def_id)
                        .cloned()
                });
        }

        let body = self.analysis_instance_mir(instance.def);
        let build_error = self.get_klint_diagnostic_item(crate::symbol::build_error);
        let mut block_entries =
            vec![vec![MirLocalState::default(); body.local_decls.len()]; body.basic_blocks.len()];
        let mut block_exit_dependencies =
            vec![vec![ExprDependency::Constant; body.local_decls.len()]; body.basic_blocks.len()];

        for arg_index in 0..body.arg_count {
            block_entries[mir::START_BLOCK.as_usize()][arg_index + 1] =
                Self::local_state_for_dependency(ExprDependency::param(arg_index));
        }

        let mut summary = SemanticFunctionSummary::default();
        let mut worklist = VecDeque::from([mir::START_BLOCK]);
        let mut queued = vec![false; body.basic_blocks.len()];
        queued[mir::START_BLOCK.as_usize()] = true;

        self.call_stack.borrow_mut().push(UseSite {
            instance: poly_instance,
            kind: UseSiteKind::Other(
                self.def_span(instance.def_id()),
                "used while inferring build_assert summary".into(),
            ),
        });

        while let Some(bb) = worklist.pop_front() {
            queued[bb.as_usize()] = false;
            let data = &body.basic_blocks[bb];
            let mut env = block_entries[bb.as_usize()].clone();

            for statement in &data.statements {
                let mir::StatementKind::Assign(box (place, rvalue)) = &statement.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                env[place.local.as_usize()] = self.mir_rvalue_state(typing_env, body, &env, rvalue);
            }

            for (local, state) in env.iter().enumerate() {
                block_exit_dependencies[bb.as_usize()][local] = state.dependency.clone();
            }

            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    let callee_ty = func.ty(body, self.tcx);
                    let callee_ty = instance.instantiate_mir_and_normalize_erasing_regions(
                        self.tcx,
                        typing_env,
                        rustc_middle::ty::EarlyBinder::bind(callee_ty),
                    );
                    let actual_args: Vec<_> = args
                        .iter()
                        .map(|arg| self.mir_operand_dependency(body, &env, &arg.node))
                        .collect();

                    if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) = callee_ty.kind()
                    {
                        if self.is_build_error_def(*def_id, build_error) {
                            let mut dep = ExprDependency::Constant;
                            for &pred in body.basic_blocks.predecessors()[bb].iter() {
                                if let TerminatorKind::SwitchInt { discr, .. } =
                                    &body.basic_blocks[pred].terminator().kind
                                {
                                    dep = Self::join_dependency(
                                        &dep,
                                        &match discr {
                                            Operand::Copy(place) | Operand::Move(place) => {
                                                block_exit_dependencies[pred.as_usize()]
                                                    .get(place.local.as_usize())
                                                    .cloned()
                                                    .unwrap_or(ExprDependency::Runtime)
                                            }
                                            Operand::Constant(_) => ExprDependency::Constant,
                                            Operand::RuntimeChecks(_) => ExprDependency::Runtime,
                                        },
                                    );
                                }
                            }

                            match dep {
                                ExprDependency::Constant => {}
                                ExprDependency::Param(params) => {
                                    summary.requirement.param_dependencies.extend(params);
                                }
                                ExprDependency::Runtime => {
                                    summary.requirement.has_local_runtime_dependency = true;
                                }
                            }
                        } else {
                            let mut callee_targets = FxHashSet::default();
                            let mut direct_summary = None;

                            match Instance::try_resolve(self.tcx, typing_env, *def_id, generic_args)
                                .unwrap()
                            {
                                Some(callee_instance)
                                    if !matches!(
                                        callee_instance.def,
                                        rustc_middle::ty::InstanceKind::Virtual(..)
                                    ) =>
                                {
                                    callee_targets
                                        .insert(typing_env.as_query_input(callee_instance));
                                }
                                Some(Instance {
                                    def: rustc_middle::ty::InstanceKind::Virtual(trait_method, _),
                                    ..
                                }) if !args.is_empty() => {
                                    callee_targets = self.resolve_virtual_call_targets(
                                        typing_env,
                                        trait_method,
                                        generic_args,
                                        &args[0].node,
                                        body,
                                        &env,
                                        terminator.source_info.span,
                                    );
                                    if callee_targets.is_empty() {
                                        direct_summary = self
                                            .build_assert_summary_for_def_id_with_local_summaries(
                                                trait_method,
                                                local_summaries,
                                            );
                                    }
                                }
                                Some(callee_instance) => {
                                    direct_summary = self
                                        .build_assert_summary_for_def_id_with_local_summaries(
                                            callee_instance.def_id(),
                                            local_summaries,
                                        );
                                }
                                None => {
                                    direct_summary = self
                                        .build_assert_summary_for_def_id_with_local_summaries(
                                            *def_id,
                                            local_summaries,
                                        );
                                }
                            }

                            let call_summary = direct_summary.or_else(|| {
                                let joined = self
                                    .join_build_assert_callee_summaries_with_local_summaries(
                                        callee_targets,
                                        local_summaries,
                                    )?;
                                let return_dependency =
                                    self.map_semantic_return_dependency(&joined, &actual_args);
                                Some(SemanticFunctionSummary {
                                    requirement: joined.requirement,
                                    return_dependency,
                                })
                            });

                            if let Some(call_summary) = call_summary {
                                let propagated = self.project_semantic_dependencies(
                                    &actual_args,
                                    &call_summary.requirement.param_dependencies,
                                );
                                match propagated {
                                    ExprDependency::Constant => {}
                                    ExprDependency::Param(params) => {
                                        summary.requirement.param_dependencies.extend(params);
                                    }
                                    ExprDependency::Runtime => {
                                        summary.requirement.has_local_runtime_dependency = true;
                                    }
                                }

                                if call_summary.requirement.has_local_runtime_dependency {
                                    summary.requirement.has_local_runtime_dependency = true;
                                }
                                if call_summary.requirement.has_unknown_dependency {
                                    summary.requirement.has_unknown_dependency = true;
                                }

                                if let Some(target) = target
                                    && destination.projection.is_empty()
                                {
                                    let entry = &mut block_entries[target.as_usize()]
                                        [destination.local.as_usize()];
                                    if Self::merge_mir_local_state_into(
                                        entry,
                                        &Self::local_state_for_dependency(
                                            call_summary.return_dependency,
                                        ),
                                    ) && !queued[target.as_usize()]
                                    {
                                        queued[target.as_usize()] = true;
                                        worklist.push_back(*target);
                                    }
                                }
                            }
                        }
                    } else {
                        let mut callee_targets = FxHashSet::default();
                        let mut call_summary = None;

                        match &func {
                            Operand::Copy(place) | Operand::Move(place)
                                if place.projection.is_empty() =>
                            {
                                callee_targets = env[place.local.as_usize()]
                                    .fn_targets
                                    .iter()
                                    .copied()
                                    .collect();
                            }
                            Operand::Constant(constant) => {
                                if let rustc_middle::ty::TyKind::FnDef(def_id, generic_args) =
                                    constant.const_.ty().kind()
                                {
                                    if let Some(instance) = Instance::resolve_for_fn_ptr(
                                        self.tcx,
                                        typing_env,
                                        *def_id,
                                        generic_args,
                                    ) {
                                        callee_targets.insert(typing_env.as_query_input(instance));
                                    } else {
                                        call_summary = Some(
                                            self.build_assert_summary_for_def_id_with_local_summaries(
                                                *def_id,
                                                local_summaries,
                                            )
                                            .unwrap_or_else(|| self.conservative_unknown_call_summary()),
                                        );
                                    }
                                } else {
                                    call_summary = Some(self.conservative_unknown_call_summary());
                                }
                            }
                            Operand::RuntimeChecks(_) => {
                                call_summary = Some(self.conservative_unknown_call_summary());
                            }
                            _ => {}
                        }

                        if callee_targets.is_empty() {
                            let call_summary = call_summary
                                .unwrap_or_else(|| self.conservative_unknown_call_summary());
                            let propagated = self.project_semantic_dependencies(
                                &actual_args,
                                &call_summary.requirement.param_dependencies,
                            );
                            match propagated {
                                ExprDependency::Constant => {}
                                ExprDependency::Param(params) => {
                                    summary.requirement.param_dependencies.extend(params);
                                }
                                ExprDependency::Runtime => {
                                    summary.requirement.has_local_runtime_dependency = true;
                                }
                            }
                            if call_summary.requirement.has_local_runtime_dependency {
                                summary.requirement.has_local_runtime_dependency = true;
                            }
                            if call_summary.requirement.has_unknown_dependency {
                                summary.requirement.has_unknown_dependency = true;
                            }

                            if let Some(target) = target
                                && destination.projection.is_empty()
                            {
                                let entry = &mut block_entries[target.as_usize()]
                                    [destination.local.as_usize()];
                                if Self::merge_mir_local_state_into(
                                    entry,
                                    &Self::local_state_for_dependency(
                                        self.map_semantic_return_dependency(
                                            &call_summary,
                                            &actual_args,
                                        ),
                                    ),
                                ) && !queued[target.as_usize()]
                                {
                                    queued[target.as_usize()] = true;
                                    worklist.push_back(*target);
                                }
                            }
                            continue;
                        }

                        let joined_summary = self
                            .join_build_assert_callee_summaries_with_local_summaries(
                                callee_targets,
                                local_summaries,
                            )
                            .unwrap_or_else(|| self.conservative_unknown_call_summary());

                        let propagated = self.project_semantic_dependencies(
                            &actual_args,
                            &joined_summary.requirement.param_dependencies,
                        );
                        match propagated {
                            ExprDependency::Constant => {}
                            ExprDependency::Param(params) => {
                                summary.requirement.param_dependencies.extend(params);
                            }
                            ExprDependency::Runtime => {
                                summary.requirement.has_local_runtime_dependency = true;
                            }
                        }
                        if joined_summary.requirement.has_local_runtime_dependency {
                            summary.requirement.has_local_runtime_dependency = true;
                        }
                        if joined_summary.requirement.has_unknown_dependency {
                            summary.requirement.has_unknown_dependency = true;
                        }

                        if let Some(target) = target
                            && destination.projection.is_empty()
                        {
                            let entry =
                                &mut block_entries[target.as_usize()][destination.local.as_usize()];
                            if Self::merge_mir_local_state_into(
                                entry,
                                &Self::local_state_for_dependency(
                                    self.map_semantic_return_dependency(
                                        &joined_summary,
                                        &actual_args,
                                    ),
                                ),
                            ) && !queued[target.as_usize()]
                            {
                                queued[target.as_usize()] = true;
                                worklist.push_back(*target);
                            }
                        }
                    }
                }
                TerminatorKind::Return => {
                    summary.return_dependency =
                        Self::join_dependency(&summary.return_dependency, &env[0].dependency);
                }
                _ => {}
            }

            for succ in terminator.successors() {
                let succ_entry = &mut block_entries[succ.as_usize()];
                let mut succ_changed = false;
                for (entry, current) in succ_entry.iter_mut().zip(env.iter()) {
                    succ_changed |= Self::merge_mir_local_state_into(entry, current);
                }
                if succ_changed && !queued[succ.as_usize()] {
                    queued[succ.as_usize()] = true;
                    worklist.push_back(succ);
                }
            }
        }

        self.call_stack.borrow_mut().pop();
        Some(summary)
    }

    pub(crate) fn exact_instance_build_assert_summary(
        &self,
        poly_instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,
    ) -> Option<SemanticFunctionSummary> {
        self.exact_instance_build_assert_summary_with_local_summaries(poly_instance, None)
    }

    pub(crate) fn encode_build_assert_summaries(&self) {
        let exported = exported_build_assert_body_owners(self);
        tracing::debug!(
            exported_body_owner_count = exported.len(),
            "encoding build_assert summaries"
        );
        for def_id in exported {
            if let Some(summary) = self
                .instance_build_assert_summary(poly_instance_of_def_id(self, def_id.to_def_id()))
            {
                self.sql_store::<instance_build_assert_summary>(
                    poly_instance_of_def_id(self, def_id.to_def_id()),
                    Some(summary),
                );
            }
        }
    }
}

fn build_assert_call_site(
    tcx: TyCtxt<'_>,
    span: Span,
    build_assert: Option<DefId>,
) -> Option<Span> {
    // Match by diagnostic item first, then by macro name as a compatibility fallback for older
    // trees where the explicit annotation may not exist yet.
    span.macro_backtrace()
        .find(|expn_data| {
            let Some(macro_def_id) = expn_data.macro_def_id else {
                return false;
            };

            Some(macro_def_id) == build_assert
                || tcx.item_name(macro_def_id) == crate::symbol::build_assert
        })
        .map(|expn_data| expn_data.call_site.source_callsite())
}

pub fn build_assert_condition(
    tcx: TyCtxt<'_>,
    expr: &Expr<'_>,
    build_assert: Option<DefId>,
) -> Option<BuildAssertCondition> {
    // Recover the asserted condition from the expanded HIR shape of `build_assert!` itself:
    // the macro body contributes the outer `!`, while the operand span still points at the
    // user's original condition expression.
    let rustc_hir::ExprKind::Unary(UnOp::Not, condition) = expr.kind else {
        return None;
    };
    if !expr.span.from_expansion() {
        return None;
    }

    let call_site = build_assert_call_site(tcx, expr.span, build_assert)?;
    let condition_span = condition.span.source_callsite();
    Some(BuildAssertCondition {
        call_site,
        condition_span,
    })
}

fn is_reportable_fn(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn)
}

struct DirectBuildAssertVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    build_assert: Option<DefId>,
    build_assert_conditions: FxHashMap<Span, Span>,
    seen_build_assert_callsites: FxHashSet<Span>,
    summary: LocalDirectDiagnosticSummary,
}

struct LocalInterestVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    build_assert: Option<DefId>,
    build_assert_conditions: FxHashMap<Span, Span>,
    seen_build_assert_callsites: FxHashSet<Span>,
    summary: LocalInterestSummary,
}

impl<'a, 'tcx> DirectBuildAssertVisitor<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typeck: &'a TypeckResults<'tcx>,
        build_assert: Option<DefId>,
    ) -> Self {
        Self {
            tcx,
            typeck,
            build_assert,
            build_assert_conditions: FxHashMap::default(),
            seen_build_assert_callsites: FxHashSet::default(),
            summary: LocalDirectDiagnosticSummary::default(),
        }
    }

    fn path_dependency(&self, qpath: &QPath<'tcx>, hir_id: HirId) -> ExprDependency {
        match self.typeck.qpath_res(qpath, hir_id) {
            Res::Def(
                DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::ConstParam,
                _,
            ) => ExprDependency::Constant,
            Res::Def(
                DefKind::Static {
                    mutability: Mutability::Not,
                    ..
                },
                _,
            ) => ExprDependency::Constant,
            Res::Local(..) => ExprDependency::Runtime,
            _ => ExprDependency::Runtime,
        }
    }

    fn combine_exprs<I>(&self, exprs: I) -> ExprDependency
    where
        I: IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        ExprDependency::combine(exprs.into_iter().map(|expr| self.expr_dependency(expr)))
    }

    fn expr_dependency(&self, expr: &'tcx Expr<'tcx>) -> ExprDependency {
        match expr.kind {
            rustc_hir::ExprKind::ConstBlock(..) | rustc_hir::ExprKind::Lit(..) => {
                ExprDependency::Constant
            }
            rustc_hir::ExprKind::Path(ref qpath) => self.path_dependency(qpath, expr.hir_id),
            rustc_hir::ExprKind::Use(inner, _)
            | rustc_hir::ExprKind::Unary(_, inner)
            | rustc_hir::ExprKind::Cast(inner, _)
            | rustc_hir::ExprKind::Type(inner, _)
            | rustc_hir::ExprKind::DropTemps(inner)
            | rustc_hir::ExprKind::Field(inner, _)
            | rustc_hir::ExprKind::AddrOf(_, _, inner)
            | rustc_hir::ExprKind::UnsafeBinderCast(_, inner, _) => self.expr_dependency(inner),
            rustc_hir::ExprKind::Binary(_, lhs, rhs)
            | rustc_hir::ExprKind::AssignOp(_, lhs, rhs)
            | rustc_hir::ExprKind::Index(lhs, rhs, _) => {
                ExprDependency::combine([self.expr_dependency(lhs), self.expr_dependency(rhs)])
            }
            rustc_hir::ExprKind::Assign(_, rhs, _) | rustc_hir::ExprKind::Repeat(rhs, _) => {
                self.expr_dependency(rhs)
            }
            rustc_hir::ExprKind::Array(exprs) | rustc_hir::ExprKind::Tup(exprs) => {
                self.combine_exprs(exprs.iter())
            }
            rustc_hir::ExprKind::Block(block, _) => block
                .expr
                .map(|expr| self.expr_dependency(expr))
                .unwrap_or(ExprDependency::Constant),
            rustc_hir::ExprKind::Struct(_, fields, tail) => {
                let mut exprs = Vec::with_capacity(fields.len() + 1);
                for field in fields {
                    exprs.push(field.expr);
                }
                if let rustc_hir::StructTailExpr::Base(expr) = tail {
                    exprs.push(expr);
                }
                self.combine_exprs(exprs)
            }
            rustc_hir::ExprKind::If(condition, then_expr, else_expr) => {
                let mut exprs = vec![condition, then_expr];
                if let Some(expr) = else_expr {
                    exprs.push(expr);
                }
                self.combine_exprs(exprs)
            }
            rustc_hir::ExprKind::Match(scrutinee, arms, _) => {
                let mut dependencies = Vec::with_capacity(1 + arms.len() * 2);
                dependencies.push(self.expr_dependency(scrutinee));

                for arm in arms {
                    if let Some(guard) = arm.guard {
                        dependencies.push(self.expr_dependency(guard));
                    }
                    dependencies.push(self.expr_dependency(arm.body));
                }

                ExprDependency::combine(dependencies)
            }
            rustc_hir::ExprKind::Call(callee, args) => self.call_expr_dependency(callee, args),
            rustc_hir::ExprKind::MethodCall(_, receiver, args, _) => {
                self.method_call_expr_dependency(expr, receiver, args)
            }
            _ => ExprDependency::Runtime,
        }
    }

    fn call_expr_dependency(
        &self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> ExprDependency {
        let rustc_hir::ExprKind::Path(ref qpath) = callee.kind else {
            return ExprDependency::Runtime;
        };
        let resolved = self.typeck.qpath_res(qpath, callee.hir_id);
        let args_dependency = self.combine_exprs(args.iter());

        if matches!(args_dependency, ExprDependency::Constant)
            && matches!(resolved, Res::Def(DefKind::Ctor(..), _))
        {
            return ExprDependency::Constant;
        }

        if let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = resolved
            && self.tcx.is_const_fn(def_id)
            && matches!(args_dependency, ExprDependency::Constant)
        {
            return ExprDependency::Constant;
        }

        ExprDependency::Runtime
    }

    fn method_call_expr_dependency(
        &self,
        expr: &'tcx Expr<'tcx>,
        receiver: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> ExprDependency {
        let dependency = self.combine_exprs(std::iter::once(receiver).chain(args.iter()));
        let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) else {
            return ExprDependency::Runtime;
        };

        if self.tcx.is_const_fn(def_id) && matches!(dependency, ExprDependency::Constant) {
            return ExprDependency::Constant;
        }

        ExprDependency::Runtime
    }

    fn finish(self) -> LocalDirectDiagnosticSummary {
        self.summary
    }
}

impl<'a, 'tcx> LocalInterestVisitor<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        typeck: &'a TypeckResults<'tcx>,
        build_assert: Option<DefId>,
    ) -> Self {
        Self {
            tcx,
            typeck,
            build_assert,
            build_assert_conditions: FxHashMap::default(),
            seen_build_assert_callsites: FxHashSet::default(),
            summary: LocalInterestSummary::default(),
        }
    }

    fn resolve_direct_call(&self, callee: &'tcx Expr<'tcx>) -> Option<LocalDefId> {
        let rustc_hir::ExprKind::Path(ref qpath) = callee.kind else {
            return None;
        };
        match self.typeck.qpath_res(qpath, callee.hir_id) {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => def_id.as_local(),
            _ => None,
        }
    }

    fn resolve_method_call(&self, expr: &'tcx Expr<'tcx>) -> Option<LocalDefId> {
        self.typeck.type_dependent_def_id(expr.hir_id)?.as_local()
    }

    fn finish(self) -> LocalInterestSummary {
        self.summary
    }
}

impl<'tcx> hir_visit::Visitor<'tcx> for DirectBuildAssertVisitor<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let Some(condition) = build_assert_condition(self.tcx, expr, self.build_assert) {
            self.build_assert_conditions
                .entry(condition.condition_span)
                .or_insert(condition.call_site);
        }

        let source_span = expr.span.source_callsite();
        if let Some(&call_site) = self.build_assert_conditions.get(&source_span)
            && self.seen_build_assert_callsites.insert(call_site)
        {
            let dependency = self.expr_dependency(expr);
            if !matches!(dependency, ExprDependency::Constant) {
                self.summary.direct_requirement_origin =
                    Some(RequirementOrigin::Direct { span: call_site });
            }
        }

        hir_visit::walk_expr(self, expr);
    }
}

impl<'tcx> hir_visit::Visitor<'tcx> for LocalInterestVisitor<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let Some(condition) = build_assert_condition(self.tcx, expr, self.build_assert) {
            self.build_assert_conditions
                .entry(condition.condition_span)
                .or_insert(condition.call_site);
        }

        let source_span = expr.span.source_callsite();
        if let Some(&call_site) = self.build_assert_conditions.get(&source_span)
            && self.seen_build_assert_callsites.insert(call_site)
        {
            self.summary.has_direct_build_assert = true;
        }

        match expr.kind {
            rustc_hir::ExprKind::Call(callee, _) => {
                if let Some(local_def_id) = self.resolve_direct_call(callee) {
                    self.summary.direct_callees.insert(local_def_id);
                } else if let rustc_hir::ExprKind::Path(ref qpath) = callee.kind
                    && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) =
                        self.typeck.qpath_res(qpath, callee.hir_id)
                {
                    self.summary.external_callees.insert(def_id);
                }
            }
            rustc_hir::ExprKind::MethodCall(_, _, _, _) => {
                if let Some(local_def_id) = self.resolve_method_call(expr) {
                    self.summary.direct_callees.insert(local_def_id);
                } else if let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id) {
                    self.summary.external_callees.insert(def_id);
                }
            }
            _ => {}
        }

        hir_visit::walk_expr(self, expr);
    }
}

pub struct BuildAssertLints<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
}

impl_lint_pass!(BuildAssertLints<'_> => [BUILD_ASSERT_NOT_INLINED]);

impl<'tcx> LateLintPass<'tcx> for BuildAssertLints<'tcx> {
    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let direct_diagnostics = self.cx.local_direct_build_assert_diagnostics();
        let body_owners = self.cx.local_build_assert_candidate_functions();
        tracing::debug!(
            body_owner_count = body_owners.len(),
            "emitting build_assert lints"
        );

        for def_id in body_owners {
            if self
                .cx
                .instance_build_assert_summary(poly_instance_of_def_id(self.cx, def_id.to_def_id()))
                .is_some_and(|summary| summary.requirement.requires_inline())
                && !has_inline_always(cx.tcx, def_id.to_def_id())
            {
                emit_build_assert_not_inlined(
                    cx,
                    def_id,
                    direct_diagnostics
                        .get(&def_id)
                        .and_then(|direct_summary| direct_summary.direct_requirement_origin)
                        .or_else(|| {
                            self.cx
                                .local_build_assert_propagated_origin_diagnostic(def_id)
                        }),
                );
            }
        }
    }
}
