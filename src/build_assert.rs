// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_ast::Mutability;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit as hir_visit;
use rustc_hir::{Body, Expr, HirId, QPath, Stmt, StmtKind, UnOp};
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_session::impl_lint_pass;
use rustc_span::Span;

use crate::build_assert_not_inlined::{
    BUILD_ASSERT_NOT_INLINED, emit_build_assert_not_inlined, has_inline_always,
};
use crate::ctxt::AnalysisCtxt;
use crate::mono_graph::{CallableTargets, IndirectCandidates, collect_indirect_candidates};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct BuildAssertCondition {
    /// Span of the original `build_assert!(...)` invocation in source.
    pub call_site: Span,
    /// Span of the first macro argument, i.e. the asserted condition.
    pub condition_span: Span,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub enum ExprDependency {
    #[default]
    Constant,
    Param(FxHashSet<usize>),
    Runtime,
}

impl ExprDependency {
    /// Record that an expression depends on one specific function parameter.
    pub fn param(index: usize) -> Self {
        let mut params = FxHashSet::default();
        params.insert(index);
        Self::Param(params)
    }

    /// Merge dependencies from subexpressions. Any runtime component dominates; otherwise we keep
    /// the union of parameter indices that still matter to the value.
    pub fn combine<I>(dependencies: I) -> Self
    where
        I: IntoIterator<Item = ExprDependency>,
    {
        let mut params = FxHashSet::default();

        for dependency in dependencies {
            match dependency {
                ExprDependency::Constant => {}
                ExprDependency::Param(dep_params) => params.extend(dep_params),
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
    Propagated { callee: LocalDefId, call_span: Span },
}

type FunctionSummaries = FxHashMap<LocalDefId, FunctionSummary>;

#[derive(Clone, Default, PartialEq, Eq)]
pub(crate) struct RequirementSummary {
    pub(crate) param_dependencies: FxHashSet<usize>,
    has_local_runtime_dependency: bool,
    pub(crate) origin: Option<RequirementOrigin>,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub(crate) struct FunctionSummary {
    pub(crate) requirement: RequirementSummary,
    return_dependency: ExprDependency,
}

impl RequirementSummary {
    /// The inline requirement matters only when some non-constant value still flows into
    /// `build_assert!`, either directly or through a caller.
    pub(crate) fn requires_inline(&self) -> bool {
        self.has_local_runtime_dependency || !self.param_dependencies.is_empty()
    }

    /// Record a direct `build_assert!` use in this body. Constant assertions stay quiet; anything
    /// else seeds the later caller propagation.
    fn record_direct_use(&mut self, dependency: ExprDependency, span: Span) {
        match dependency {
            ExprDependency::Constant => {}
            ExprDependency::Param(params) => {
                self.param_dependencies.extend(params);
                self.origin
                    .get_or_insert(RequirementOrigin::Direct { span });
            }
            ExprDependency::Runtime => {
                self.has_local_runtime_dependency = true;
                self.origin
                    .get_or_insert(RequirementOrigin::Direct { span });
            }
        }
    }

    /// Record that this function inherits the inline requirement from a callee after mapping the
    /// callee's relevant parameters onto the actual callsite arguments.
    fn record_propagated_use(&mut self, dependency: ExprDependency, origin: RequirementOrigin) {
        match dependency {
            ExprDependency::Constant => {}
            ExprDependency::Param(params) => {
                if !params.is_empty() {
                    self.param_dependencies.extend(params);
                    self.origin.get_or_insert(origin);
                }
            }
            ExprDependency::Runtime => {
                self.has_local_runtime_dependency = true;
                self.origin.get_or_insert(origin);
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

#[derive(Default)]
struct ScopeFrame {
    bindings: Vec<(HirId, Option<LocalBinding>)>,
}

#[derive(Clone, Default)]
struct LocalBinding {
    dependency: ExprDependency,
    callables: CallableTargets,
}

struct LocalEnv {
    bindings: FxHashMap<HirId, LocalBinding>,
    scopes: Vec<ScopeFrame>,
}

impl LocalEnv {
    fn new() -> Self {
        Self {
            bindings: FxHashMap::default(),
            scopes: vec![ScopeFrame::default()],
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(ScopeFrame::default());
    }

    fn exit_scope(&mut self) {
        let frame = self.scopes.pop().expect("scope underflow");

        for (hir_id, old) in frame.bindings.into_iter().rev() {
            if let Some(old) = old {
                self.bindings.insert(hir_id, old);
            } else {
                self.bindings.remove(&hir_id);
            }
        }
    }

    fn update_binding(&mut self, hir_id: HirId, f: impl FnOnce(&mut LocalBinding)) {
        let mut binding = self.binding(hir_id).cloned().unwrap_or_default();
        f(&mut binding);
        let old = self.bindings.insert(hir_id, binding);
        self.scopes
            .last_mut()
            .expect("root scope should always be present")
            .bindings
            .push((hir_id, old));
    }

    fn binding(&self, hir_id: HirId) -> Option<&LocalBinding> {
        self.bindings.get(&hir_id)
    }

    fn get_dependency(&self, hir_id: HirId) -> Option<&ExprDependency> {
        self.binding(hir_id).map(|binding| &binding.dependency)
    }

    fn get_callables(&self, hir_id: HirId) -> Option<&CallableTargets> {
        self.binding(hir_id).map(|binding| &binding.callables)
    }

    fn bind_dependency(&mut self, hir_id: HirId, dependency: ExprDependency) {
        self.update_binding(hir_id, |binding| binding.dependency = dependency);
    }

    fn bind_callables(&mut self, hir_id: HirId, targets: CallableTargets) {
        self.update_binding(hir_id, |binding| binding.callables = targets);
    }

    fn clear_callables(&mut self, hir_id: HirId) {
        self.update_binding(hir_id, |binding| binding.callables.clear());
    }

    fn bind_runtime_pattern(&mut self, pat: &rustc_hir::Pat<'_>) {
        pat.each_binding(|_, hir_id, _, _| {
            self.bind_dependency(hir_id, ExprDependency::Runtime);
        });
    }
}

struct SummaryContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck: &'a TypeckResults<'tcx>,
    build_assert: Option<DefId>,
    callee_summaries: &'a FunctionSummaries,
    indirect_candidates: &'a IndirectCandidates,
}

struct SummaryState {
    env: LocalEnv,
    return_dependencies: Vec<ExprDependency>,
    build_assert_conditions: FxHashMap<Span, Span>,
    seen_build_assert_callsites: FxHashSet<Span>,
    summary: FunctionSummary,
}

struct SummaryAnalyzer<'a, 'tcx> {
    cx: SummaryContext<'a, 'tcx>,
    state: SummaryState,
}

enum ResolvedCall {
    Local(LocalDefId),
    NonLocalConst,
    Other,
}

impl<'a, 'tcx> SummaryAnalyzer<'a, 'tcx> {
    /// Seed the local environment with parameter dependencies so later expression evaluation can
    /// distinguish const-only values from values that still depend on caller inputs.
    fn new(
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        typeck: &'a TypeckResults<'tcx>,
        build_assert: Option<DefId>,
        callee_summaries: &'a FunctionSummaries,
        indirect_candidates: &'a IndirectCandidates,
        body: &'tcx Body<'tcx>,
    ) -> Self {
        let mut analyzer = Self {
            cx: SummaryContext {
                tcx,
                owner,
                typeck,
                build_assert,
                callee_summaries,
                indirect_candidates,
            },
            state: SummaryState {
                env: LocalEnv::new(),
                return_dependencies: Vec::new(),
                build_assert_conditions: FxHashMap::default(),
                seen_build_assert_callsites: FxHashSet::default(),
                summary: FunctionSummary::default(),
            },
        };

        for (param_index, param) in body.params.iter().enumerate() {
            param.pat.each_binding(|_, hir_id, _, _| {
                analyzer
                    .state
                    .env
                    .bind_dependency(hir_id, ExprDependency::param(param_index));
            });
        }

        analyzer
    }

    /// Finalize one body's summary after visiting all explicit returns and the tail expression.
    fn finish_summary(mut self, body: &'tcx Body<'tcx>) -> FunctionSummary {
        let body_dependency = self.expr_dependency(body.value);
        self.state.return_dependencies.push(body_dependency);
        self.state.summary.return_dependency =
            ExprDependency::combine(self.state.return_dependencies);
        self.state.summary
    }

    fn with_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.state.env.enter_scope();
        let result = f(self);
        self.state.env.exit_scope();
        result
    }

    /// Resolve the set of local functions represented by an expression when it is used as a
    /// callable value. This is what lets the lint follow function pointers precisely enough for
    /// same-body value flow.
    fn expr_callable_targets(&self, expr: &'tcx Expr<'tcx>) -> CallableTargets {
        match expr.kind {
            rustc_hir::ExprKind::Path(ref qpath) => {
                match self.cx.typeck.qpath_res(qpath, expr.hir_id) {
                    Res::Local(local) => self
                        .state
                        .env
                        .get_callables(local)
                        .cloned()
                        .unwrap_or_default(),
                    Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => def_id
                        .as_local()
                        .filter(|&def_id| is_reportable_fn(self.cx.tcx, def_id))
                        .into_iter()
                        .collect(),
                    _ => FxHashSet::default(),
                }
            }
            rustc_hir::ExprKind::Use(inner, _)
            | rustc_hir::ExprKind::Cast(inner, _)
            | rustc_hir::ExprKind::Type(inner, _)
            | rustc_hir::ExprKind::DropTemps(inner)
            | rustc_hir::ExprKind::AddrOf(_, _, inner) => self.expr_callable_targets(inner),
            rustc_hir::ExprKind::Block(block, _) => block
                .expr
                .map(|expr| self.expr_callable_targets(expr))
                .unwrap_or_default(),
            _ => FxHashSet::default(),
        }
    }

    /// Indirect targets are resolved once up front from the mono graph and then consumed by HIR
    /// callsite id, so the summary pass does not need to know about mono items or span matching.
    fn indirect_targets_for_callsite(&self, hir_id: HirId) -> CallableTargets {
        let Some(candidates) = self.cx.indirect_candidates.get(&self.cx.owner) else {
            return FxHashSet::default();
        };
        candidates.get(&hir_id).cloned().unwrap_or_default()
    }

    fn bind_pattern(
        &mut self,
        pat: &'tcx rustc_hir::Pat<'tcx>,
        dependency: ExprDependency,
        targets: CallableTargets,
    ) {
        pat.each_binding(|_, hir_id, _, _| {
            self.state.env.bind_dependency(hir_id, dependency.clone());
            if targets.is_empty() {
                self.state.env.clear_callables(hir_id);
            } else {
                self.state.env.bind_callables(hir_id, targets.clone());
            }
        });
    }

    fn set_callable_targets(&mut self, hir_id: HirId, targets: CallableTargets) {
        if targets.is_empty() {
            self.state.env.clear_callables(hir_id);
        } else {
            self.state.env.bind_callables(hir_id, targets);
        }
    }

    fn combine_exprs<I>(&mut self, exprs: I) -> ExprDependency
    where
        I: IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        ExprDependency::combine(exprs.into_iter().map(|expr| self.expr_dependency(expr)))
    }

    fn project_param_dependencies(
        &self,
        actual_args: &[ExprDependency],
        params: &FxHashSet<usize>,
    ) -> ExprDependency {
        ExprDependency::combine(params.iter().map(|&param_index| {
            actual_args
                .get(param_index)
                .cloned()
                .unwrap_or(ExprDependency::Runtime)
        }))
    }

    fn local_fn_def_from_res(&self, res: Res) -> Option<LocalDefId> {
        match res {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => def_id.as_local(),
            _ => None,
        }
    }

    fn resolve_direct_call(&self, callee: &'tcx Expr<'tcx>) -> ResolvedCall {
        let rustc_hir::ExprKind::Path(ref qpath) = callee.kind else {
            return ResolvedCall::Other;
        };
        let resolved = self.cx.typeck.qpath_res(qpath, callee.hir_id);

        if let Some(local_def_id) = self.local_fn_def_from_res(resolved)
            && is_reportable_fn(self.cx.tcx, local_def_id)
        {
            return ResolvedCall::Local(local_def_id);
        }

        if let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = resolved
            && self.cx.tcx.is_const_fn(def_id)
        {
            return ResolvedCall::NonLocalConst;
        }

        ResolvedCall::Other
    }

    fn resolve_method_call(&self, expr: &'tcx Expr<'tcx>) -> ResolvedCall {
        let Some(def_id) = self.cx.typeck.type_dependent_def_id(expr.hir_id) else {
            return ResolvedCall::Other;
        };

        if let Some(local_def_id) = def_id.as_local()
            && is_reportable_fn(self.cx.tcx, local_def_id)
        {
            return ResolvedCall::Local(local_def_id);
        }

        if self.cx.tcx.is_const_fn(def_id) {
            return ResolvedCall::NonLocalConst;
        }

        ResolvedCall::Other
    }

    fn apply_assignment(&mut self, lhs: &'tcx Expr<'tcx>, rhs: &'tcx Expr<'tcx>) {
        let Some(local) = self.lhs_local(lhs) else {
            return;
        };

        let dependency = self.expr_dependency(rhs);
        self.state.env.bind_dependency(local, dependency);
        self.set_callable_targets(local, self.expr_callable_targets(rhs));
    }

    fn apply_assign_op(&mut self, lhs: &'tcx Expr<'tcx>) {
        let Some(local) = self.lhs_local(lhs) else {
            return;
        };

        self.state
            .env
            .bind_dependency(local, ExprDependency::Runtime);
        self.state.env.clear_callables(local);
    }

    fn apply_let_binding(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
        if let Some(init) = local.init {
            let dependency = self.expr_dependency(init);
            let targets = self.expr_callable_targets(init);
            self.bind_pattern(local.pat, dependency, targets);
        } else {
            self.state.env.bind_runtime_pattern(local.pat);
        }
    }

    /// Classify what a path depends on. Const items, const params, and immutable statics are
    /// treated as effectively constant for this lint; unresolved or mutable values are runtime.
    fn path_dependency(&self, qpath: &QPath<'tcx>, hir_id: HirId) -> ExprDependency {
        match self.cx.typeck.qpath_res(qpath, hir_id) {
            Res::Local(local) => self
                .state
                .env
                .get_dependency(local)
                .cloned()
                .unwrap_or(ExprDependency::Runtime),
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
            _ => ExprDependency::Runtime,
        }
    }

    /// Evaluate a block expression while respecting scope-local rebinding from `let` statements and
    /// assignments inside the block.
    fn block_dependency(&mut self, block: &'tcx rustc_hir::Block<'tcx>) -> ExprDependency {
        self.with_scope(|this| {
            for stmt in block.stmts {
                match stmt.kind {
                    StmtKind::Let(local) => this.apply_let_binding(local),
                    StmtKind::Expr(expr) | StmtKind::Semi(expr) => match expr.kind {
                        rustc_hir::ExprKind::Assign(lhs, rhs, _) => this.apply_assignment(lhs, rhs),
                        rustc_hir::ExprKind::AssignOp(_, lhs, _) => this.apply_assign_op(lhs),
                        _ => {}
                    },
                    StmtKind::Item(..) => {}
                }
            }

            block
                .expr
                .map(|expr| this.expr_dependency(expr))
                .unwrap_or(ExprDependency::Constant)
        })
    }

    /// Re-express a local helper's return-value dependency in terms of the caller's actual
    /// arguments. This is what allows `helper(x)` to stay parameter-sensitive instead of collapsing
    /// to a generic runtime value.
    fn mapped_callee_return_dependency<I>(
        &mut self,
        callee: LocalDefId,
        actual_args: I,
    ) -> Option<ExprDependency>
    where
        I: IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        let callee_summary = self.cx.callee_summaries.get(&callee)?;
        let actual_args: Vec<_> = actual_args
            .into_iter()
            .map(|arg| self.expr_dependency(arg))
            .collect();

        Some(match &callee_summary.return_dependency {
            ExprDependency::Constant => ExprDependency::Constant,
            ExprDependency::Param(params) => self.project_param_dependencies(&actual_args, params),
            ExprDependency::Runtime => ExprDependency::Runtime,
        })
    }

    /// Classify what value flows into an expression. This is the shared local reasoning that both
    /// direct `build_assert!` uses and propagated caller requirements build on top of.
    fn expr_dependency(&mut self, expr: &'tcx Expr<'tcx>) -> ExprDependency {
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
            rustc_hir::ExprKind::Block(block, _) => self.block_dependency(block),
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
        &mut self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> ExprDependency {
        let rustc_hir::ExprKind::Path(ref qpath) = callee.kind else {
            return ExprDependency::Runtime;
        };
        let resolved = self.cx.typeck.qpath_res(qpath, callee.hir_id);
        let args_dependency = self.combine_exprs(args.iter());

        // Tuple/struct constructors are const when all inputs are const even though
        // they surface as calls in HIR.
        if matches!(args_dependency, ExprDependency::Constant)
            && matches!(resolved, Res::Def(DefKind::Ctor(..), _))
        {
            return ExprDependency::Constant;
        }

        // If the callee is local and already summarized, project its return-value
        // dependency back onto these actual arguments instead of losing precision.
        if let Some(mapped_dependency) = self.mapped_call_dependency(
            self.resolve_direct_call(callee),
            args.iter(),
            args_dependency.clone(),
        ) {
            return mapped_dependency;
        }

        ExprDependency::Runtime
    }

    fn mapped_call_dependency<I>(
        &mut self,
        resolved: ResolvedCall,
        actual_args: I,
        constant_dependency: ExprDependency,
    ) -> Option<ExprDependency>
    where
        I: Clone + IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        match resolved {
            ResolvedCall::Local(local_def_id) => {
                self.mapped_callee_return_dependency(local_def_id, actual_args)
            }
            ResolvedCall::NonLocalConst
                if matches!(constant_dependency, ExprDependency::Constant) =>
            {
                Some(ExprDependency::Constant)
            }
            ResolvedCall::Other | ResolvedCall::NonLocalConst => None,
        }
    }

    fn method_call_expr_dependency(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        receiver: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> ExprDependency {
        let dependency = self.combine_exprs(std::iter::once(receiver).chain(args.iter()));

        // Methods on local impls use the same summary projection as free functions, but
        // include the receiver as argument zero.
        if let Some(mapped_dependency) = self.mapped_call_dependency(
            self.resolve_method_call(expr),
            std::iter::once(receiver).chain(args.iter()),
            dependency.clone(),
        ) {
            return mapped_dependency;
        }

        ExprDependency::Runtime
    }

    fn lhs_local(&self, expr: &'tcx Expr<'tcx>) -> Option<HirId> {
        if let rustc_hir::ExprKind::Path(ref qpath) = expr.kind
            && let Res::Local(local) = self.cx.typeck.qpath_res(qpath, expr.hir_id)
        {
            return Some(local);
        }

        None
    }

    /// Propagate the callee's inline requirement through one direct call by looking only at the
    /// callee parameters that actually matter to its `build_assert!` condition.
    fn propagate_callee_requirement<I>(
        &mut self,
        callee: LocalDefId,
        call_span: Span,
        actual_args: I,
    ) where
        I: IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        let Some(callee_summary) = self.cx.callee_summaries.get(&callee) else {
            return;
        };
        if callee_summary.requirement.param_dependencies.is_empty() {
            return;
        }

        let actual_args: Vec<_> = actual_args
            .into_iter()
            .map(|arg| self.expr_dependency(arg))
            .collect();

        let dependency = self.project_param_dependencies(
            &actual_args,
            &callee_summary.requirement.param_dependencies,
        );

        self.state.summary.requirement.record_propagated_use(
            dependency,
            RequirementOrigin::Propagated { callee, call_span },
        );
    }

    /// Indirect edges are pre-resolved to a set of possible local callees. Apply the same
    /// parameter-sensitive propagation to each candidate.
    fn propagate_indirect_call_targets<I>(
        &mut self,
        targets: CallableTargets,
        call_span: Span,
        actual_args: I,
    ) where
        I: Clone + IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        for callee in targets {
            if is_reportable_fn(self.cx.tcx, callee) {
                self.propagate_callee_requirement(callee, call_span, actual_args.clone());
            }
        }
    }

    /// Follow a function-pointer-like call when the callee expression itself carries a local target
    /// set, e.g. `let f = helper; f(x)`.
    fn maybe_propagate_indirect_call(
        &mut self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
        call_span: Span,
    ) {
        let targets = self.expr_callable_targets(callee);
        if !targets.is_empty() {
            self.propagate_indirect_call_targets(targets, call_span, args.iter());
        }
    }

    /// Follow dyn-dispatch and other mono-resolved method-call edges that were keyed to the source
    /// callsite during candidate collection.
    fn maybe_propagate_indirect_method_call(
        &mut self,
        hir_id: HirId,
        receiver: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
        call_span: Span,
    ) {
        let targets = self.indirect_targets_for_callsite(hir_id);
        if !targets.is_empty() {
            self.propagate_indirect_call_targets(
                targets,
                call_span,
                std::iter::once(receiver).chain(args.iter()),
            );
        }
    }
}

impl<'tcx> hir_visit::Visitor<'tcx> for SummaryAnalyzer<'_, 'tcx> {
    fn visit_block(&mut self, block: &'tcx rustc_hir::Block<'tcx>) {
        self.with_scope(|this| hir_visit::walk_block(this, block));
    }

    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) {
        match stmt.kind {
            StmtKind::Let(local) => {
                if let Some(init) = local.init {
                    self.visit_expr(init);
                }

                self.apply_let_binding(local);

                if let Some(els) = local.els {
                    self.visit_block(els);
                }
            }
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => self.visit_expr(expr),
            StmtKind::Item(item) => hir_visit::walk_item(self, self.cx.tcx.hir_item(item)),
        }
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        // Expanded HIR nodes that still carry `build_assert!` ancestry point back to the whole
        // macro invocation. Remember the recovered source condition span here, then match it
        // against ordinary source-level expressions later in the same traversal.
        if let Some(condition) = build_assert_condition(self.cx.tcx, expr, self.cx.build_assert) {
            self.state
                .build_assert_conditions
                .entry(condition.condition_span)
                .or_insert(condition.call_site);
        }

        let source_span = expr.span.source_callsite();
        if let Some(&call_site) = self.state.build_assert_conditions.get(&source_span)
            && self.state.seen_build_assert_callsites.insert(call_site)
        {
            let dependency = self.expr_dependency(expr);
            if !matches!(dependency, ExprDependency::Constant) {
                self.state
                    .summary
                    .requirement
                    .record_direct_use(dependency, call_site);
            }
        }

        match expr.kind {
            rustc_hir::ExprKind::Call(callee, args) => {
                self.visit_expr(callee);
                for arg in args {
                    self.visit_expr(arg);
                }

                if let ResolvedCall::Local(local_def_id) = self.resolve_direct_call(callee) {
                    self.propagate_callee_requirement(local_def_id, expr.span, args.iter());
                } else {
                    self.maybe_propagate_indirect_call(callee, args, expr.span);
                }
            }
            rustc_hir::ExprKind::MethodCall(_, receiver, args, _) => {
                self.visit_expr(receiver);
                for arg in args {
                    self.visit_expr(arg);
                }

                if let ResolvedCall::Local(local_def_id) = self.resolve_method_call(expr)
                    && self.cx.callee_summaries.contains_key(&local_def_id)
                {
                    self.propagate_callee_requirement(
                        local_def_id,
                        expr.span,
                        std::iter::once(receiver).chain(args.iter()),
                    );
                } else {
                    self.maybe_propagate_indirect_method_call(
                        expr.hir_id,
                        receiver,
                        args,
                        expr.span,
                    );
                }
            }
            rustc_hir::ExprKind::Assign(lhs, rhs, _) => {
                self.visit_expr(rhs);
                self.visit_expr(lhs);
                self.apply_assignment(lhs, rhs);
            }
            rustc_hir::ExprKind::AssignOp(_, lhs, rhs) => {
                self.visit_expr(rhs);
                self.visit_expr(lhs);
                self.apply_assign_op(lhs);
            }
            rustc_hir::ExprKind::Ret(Some(value)) => {
                self.visit_expr(value);
                let dependency = self.expr_dependency(value);
                self.state.return_dependencies.push(dependency);
            }
            _ => hir_visit::walk_expr(self, expr),
        }
    }
}

/// Analyze one function body against the current fixed-point summaries of its callees.
fn analyze_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck: &TypeckResults<'tcx>,
    build_assert: Option<DefId>,
    callee_summaries: &FunctionSummaries,
    indirect_candidates: &IndirectCandidates,
    body: &'tcx Body<'tcx>,
) -> FunctionSummary {
    let mut analyzer = SummaryAnalyzer::new(
        tcx,
        owner,
        typeck,
        build_assert,
        callee_summaries,
        indirect_candidates,
        body,
    );
    hir_visit::Visitor::visit_body(&mut analyzer, body);
    analyzer.finish_summary(body)
}

fn compute_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    bodies: &FxHashMap<LocalDefId, &'tcx Body<'tcx>>,
    body_owners: &[LocalDefId],
    build_assert: Option<DefId>,
    indirect_candidates: &IndirectCandidates,
) -> FunctionSummaries {
    let mut summaries = FunctionSummaries::default();

    // Iterate to a fixpoint because one local helper's summary may depend on another helper's
    // return dependency or inline requirement.
    loop {
        let mut changed = false;

        for &def_id in body_owners {
            let body = bodies[&def_id];
            let summary = analyze_body(
                tcx,
                def_id,
                tcx.typeck(def_id),
                build_assert,
                &summaries,
                indirect_candidates,
                body,
            );

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

pub struct BuildAssertNotInlined<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
    pub bodies: FxHashMap<LocalDefId, &'tcx Body<'tcx>>,
}

impl_lint_pass!(BuildAssertNotInlined<'_> => [BUILD_ASSERT_NOT_INLINED]);

impl<'tcx> LateLintPass<'tcx> for BuildAssertNotInlined<'tcx> {
    fn check_fn(
        &mut self,
        _: &LateContext<'tcx>,
        _: hir_visit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx Body<'tcx>,
        _: Span,
        def_id: LocalDefId,
    ) {
        if is_reportable_fn(self.cx.tcx, def_id) {
            self.bodies.insert(def_id, body);
        }
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let build_assert = self
            .cx
            .get_klint_diagnostic_item(crate::symbol::build_assert);

        let mut body_owners: Vec<_> = self.bodies.keys().copied().collect();
        body_owners.sort_by_key(|&def_id| cx.tcx.def_span(def_id).lo());
        let indirect_candidates = collect_indirect_candidates(cx.tcx, &self.bodies, &body_owners);
        let summaries = compute_summaries(
            cx.tcx,
            &self.bodies,
            &body_owners,
            build_assert,
            &indirect_candidates,
        );

        for def_id in body_owners {
            let Some(summary) = summaries.get(&def_id) else {
                continue;
            };

            if summary.requirement.requires_inline()
                && !has_inline_always(cx.tcx, def_id.to_def_id())
            {
                emit_build_assert_not_inlined(cx, def_id, summary);
            }
        }
    }
}
