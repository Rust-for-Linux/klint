// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::HirId;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{Expr, UnOp};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

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

type CallableTargets = FxHashSet<LocalDefId>;
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
