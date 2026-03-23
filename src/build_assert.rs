// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
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
