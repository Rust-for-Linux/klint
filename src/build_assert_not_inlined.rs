// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_lint::{LateContext, LintContext};
use rustc_middle::ty::TyCtxt;
use rustc_session::declare_tool_lint;

use crate::build_assert::{FunctionSummary, RequirementOrigin};
use crate::diagnostic::ClosureDiag;

declare_tool_lint! {
    pub klint::BUILD_ASSERT_NOT_INLINED,
    Warn,
    "function depends on build_assert! but is not marked #[inline(always)]"
}

/// This lint is about the source-level contract of user-authored functions, so only
/// `#[inline(always)]` counts as satisfying it.
pub(crate) fn has_inline_always(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.codegen_fn_attrs(def_id).inline.always()
}

pub(crate) fn emit_build_assert_not_inlined(
    cx: &LateContext<'_>,
    def_id: LocalDefId,
    summary: &FunctionSummary,
) {
    cx.emit_span_lint(
        BUILD_ASSERT_NOT_INLINED,
        cx.tcx.def_span(def_id),
        ClosureDiag(|diag| {
            diag.primary_message(
                "this function depends on non-static values used by `build_assert!` and should be marked `#[inline(always)]`; otherwise its error path may fail to optimize away",
            );

            match summary.requirement.origin {
                Some(RequirementOrigin::Direct { span }) => {
                    diag.span_note(
                        span,
                        "`build_assert!` uses non-static values here and relies on the surrounding call chain being inlined",
                    );
                }
                Some(RequirementOrigin::Propagated { callee, call_span }) => {
                    diag.span_note(
                        call_span,
                        format!(
                            "this call passes non-static values into `{}` which must be inlined for `build_assert!` to optimize away",
                            cx.tcx.def_path_str(callee.to_def_id())
                        ),
                    );
                }
                None => {}
            }
        }),
    );
}
