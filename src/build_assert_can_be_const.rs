// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_lint::{LateContext, LintContext};
use rustc_session::declare_tool_lint;
use rustc_span::Span;

use crate::diagnostic::ClosureDiag;

declare_tool_lint! {
    pub klint::BUILD_ASSERT_CAN_BE_CONST,
    Warn,
    "build_assert! does not depend on runtime values and can be written as a const assert"
}

pub(crate) fn emit_build_assert_can_be_const(cx: &LateContext<'_>, span: Span) {
    cx.emit_span_lint(
        BUILD_ASSERT_CAN_BE_CONST,
        span,
        ClosureDiag(|diag| {
            diag.primary_message(
                "this `build_assert!` does not depend on runtime values; prefer `const { assert!(...) }` instead",
            );
            diag.span_note(
                span,
                "this assertion is already effectively constant, so it does not need `build_assert!` to optimize away an error path",
            );
        }),
    );
}
