use rustc_hir::Expr;
use rustc_lint::{LateContext, LateLintPass, LintContext, declare_tool_lint, impl_lint_pass};
use rustc_span::{self, Span, Symbol};

use crate::ctxt::AnalysisCtxt;

declare_tool_lint! {
    /// The `c_str_literal` lint detects when the kernel `c_str!` macro is used on a string literal.
    pub klint::C_STR_LITERAL,
    Warn,
    "`c_str!` used on a string literal"
}

pub struct CStrLiteralLint<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
}

impl_lint_pass!(CStrLiteralLint<'_> => [C_STR_LITERAL]);

#[derive(Diagnostic)]
#[diag("`{$macro_name}!` is used on a literal")]
struct CStrLiteral {
    #[primary_span]
    #[suggestion(
        "use C-string literals instead",
        code = "c{arg}",
        applicability = "machine-applicable"
    )]
    pub span: Span,
    pub macro_name: Symbol,
    pub arg: String,
}

impl<'tcx> CStrLiteralLint<'tcx> {
    fn extract_arg(&self, span: Span) -> Option<String> {
        let source = self.cx.sess.source_map().span_to_snippet(span).ok()?;

        let arg = source.split_once('!')?.1;
        if arg.len() <= 2 {
            return None;
        }

        Some(arg[1..arg.len() - 1].trim().to_owned())
    }
}

impl<'tcx> LateLintPass<'tcx> for CStrLiteralLint<'tcx> {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        // If would be ideal if we can check before macro expansion. However, pre_expansion_lint is
        // not recommended because the lint level infrastructure if not yet ready, and also it does
        // not have information of the name resolution available so we cannot precisely determine if
        // the macro is something that we want to lint now.
        //
        // So, as an alternative strategy, try to backtrace macros and find an expression that is expanded
        // from the `c_str!` macro. Once that found, use span information to recover the argument used to
        // call the macro.
        //
        // However, given that `c_str!` have used `concat!()` internally, there is no single span in the
        // expanded HIR that maps to the input argument... As a very crude approximation, use source map
        // to obtain the source and check based on that. This is also very hacky but at least lint level
        // and name resolution works as intended...

        // TODO: This check will replicated multiple times for each sub-expression of `c_str!`.
        // It might be good if we stop early and stop recursing into sub-expressions, although this is not
        // something that can be achieved with `LateLintPass`.
        let span = expr.span;
        let Some(expn_data) = span.macro_backtrace().next() else {
            return;
        };

        let Some(c_str) = self.cx.get_klint_diagnostic_item(crate::symbol::c_str) else {
            return;
        };

        if expn_data.macro_def_id != Some(c_str) {
            return;
        }

        if let Some(arg) = self.extract_arg(expn_data.call_site) {
            if arg.starts_with('"') && arg.ends_with('"') {
                cx.emit_span_lint(
                    C_STR_LITERAL,
                    expn_data.call_site,
                    CStrLiteral {
                        span: expn_data.call_site,
                        macro_name: self.cx.item_name(c_str),
                        arg,
                    },
                );
            }
        }
    }
}
