use rustc_ast::{MacCall, token};
use rustc_ast::tokenstream::TokenTree;
use rustc_lint::{EarlyContext, EarlyLintPass, LintContext};
use rustc_session::{declare_tool_lint, impl_lint_pass};

declare_tool_lint! {
    /// The `pr_missing_newline` lint detects `pr_*` calls that do not end with a newline.
    pub klint::PR_MISSING_NEWLINE,
    Warn,
    "pr_* logging calls should end with a trailing \"\\n\""
}

pub struct PrMissingNewline;

impl_lint_pass!(PrMissingNewline => [PR_MISSING_NEWLINE]);

impl EarlyLintPass for PrMissingNewline {
    fn check_mac(&mut self, cx: &EarlyContext<'_>, mac: &MacCall) {
        // Check if the macro path starts with "pr_"
        if let Some(segment) = mac.path.segments.last() {
            let name = segment.ident.as_str();
            if !name.starts_with("pr_") {
                return;
            }
            if name == "pr_cont" {
                return;
            }
        } else {
            return;
        }

        // We want to check the first argument of the macro.
        // The arguments are in `mac.args`. This is a `MacArgs`.
        // We usually expect `MacArgs::Delimited`.
        
        // `mac.args` appears to be `P<DelimArgs>` in this toolchain.
        let tokens = &mac.args.tokens;

        // We need to look at the tokens to find the format string.
        // This is a simplified check assuming the first token is a string literal.
        // A robust check might need to parse the token stream, but for `pr_info!("str")`
        // checking the first token tree is often enough if we skip whitespace/comments?
        // Actually, `rustc_ast` usually gives us a stream.
        
        // We need to look at the tokens to find the format string.
        for tt in tokens.iter() {
            if let TokenTree::Token(token, _) = tt {
                if let token::TokenKind::Literal(lit) = token.kind {
                     if matches!(lit.kind, token::LitKind::Str | token::LitKind::StrRaw(_)) {
                         let msg = lit.symbol.as_str();
                         if !msg.ends_with('\n') {
                            cx.span_lint(PR_MISSING_NEWLINE, mac.span(), |diag| {
                                diag.primary_message("pr_* logging calls should end with a trailing \"\\n\"");
                            });
                         }
                         // We found the format string, stop checking.
                         return;
                     }
                }
            }
        }
    }
}
