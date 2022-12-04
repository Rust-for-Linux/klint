use rustc_ast::{ast, token, tokenstream::TokenTree};
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;

use crate::atomic_context::PreemptionCountRange;

#[derive(Debug)]
pub enum KlintAttribute {
    PreemptionCount {
        adjustment: Option<i32>,
        assumption: Option<PreemptionCountRange>,
    },
}

pub fn parse_klint_attribute(
    tcx: TyCtxt<'_>,
    hir_id: HirId,
    attr: &ast::Attribute,
) -> Option<KlintAttribute> {
    let ast::AttrKind::Normal(normal_attr) = &attr.kind else { return None };
    let item = &normal_attr.item;
    if item.path.segments[0].ident.name != *crate::symbol::klint {
        return None;
    };
    if item.path.segments.len() != 2 {
        tcx.struct_span_lint_hir(
            crate::INCORRECT_ATTRIBUTE,
            hir_id,
            attr.span,
            "invalid klint attribute",
            |diag| diag,
        );
        return None;
    }
    match item.path.segments[1].ident.name {
        v if v == *crate::symbol::preempt_count => {
            let mut adjustment = None;
            let mut assumption = None;

            let ast::MacArgs::Delimited(delim_span, _, tts) = &item.args else {
                tcx.struct_span_lint_hir(
                    crate::INCORRECT_ATTRIBUTE,
                    hir_id,
                    attr.span,
                    "incorrect usage of `#[kint::preempt_count]`",
                    |diag| {
                        diag.help("correct usage looks like `#[kint::preempt_count(...)]`")
                    },
                );
                return None;
            };

            let mut cursor = tts.trees();
            while let Some(prop) = cursor.next() {
                let invalid_prop = |span| {
                    tcx.struct_span_lint_hir(
                        crate::INCORRECT_ATTRIBUTE,
                        hir_id,
                        span,
                        "incorrect usage of `#[kint::preempt_count]`",
                        |diag| diag.help("`adjust` or `assume` expected"),
                    );
                    None
                };

                let TokenTree::Token(token, _) = prop else { return invalid_prop(delim_span.close) };
                let Some((name, _)) = token.ident() else { return invalid_prop(token.span) };
                let expect = match name.name {
                    v if v == *crate::symbol::adjust => false,
                    v if v == *crate::symbol::expect => true,
                    _ => {
                        return invalid_prop(token.span);
                    }
                };

                // Check and skip `=`.
                let expect_eq = |span| {
                    tcx.struct_span_lint_hir(
                        crate::INCORRECT_ATTRIBUTE,
                        hir_id,
                        span,
                        "incorrect usage of `#[kint::preempt_count]`",
                        |diag| diag.help("`=` expected after property name"),
                    );
                    None
                };
                let Some(eq) = cursor.next() else { return expect_eq(delim_span.close) };
                if !matches!(
                    eq,
                    TokenTree::Token(
                        token::Token {
                            kind: token::TokenKind::Eq,
                            ..
                        },
                        _
                    )
                ) {
                    return expect_eq(eq.span());
                }

                if !expect {
                    // Parse adjustment, which is a single integer literal.
                    let expect_int = |span| {
                        tcx.struct_span_lint_hir(
                            crate::INCORRECT_ATTRIBUTE,
                            hir_id,
                            span,
                            "incorrect usage of `#[kint::preempt_count]`",
                            |diag| diag.help("an integer expected as the value of `adjust`"),
                        );
                        None
                    };

                    let negative = if matches!(
                        cursor.look_ahead(0),
                        Some(TokenTree::Token(
                            token::Token {
                                kind: token::TokenKind::BinOp(token::BinOpToken::Minus),
                                ..
                            },
                            _
                        ))
                    ) {
                        cursor.next();
                        true
                    } else {
                        false
                    };

                    let Some(token) = cursor.next() else { return expect_int(delim_span.close) };
                    let TokenTree::Token(
                        token::Token {
                            kind: token::TokenKind::Literal(lit),
                            ..
                        },
                        _,
                    ) = token else { return expect_int(token.span()) };
                    if lit.kind != token::LitKind::Integer || lit.suffix.is_some() {
                        return expect_int(token.span());
                    }
                    let Some(v) = lit.symbol.as_str().parse::<i32>().ok() else {
                        return expect_int(token.span());
                    };
                    let v = if negative { -v } else { v };
                    adjustment = Some(v);
                } else {
                    // Parse assumption, which is a range.
                    let expect_range = |span| {
                        tcx.struct_span_lint_hir(
                            crate::INCORRECT_ATTRIBUTE,
                            hir_id,
                            span,
                            "incorrect usage of `#[kint::preempt_count]`",
                            |diag| diag.help("a range expected as the value of `expect`"),
                        );
                        None
                    };

                    let start_span = cursor
                        .look_ahead(0)
                        .map(|t| t.span())
                        .unwrap_or(delim_span.close);
                    let mut start = 0;
                    if !matches!(
                        cursor.look_ahead(0),
                        Some(TokenTree::Token(
                            token::Token {
                                kind: token::TokenKind::DotDot | token::TokenKind::DotDotEq,
                                ..
                            },
                            _
                        ))
                    ) {
                        let Some(token) = cursor.next() else { return expect_range(delim_span.close) };
                        let TokenTree::Token(
                            token::Token {
                                kind: token::TokenKind::Literal(lit),
                                ..
                            },
                            _,
                        ) = token else { return expect_range(token.span()) };
                        if lit.kind != token::LitKind::Integer {
                            return expect_range(token.span());
                        }
                        let Some(v) = lit.symbol.as_str().parse::<u32>().ok() else {
                            return expect_range(token.span());
                        };
                        start = v;
                    }

                    let inclusive = match cursor.look_ahead(0) {
                        Some(TokenTree::Token(
                            token::Token {
                                kind: token::TokenKind::DotDot,
                                ..
                            },
                            _,
                        )) => Some(false),
                        Some(TokenTree::Token(
                            token::Token {
                                kind: token::TokenKind::DotDotEq,
                                ..
                            },
                            _,
                        )) => Some(true),
                        _ => None,
                    };

                    let mut end = Some(start + 1);
                    if let Some(inclusive) = inclusive {
                        cursor.next();

                        let skip_hi = match cursor.look_ahead(0) {
                            Some(TokenTree::Token(
                                token::Token {
                                    kind: token::TokenKind::Comma,
                                    ..
                                },
                                _,
                            )) => true,
                            None => true,
                            _ => false,
                        };

                        if skip_hi {
                            end = None;
                        } else {
                            dbg!(skip_hi);
                            let Some(token) = cursor.next() else { return expect_range(delim_span.close) };
                            let TokenTree::Token(
                                token::Token {
                                    kind: token::TokenKind::Literal(lit),
                                    ..
                                },
                                _,
                            ) = token else { return expect_range(token.span()) };
                            if lit.kind != token::LitKind::Integer {
                                return expect_range(token.span());
                            }
                            let Some(range) = lit.symbol.as_str().parse::<u32>().ok() else {
                                return expect_range(token.span());
                            };

                            end = Some(if inclusive { range + 1 } else { range });
                        }
                    }

                    if end.is_some() && end.unwrap() <= start {
                        let end_span = cursor.next().map(|t| t.span()).unwrap_or(delim_span.close);

                        tcx.struct_span_lint_hir(
                            crate::INCORRECT_ATTRIBUTE,
                            hir_id,
                            start_span.until(end_span),
                            "incorrect usage of `#[kint::preempt_count]`",
                            |diag| {
                                diag.help("the preemption count assumption range must be non-empty")
                            },
                        );
                    }

                    assumption = Some(PreemptionCountRange { lo: start, hi: end });
                }

                // End of attribute arguments.
                if cursor.look_ahead(0).is_none() {
                    break;
                }

                // Check and skip `,`.
                let expect_comma = |span| {
                    tcx.struct_span_lint_hir(
                        crate::INCORRECT_ATTRIBUTE,
                        hir_id,
                        span,
                        "incorrect usage of `#[kint::preempt_count]`",
                        |diag| diag.help("`,` expected between property values"),
                    );
                    None
                };

                let Some(comma) = cursor.next() else { return expect_comma(delim_span.close) };
                if !matches!(
                    comma,
                    TokenTree::Token(
                        token::Token {
                            kind: token::TokenKind::Comma,
                            ..
                        },
                        _
                    )
                ) {
                    return expect_comma(comma.span());
                }
            }

            if adjustment.is_none() && assumption.is_none() {
                tcx.struct_span_lint_hir(
                    crate::INCORRECT_ATTRIBUTE,
                    hir_id,
                    item.args.span().unwrap(),
                    "incorrect usage of `#[kint::preempt_count]`",
                    |diag| diag.help("at least one property must be specified"),
                );
            }

            Some(KlintAttribute::PreemptionCount {
                adjustment,
                assumption,
            })
        }
        _ => {
            tcx.struct_span_lint_hir(
                crate::INCORRECT_ATTRIBUTE,
                hir_id,
                item.path.segments[1].span(),
                "unrecognized klint attribute",
                |diag| diag,
            );
            None
        }
    }
}
