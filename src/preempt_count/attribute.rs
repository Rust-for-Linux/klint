use std::borrow::Cow;

use rustc_ast::token::TokenKind;
use rustc_ast::{DelimArgs, Expr, ExprKind, LitKind, RangeLimits, UnOp};
use rustc_errors::{ErrorGuaranteed, PResult};
use rustc_hir::{AttrArgs, AttrItem, Attribute};
use rustc_middle::ty::TyCtxt;
use rustc_parse::exp;
use rustc_parse::parser::Parser;
use rustc_span::{Span, sym};

use crate::preempt_count::ExpectationRange;

#[derive(Diagnostic)]
#[diag("incorrect usage of `#[kint::preempt_count]`")]
#[help("{$help}")]
struct InvalidPreemptCountAttribute {
    #[primary_span]
    pub span: Span,
    pub help: Cow<'static, str>,
}

#[derive(Debug, Clone, Copy, Encodable, Decodable)]
pub struct PreemptionCount {
    pub adjustment: Option<i32>,
    pub expectation: Option<ExpectationRange>,
    pub unchecked: bool,
}

impl Default for PreemptionCount {
    fn default() -> Self {
        PreemptionCount {
            adjustment: None,
            expectation: None,
            unchecked: false,
        }
    }
}

struct AttrParser<'a, 'tcx> {
    parser: &'a mut Parser<'tcx>,
}

impl<'a, 'tcx> AttrParser<'a, 'tcx> {
    fn convert_small_int(&self, span: Span, lit: rustc_ast::token::Lit) -> PResult<'a, u32> {
        match LitKind::from_token_lit(lit) {
            Ok(LitKind::Int(val, _)) if val > 1024 => {
                Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                    span,
                    help: "value exeeds range".into(),
                }))
            }
            Ok(LitKind::Int(val, _)) => Ok(val.0 as u32),
            Ok(_) => Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                span,
                help: "literal is not integer".into(),
            })),
            Err(err) => Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                span,
                help: format!("{err:?}").into(),
            })),
        }
    }

    fn convert_small_literal(&self, expr: &Expr) -> PResult<'_, u32> {
        match expr.kind {
            ExprKind::Lit(lit) => self.convert_small_int(expr.span, lit),
            _ => Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                span: expr.span,
                help: "unexpected expression".into(),
            })),
        }
    }

    fn convert_small_literal_with_minus(&self, expr: &Expr) -> PResult<'_, i32> {
        match expr.kind {
            ExprKind::Lit(lit) => Ok(self.convert_small_int(expr.span, lit)? as i32),
            ExprKind::Unary(
                UnOp::Neg,
                Expr {
                    kind: ExprKind::Lit(lit),
                    span: lit_span,
                    ..
                },
            ) => {
                let val = self.convert_small_int(lit_span, lit)? as i32;
                Ok(-val)
            }
            _ => Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                span: expr.span,
                help: "unexpected expression".into(),
            })),
        }
    }

    fn parse_preempt_count(&mut self) -> PResult<'_, PreemptionCount> {
        let mut adjustment = None;
        let mut expectation = None;
        let mut unchecked = false;

        loop {
            if self.parser.token.kind == TokenKind::Eof {
                break;
            }

            let property = self.parser.parse_ident()?;

            match property.name {
                crate::symbol::adjust => {
                    self.parser.expect(exp!(Eq))?;

                    let expr = self.parser.parse_expr()?;
                    let v = self.convert_small_literal_with_minus(&expr)?;
                    adjustment = Some(v);
                }
                sym::expect => {
                    self.parser.expect(exp!(Eq))?;

                    let expr = self.parser.parse_expr()?;
                    let (lo, hi) = match expr.kind {
                        ExprKind::Range(range_start, range_end, limit) => {
                            let start = match range_start {
                                None => 0,
                                Some(v) => self.convert_small_literal(&v)?,
                            };

                            let end = match range_end {
                                None => None,
                                Some(v) => {
                                    let end = self.convert_small_literal(&v)?;
                                    match limit {
                                        RangeLimits::HalfOpen => Some(end),
                                        RangeLimits::Closed => Some(end + 1),
                                    }
                                }
                            };

                            if end.is_some() && end.unwrap() <= start {
                                Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                                    span: expr.span,
                                    help:
                                        "the preemption count expectation range must be non-empty"
                                            .into(),
                                }))?
                            }

                            (start, end)
                        }

                        _ => {
                            let v = self.convert_small_literal(&expr)?;
                            (v, Some(v + 1))
                        }
                    };

                    expectation = Some(ExpectationRange { lo, hi });
                }

                crate::symbol::unchecked => {
                    unchecked = true;
                }

                _ => Err(self.parser.dcx().create_err(InvalidPreemptCountAttribute {
                    span: property.span,
                    help: "unknown property, expected `adjust`, `expect` or `unchecked`".into(),
                }))?,
            }

            if self.parser.token.kind == TokenKind::Eof {
                break;
            }

            self.parser.expect(exp!(Comma))?;
        }

        Ok(PreemptionCount {
            adjustment,
            expectation,
            unchecked,
        })
    }
}

pub(crate) fn parse_preempt_count<'tcx>(
    tcx: TyCtxt<'tcx>,
    attr: &Attribute,
    item: &AttrItem,
) -> Result<PreemptionCount, ErrorGuaranteed> {
    let AttrArgs::Delimited(DelimArgs { dspan, tokens, .. }) = &item.args else {
        Err(tcx.dcx().emit_err(InvalidPreemptCountAttribute {
            span: attr.span(),
            help: "correct usage looks like `#[kint::preempt_count(...)]`".into(),
        }))?
    };

    let mut parser = Parser::new(&tcx.sess.psess, tokens.clone(), Some("attribute"));

    let v = match (AttrParser {
        parser: &mut parser,
    })
    .parse_preempt_count()
    {
        Ok(v) => v,
        Err(err) => Err(err.emit())?,
    };

    if v.adjustment.is_none() && v.expectation.is_none() {
        Err(tcx.dcx().emit_err(InvalidPreemptCountAttribute {
            span: dspan.entire(),
            help: "at least one of `adjust` or `expect` property must be specified".into(),
        }))?
    }

    Ok(v)
}
