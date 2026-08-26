// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::sync::Arc;

use rustc_ast::{LitKind, MetaItemLit};
use rustc_hir::{AttrArgs, Attribute, HirId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};

use crate::preempt_count::attribute::PreemptionCount;
use crate::preempt_count::{self, ExpectationRange};

#[derive(Debug)]
pub enum KlintAttribute {
    PreemptionCount(PreemptionCount),
    DropPreemptionCount(PreemptionCount),
    ReportPreeptionCount,
    DumpMir,
    /// Make an item known to klint as special.
    ///
    /// This is similar to `rustc_diagnostic_item` in the Rust standard library.
    DiagnosticItem(Symbol),
}

#[derive(Diagnostic)]
#[diag("unrecognized klint attribute")]
struct UnknownAttribute {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("invalid klint attribute")]
struct InvalidAttribute {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("incorrect usage of `#[kint::diagnostic_item]`")]
#[help(r#"correct usage looks like `#[kint::diagnostic_item = "name"]`"#)]
struct InvalidDiagnosticItem {
    #[primary_span]
    pub span: Span,
}

pub fn parse_klint_attribute(tcx: TyCtxt<'_>, attr: &Attribute) -> Option<KlintAttribute> {
    let Attribute::Unparsed(item) = attr else {
        return None;
    };
    if item.path.segments[0] != crate::symbol::klint {
        return None;
    };
    if item.path.segments.len() != 2 {
        tcx.dcx().emit_err(InvalidAttribute { span: item.span });
        return None;
    }
    match item.path.segments[1] {
        // Shorthands
        crate::symbol::any_context | crate::symbol::atomic_context => {
            Some(KlintAttribute::PreemptionCount(PreemptionCount {
                adjustment: None,
                expectation: Some(ExpectationRange::top()),
                unchecked: false,
            }))
        }
        crate::symbol::atomic_context_only => {
            Some(KlintAttribute::PreemptionCount(PreemptionCount {
                adjustment: None,
                expectation: Some(ExpectationRange { lo: 1, hi: None }),
                unchecked: false,
            }))
        }
        crate::symbol::process_context => Some(KlintAttribute::PreemptionCount(PreemptionCount {
            adjustment: None,
            expectation: Some(ExpectationRange::single_value(0)),
            unchecked: false,
        })),

        crate::symbol::preempt_count => Some(KlintAttribute::PreemptionCount(
            preempt_count::attribute::parse_preempt_count(tcx, attr, item).ok()?,
        )),
        crate::symbol::drop_preempt_count => Some(KlintAttribute::DropPreemptionCount(
            preempt_count::attribute::parse_preempt_count(tcx, attr, item).ok()?,
        )),
        crate::symbol::report_preempt_count => Some(KlintAttribute::ReportPreeptionCount),
        crate::symbol::dump_mir => Some(KlintAttribute::DumpMir),
        crate::symbol::diagnostic_item => {
            let AttrArgs::Eq {
                eq_span: _,
                expr:
                    MetaItemLit {
                        kind: LitKind::Str(value, _),
                        ..
                    },
            } = item.args
            else {
                tcx.dcx()
                    .emit_err(InvalidDiagnosticItem { span: attr.span() });
                None?
            };

            Some(KlintAttribute::DiagnosticItem(value))
        }
        _ => {
            tcx.dcx().emit_err(UnknownAttribute {
                span: item.path.span,
            });
            None
        }
    }
}

memoize!(
    pub fn klint_attributes<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        hir_id: HirId,
    ) -> Arc<Vec<KlintAttribute>> {
        let mut v = Vec::new();
        for attr in cx.hir_attrs(hir_id) {
            let Some(attr) = crate::attribute::parse_klint_attribute(cx.tcx, attr) else {
                continue;
            };
            v.push(attr);
        }
        Arc::new(v)
    }
);
