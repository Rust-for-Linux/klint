//! Utility for generating diagnostic information that involves chains.
//!
//! For example, when giving context about why a specific instance is used, a call stack (or rather, use stack,
//! as some usage may be due to pointer coercion or static reference).

use rustc_errors::{Diag, EmissionGuarantee, MultiSpan};
use rustc_hir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgs, Instance, PseudoCanonicalInput, TypingEnv};
use rustc_span::{Span, sym};

use crate::ctxt::AnalysisCtxt;
use crate::diagnostic::PolyDisplay;

#[derive(Debug)]
pub enum UseSiteKind {
    /// Used due to a direct function call.
    Call(Span),
    /// Used due to a variable drop.
    Drop {
        /// Span that causes the drop.
        drop_span: Span,
        /// Span of the place being dropped.
        place_span: Span,
    },
    /// A function is used when it is coerced into a function pointer.
    PointerCoercion(Span),
    /// A function is used as it is a trait method and the trait vtable is constructed.
    Vtable(Span),
    /// Some other type of usage.
    Other(Span, String),
}

impl UseSiteKind {
    pub fn span(&self) -> Span {
        match self {
            UseSiteKind::Call(span)
            | UseSiteKind::Drop {
                drop_span: span,
                place_span: _,
            }
            | UseSiteKind::PointerCoercion(span)
            | UseSiteKind::Vtable(span)
            | UseSiteKind::Other(span, _) => *span,
        }
    }

    pub fn multispan(&self) -> MultiSpan {
        match self {
            UseSiteKind::Call(span)
            | UseSiteKind::PointerCoercion(span)
            | UseSiteKind::Vtable(span)
            | UseSiteKind::Other(span, _) => MultiSpan::from_span(*span),
            UseSiteKind::Drop {
                drop_span,
                place_span,
            } => {
                let mut multispan = MultiSpan::from_span(*drop_span);
                multispan.push_span_label(*place_span, "value being dropped is here");
                multispan
            }
        }
    }
}

#[derive(Debug)]
pub struct UseSite<'tcx> {
    /// A instance that makes the use.
    pub instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,

    /// A specific use occured in the instance.
    pub kind: UseSiteKind,
}

impl<'tcx> AnalysisCtxt<'tcx> {
    /// Obtain the polymorphic instance of `def_id`.
    fn poly_instance_of_def_id(&self, def_id: DefId) -> PseudoCanonicalInput<'tcx, Instance<'tcx>> {
        let poly_typing_env = TypingEnv::post_analysis(self.tcx, def_id);
        let poly_args =
            self.erase_and_anonymize_regions(GenericArgs::identity_for_item(self.tcx, def_id));
        poly_typing_env.as_query_input(Instance::new_raw(def_id, poly_args))
    }

    /// Determine if the instance is fully polymorphic, or if it is already specialized.
    fn is_fully_polymorphic(&self, instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>) -> bool {
        self.poly_instance_of_def_id(instance.value.def_id()) == instance
    }

    pub fn note_use_stack<G: EmissionGuarantee>(
        &self,
        diag: &mut Diag<'tcx, G>,
        use_stack: &[UseSite<'tcx>],
    ) {
        for site in use_stack.iter().rev() {
            let def_id = site.instance.value.def_id();
            if self.is_lang_item(def_id, LangItem::DropGlue) {
                let ty = site.instance.value.args[0];
                diag.note(format!("which is called from drop glue of `{ty}`"));
                continue;
            }

            // Hide `drop()` call from stack as it's mostly noise.
            if self.is_diagnostic_item(sym::mem_drop, def_id) {
                continue;
            }

            if diag.span.is_dummy() {
                diag.span = site.kind.multispan();
            } else {
                match &site.kind {
                    UseSiteKind::Call(span) => {
                        diag.span_note(*span, "which is called from here");
                    }
                    UseSiteKind::Drop {
                        drop_span,
                        place_span,
                    } => {
                        let mut multispan = MultiSpan::from_span(*drop_span);
                        multispan.push_span_label(*place_span, "value being dropped is here");
                        diag.span_note(multispan, "which is dropped here");
                    }
                    UseSiteKind::PointerCoercion(span) => {
                        diag.span_note(*span, "which is used as a pointer here");
                    }
                    UseSiteKind::Vtable(span) => {
                        diag.span_note(*span, "which is used as a vtable here");
                    }
                    UseSiteKind::Other(span, other) => {
                        diag.span_note(*span, other.clone());
                    }
                }
            }

            if !self.is_fully_polymorphic(site.instance) {
                diag.note(format!("inside instance `{}`", PolyDisplay(&site.instance)));
            }
        }
    }
}
