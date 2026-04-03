// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_hir::def_id::{CrateNum, DefId, LocalDefId};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::ty::{Instance, PseudoCanonicalInput, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::Span;

use crate::ctxt::{AnalysisCtxt, PersistentQuery};

declare_tool_lint! {
    pub klint::BUILD_ASSERT_NOT_INLINED,
    Warn,
    "function depends on build_assert! but is not marked #[inline(always)]"
}

const PRIMARY_MESSAGE: &str = "this function depends on non-static values used by `build_assert!` and should be marked `#[inline(always)]`; otherwise its error path may fail to optimize away";

#[derive(Diagnostic)]
#[diag("{$primary}")]
struct BuildAssertNotInlined {
    #[primary_span]
    #[suggestion(
        "mark this function `#[inline(always)]`",
        code = "{inline_attr}",
        applicability = "machine-applicable"
    )]
    pub fn_span: Span,
    #[subdiagnostic]
    pub origin_note: Option<BuildAssertOriginNote>,
    pub primary: &'static str,
    pub inline_attr: String,
}

#[derive(Subdiagnostic)]
enum BuildAssertOriginNote {
    #[note("`build_assert!` uses non-static values here and relies on the surrounding call chain being inlined")]
    Direct {
        #[primary_span]
        span: Span,
    },
    #[note("this call passes non-static values into `{$callee}` which must be inlined for `build_assert!` to optimize away")]
    Propagated {
        #[primary_span]
        span: Span,
        callee: String,
    },
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RequirementOrigin {
    Direct { span: Span },
    Propagated { callee: DefId, call_span: Span },
}

pub(crate) fn has_inline_always(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.codegen_fn_attrs(def_id).inline.always()
}

fn inline_always_suggestion(cx: &LateContext<'_>, fn_span: Span) -> String {
    let indent = cx
        .sess()
        .source_map()
        .indentation_before(fn_span)
        .unwrap_or_default();
    format!("#[inline(always)]\n{indent}")
}

pub(crate) fn emit_build_assert_not_inlined(
    cx: &LateContext<'_>,
    def_id: LocalDefId,
    origin: Option<RequirementOrigin>,
) {
    let fn_span = cx.tcx.def_span(def_id);
    let inline_attr = inline_always_suggestion(cx, fn_span.shrink_to_lo());
    let origin_note = match origin {
        Some(RequirementOrigin::Direct { span }) => Some(BuildAssertOriginNote::Direct { span }),
        Some(RequirementOrigin::Propagated { callee, call_span }) => {
            Some(BuildAssertOriginNote::Propagated {
                span: call_span,
                callee: cx.tcx.def_path_str(callee),
            })
        }
        None => None,
    };

    cx.emit_span_lint(
        BUILD_ASSERT_NOT_INLINED,
        fn_span,
        BuildAssertNotInlined {
            fn_span: fn_span.shrink_to_lo(),
            origin_note,
            primary: PRIMARY_MESSAGE,
            inline_attr,
        },
    );
}

pub struct BuildAssertLints<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
}

impl_lint_pass!(BuildAssertLints<'_> => [BUILD_ASSERT_NOT_INLINED]);

impl<'tcx> LateLintPass<'tcx> for BuildAssertLints<'tcx> {
    fn check_crate_post(&mut self, _cx: &LateContext<'tcx>) {
        let _ = self.cx;
    }
}

#[derive(Clone, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SmallSet<T>(Vec<T>);

impl<T> Default for SmallSet<T> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub(crate) enum ExprDependency {
    #[default]
    Constant,
    Param(SmallSet<usize>),
    Runtime,
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SemanticRequirementSummary {
    pub(crate) param_dependencies: SmallSet<usize>,
    has_local_runtime_dependency: bool,
    has_unknown_dependency: bool,
}

#[derive(Clone, Default, PartialEq, Eq, Encodable, Decodable)]
pub(crate) struct SemanticFunctionSummary {
    pub(crate) requirement: SemanticRequirementSummary,
    return_dependency: ExprDependency,
}

memoize!(
    pub(crate) fn instance_build_assert_summary<'tcx>(
        _cx: &AnalysisCtxt<'tcx>,
        _poly_instance: PseudoCanonicalInput<'tcx, Instance<'tcx>>,
    ) -> Option<SemanticFunctionSummary> {
        None
    }
);

impl PersistentQuery for instance_build_assert_summary {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub(crate) fn encode_build_assert_summaries(&self) {}
}
