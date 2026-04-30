use iced_x86::{Decoder, DecoderOptions, Mnemonic, OpKind, Register};
use object::{Architecture, File, Object, ObjectSection, SectionKind};
use rustc_data_structures::fx::FxHashSet;
use rustc_errors::{Diag, Diagnostic, Level};
use rustc_hir::CRATE_HIR_ID;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::Instance;
use rustc_session::declare_tool_lint;
use rustc_span::{Span, Symbol, sym};

use crate::ctxt::AnalysisCtxt;

declare_tool_lint! {
    //// The `stack_frame_too_large` lint detects large stack frames that may potentially
    /// lead to stack overflow.
    pub klint::STACK_FRAME_TOO_LARGE,
    Allow,
    "frame size is too large"
}

#[derive(Diagnostic)]
#[diag("stack size limit is not set, default to {$default} bytes")]
#[help("set stack size limit with `--cfg CONFIG_FRAME_WARN=\"<size-in-bytes>\"`")]
struct StackFrameLimitMissing {
    #[primary_span]
    pub span: Span,
    pub default: u32,
}

#[derive(Diagnostic)]
#[diag("stack size limit is set to `{$setting}` bytes, which cannot be parsed as integer")]
#[help("set stack size limit with `--cfg CONFIG_FRAME_WARN=\"<size-in-bytes>\"`")]
struct StackFrameLimitInvalid {
    #[primary_span]
    pub span: Span,
    pub setting: Symbol,
}

#[derive(Diagnostic)]
#[diag("stack size of `{$instance}` is {$stack_size} bytes, exceeds the {$frame_limit}-byte limit")]
#[note("the stack size is inferred from instruction `{$insn}` at {$section}+{$offset}")]
struct StackFrameTooLarge<'a, 'tcx> {
    pub section: &'a str,
    pub offset: u64,
    pub insn: String,
    pub stack_size: u64,
    pub frame_limit: u64,
    #[primary_span]
    pub span: Span,
    pub instance: Instance<'tcx>,
}

pub fn stack_size_check<'tcx, 'obj>(cx: &AnalysisCtxt<'tcx>, file: &File<'obj>) {
    let lint_cfg = cx.lint_level_at_node(STACK_FRAME_TOO_LARGE, CRATE_HIR_ID);
    // Given inlining and cross-crate monomorphization happening, it does not make
    // a lot of sense to define this lint on anywhere except codegen unit level. So
    // just take levels from the crate root.
    let level = match lint_cfg.level {
        // Don't run any of the checks if the lint is allowed.
        // This is one of the more expensive checks.
        //
        // NOTE: `expect` is actually not supported as this check is too late.
        // But we need to match it so treat like `allow` anyway.
        rustc_lint::Level::Allow | rustc_lint::Level::Expect => return,
        rustc_lint::Level::Warn => Level::Warning,
        rustc_lint::Level::ForceWarn => Level::ForceWarning,
        rustc_lint::Level::Deny | rustc_lint::Level::Forbid => Level::Error,
    };

    // Obtain the stack size limit.
    // Ideally we support `#![klint::stack_frame_size_limit = 4096]`, but this is not yet stable
    // (custom_inner_attributes).
    // Instead, we find via `CONFIG_FRAME_WARN` cfg.
    let frame_limit_sym = cx
        .sess
        .config
        .iter()
        .copied()
        .find(|&(k, v)| k == crate::symbol::CONFIG_FRAME_WARN && v.is_some())
        .map(|(_, v)| v.unwrap())
        .unwrap_or(sym::empty);
    let frame_limit = if frame_limit_sym.is_empty() {
        cx.dcx().emit_warn(StackFrameLimitMissing {
            span: lint_cfg.src.span(),
            default: 2048,
        });
        2048
    } else if let Ok(v) = frame_limit_sym.as_str().parse() {
        v
    } else {
        cx.dcx().emit_err(StackFrameLimitInvalid {
            span: lint_cfg.src.span(),
            setting: frame_limit_sym,
        });
        return;
    };

    // Currently only x64 is supported for this lint.
    if file.architecture() != Architecture::X86_64 {
        return;
    }

    for section in file.sections() {
        // Only check text sections.
        if !matches!(section.kind(), SectionKind::Text) {
            continue;
        }

        let data = section.uncompressed_data().unwrap();
        let decoder = Decoder::with_ip(64, &data, 0, DecoderOptions::NONE);

        let mut linted = FxHashSet::default();
        for insn in decoder {
            if insn.mnemonic() == Mnemonic::Sub
                && insn.op0_kind() == OpKind::Register
                && insn.op0_register() == Register::RSP
                && let Ok(stack_size) = insn.try_immediate(1)
            {
                if stack_size < frame_limit {
                    continue;
                }

                let offset = insn.ip();

                let Some((symbol, _)) =
                    super::find_symbol_from_section_offset(file, &section, offset)
                else {
                    continue;
                };

                let Some(MonoItem::Fn(instance)) = cx.symbol_name_to_mono(symbol) else {
                    continue;
                };

                if !linted.insert(instance) {
                    continue;
                }

                let diag: Diag<'_, ()> = StackFrameTooLarge {
                    section: section.name().unwrap(),
                    offset,
                    insn: insn.to_string(),
                    stack_size,
                    frame_limit,
                    span: cx.def_span(instance.def_id()),
                    instance,
                }
                .into_diag(cx.dcx(), level);
                diag.emit();
            }
        }
    }
}
