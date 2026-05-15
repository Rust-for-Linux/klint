use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::LangItem;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_middle::{mir, ty};
use rustc_span::{BytePos, DUMMY_SP, FileName, RemapPathScopeComponents, Span};

use crate::ctxt::AnalysisCtxt;
use crate::diagnostic::use_stack::UseSiteKind;

memoize!(
    fn mono_items<'tcx>(cx: &AnalysisCtxt<'tcx>) -> Arc<Vec<MonoItem<'tcx>>> {
        let mono_items = crate::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            crate::monomorphize_collector::MonoItemCollectionStrategy::Lazy,
        )
        .0;

        mono_items.into()
    }
);

memoize!(
    fn symbol_name_map<'tcx>(cx: &AnalysisCtxt<'tcx>) -> Arc<FxHashMap<&'tcx str, MonoItem<'tcx>>> {
        let map = cx.mono_items();
        Arc::new(
            map.iter()
                .map(|&item| (item.symbol_name(cx.tcx).name, item))
                .collect(),
        )
    }
);

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn symbol_name_to_mono(&self, name: &str) -> Option<MonoItem<'tcx>> {
        self.symbol_name_map().get(name).copied()
    }
}

pub fn recover_span_from_line_no<'tcx>(
    tcx: TyCtxt<'tcx>,
    location: &super::dwarf::Location,
) -> Option<Span> {
    // Find the file in session's source map.
    let source_map = tcx.sess.source_map();
    let mut found_file = None;
    for file in source_map.files().iter() {
        if let FileName::Real(real) = &file.name {
            if real.path(RemapPathScopeComponents::DEBUGINFO) == location.file {
                found_file = Some(file.clone());
            }
        }
    }

    let Some(found_file) = found_file else {
        return None;
    };

    let range = found_file.line_bounds((location.line as usize).saturating_sub(1));
    Some(Span::with_root_ctxt(
        BytePos(range.start.0 + location.column.saturating_sub(1) as u32),
        // We only have a single column info. A good approximation is to extend to end of line (which is typically the case for function calls).
        BytePos(range.end.0 - 1),
    ))
}

// Compare a recovered span from a compiler-produced span, and determine if they're likely the same source.
pub fn recover_span<'tcx>(recover_span: Span, span: Span) -> bool {
    // Recovered span is produced through debug info. This will undergo the debuginfo collapse process.
    // Before comparing, undergo the same process for `span`.

    let collapsed = rustc_span::hygiene::walk_chain_collapsed(span, DUMMY_SP);

    let range = collapsed.lo()..collapsed.hi();
    range.contains(&recover_span.lo())
}

pub fn recover_fn_call_span<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: Instance<'tcx>,
    callee: &str,
    location: Option<&super::dwarf::Location>,
) -> Option<(Instance<'tcx>, UseSiteKind)> {
    let mir = tcx.instance_mir(caller.def);

    let mut callee_instance = None;
    let mut sites = Vec::new();

    for block in mir.basic_blocks.iter() {
        let terminator = block.terminator();

        // Skip over inlined body. We'll check them from scopes directly.
        if mir.source_scopes[terminator.source_info.scope]
            .inlined
            .is_some()
        {
            continue;
        }

        match terminator.kind {
            mir::TerminatorKind::Call { ref func, .. }
            | mir::TerminatorKind::TailCall { ref func, .. } => {
                let callee_ty = func.ty(mir, tcx);
                let callee_ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(callee_ty),
                );

                let ty::FnDef(def_id, args) = *callee_ty.kind() else {
                    continue;
                };

                let instance = ty::Instance::expect_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    def_id,
                    args,
                    terminator.source_info.span,
                );
                if tcx.symbol_name(instance).name != callee {
                    continue;
                }

                callee_instance = Some(instance);
                sites.push(UseSiteKind::Call(terminator.source_info.span));
            }
            mir::TerminatorKind::Drop { ref place, .. } => {
                let ty = place.ty(mir, tcx).ty;
                let ty = caller.instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    ty::EarlyBinder::bind(ty),
                );

                let instance = Instance::resolve_drop_glue(tcx, ty);
                if tcx.symbol_name(instance).name != callee {
                    continue;
                }

                callee_instance = Some(instance);
                sites.push(UseSiteKind::Drop {
                    drop_span: terminator.source_info.span,
                    place_span: mir.local_decls[place.local].source_info.span,
                });
            }

            // If MIR has an assertion terminator, we should find the corresponding language
            // item and recover from there.
            mir::TerminatorKind::Assert { ref msg, .. } => {
                let lang_item = match **msg {
                    mir::AssertKind::BoundsCheck { .. } => LangItem::PanicBoundsCheck,
                    mir::AssertKind::MisalignedPointerDereference { .. } => {
                        LangItem::PanicMisalignedPointerDereference
                    }
                    _ => msg.panic_function(),
                };

                let def_id = tcx.require_lang_item(lang_item, terminator.source_info.span);
                let instance = Instance::mono(tcx, def_id);
                if tcx.symbol_name(instance).name != callee {
                    continue;
                }

                callee_instance = Some(instance);
                sites.push(UseSiteKind::Other(
                    terminator.source_info.span,
                    "assert".to_owned(),
                ));
            }

            _ => continue,
        };
    }

    // In addition to direct function calls, we should also inspect inlined functions.
    for scope in mir.source_scopes.iter() {
        if scope.inlined_parent_scope.is_none()
            && let Some((instance, span)) = scope.inlined
        {
            let instance = caller.instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(instance),
            );

            if tcx.symbol_name(instance).name != callee {
                continue;
            }

            callee_instance = Some(instance);
            sites.push(UseSiteKind::Call(span));
        }
    }

    let Some(callee_instance) = callee_instance else {
        tracing::error!("{} does not contain call to {}", caller, callee);
        return None;
    };

    // If there's only a single span, then it has to be the correct span.
    if sites.len() == 1 {
        return Some((callee_instance, sites.pop().unwrap()));
    }

    // Otherwise, we need to use the DWARF location information to find the best related span.
    let Some(loc) = &location else {
        tracing::warn!(
            "no way to distinguish {}'s use of {}",
            caller,
            callee_instance
        );
        return Some((callee_instance, sites.pop().unwrap()));
    };

    let Some(recovered_span) = recover_span_from_line_no(tcx, loc) else {
        tracing::warn!(
            "no way to distinguish {}'s use of {}",
            caller,
            callee_instance
        );
        return Some((callee_instance, sites.pop().unwrap()));
    };

    // Now we have a recovered span. Use this span to match spans that we have.
    for site in sites {
        if recover_span(recovered_span, site.span()) {
            return Some((callee_instance, site));
        }
    }

    // No perfect match, just use the recovered span that we have.
    Some((callee_instance, UseSiteKind::Call(recovered_span)))
}
