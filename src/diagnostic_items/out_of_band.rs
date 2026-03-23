//! Out-of-band attributes attached without source code changes.

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::diagnostic_items::DiagnosticItems;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;

pub fn infer_missing_items<'tcx>(tcx: TyCtxt<'tcx>, items: &mut DiagnosticItems) {
    if !items.name_to_id.contains_key(&crate::symbol::build_error)
        && let Some(def_id) = infer_build_error_diagnostic_item(tcx)
    {
        super::collect_item(tcx, items, crate::symbol::build_error, def_id);
    }

    if !items.name_to_id.contains_key(&crate::symbol::build_assert)
        && let Some(def_id) = infer_build_assert_diagnostic_item(tcx)
    {
        super::collect_item(tcx, items, crate::symbol::build_assert, def_id);
    }

    if !items.name_to_id.contains_key(&crate::symbol::c_str)
        && let Some(def_id) = infer_c_str_diagnostic_item(tcx)
    {
        super::collect_item(tcx, items, crate::symbol::c_str, def_id);
    }
}

pub fn infer_build_error_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    for exported in tcx.exported_non_generic_symbols(LOCAL_CRATE) {
        if let ExportedSymbol::NonGeneric(def_id) = exported.0
            && exported.0.symbol_name_for_local_instance(tcx).name == "rust_build_error"
        {
            return Some(def_id);
        }
    }

    None
}

fn infer_local_macro_diagnostic_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    expected_path: &str,
) -> Option<DefId> {
    let mut matches = tcx
        .hir_crate_items(())
        .owners()
        .map(|owner| owner.to_def_id())
        .filter(|&def_id| {
            matches!(tcx.def_kind(def_id), DefKind::Macro(_))
                && tcx.def_path_str(def_id) == expected_path
        });

    let def_id = matches.next()?;
    matches.next().is_none().then_some(def_id)
}

pub fn infer_build_assert_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    let name = tcx.crate_name(LOCAL_CRATE);

    if name != crate::symbol::kernel {
        return None;
    }

    infer_local_macro_diagnostic_item(tcx, "kernel::prelude::build_assert")
}

pub fn infer_c_str_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    let name = tcx.crate_name(LOCAL_CRATE);

    if name != crate::symbol::kernel {
        return None;
    }

    infer_local_macro_diagnostic_item(tcx, "kernel::c_str")
}
