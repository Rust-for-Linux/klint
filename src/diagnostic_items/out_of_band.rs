//! Out-of-band attributes attached without source code changes.

use rustc_attr_ir::diagnostic_items::DiagnosticItems;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CRATE_DEF_ID, DefId, LOCAL_CRATE};
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;

pub fn infer_missing_items<'tcx>(tcx: TyCtxt<'tcx>, items: &mut DiagnosticItems) {
    if !items.name_to_id.contains_key(&crate::symbol::build_error) {
        if let Some(def_id) = infer_build_error_diagnostic_item(tcx) {
            super::collect_item(tcx, items, crate::symbol::build_error, def_id);
        }
    }

    if !items.name_to_id.contains_key(&crate::symbol::c_str) {
        if let Some(def_id) = infer_c_str_diagnostic_item(tcx) {
            super::collect_item(tcx, items, crate::symbol::c_str, def_id);
        }
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

pub fn infer_c_str_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    let name = tcx.crate_name(LOCAL_CRATE);

    if name != crate::symbol::kernel {
        return None;
    }

    let c_str = tcx
        .module_children_local(CRATE_DEF_ID)
        .iter()
        .find(|c| {
            c.ident.name == crate::symbol::c_str && matches!(c.res, Res::Def(DefKind::Macro(_), _))
        })?
        .res
        .def_id();

    Some(c_str)
}
