//! Out-of-band attributes attached without source code changes.

use rustc_hir::def::DefKind;
use rustc_hir::def::Res;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::diagnostic_items::DiagnosticItems;
use rustc_middle::middle::exported_symbols::ExportedSymbol;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

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
    expected_path: &[PathSegment],
) -> Option<DefId> {
    let (root, rest) = expected_path.split_first()?;
    let PathSegment::Type(root) = root else {
        return None;
    };

    if *root != tcx.crate_name(LOCAL_CRATE) {
        return None;
    }

    lookup_with_local_root(tcx, rest)
}

#[derive(Clone, Copy)]
enum PathSegment {
    Type(Symbol),
    Macro(Symbol),
}

fn lookup_with_local_root<'tcx>(tcx: TyCtxt<'tcx>, path: &[PathSegment]) -> Option<DefId> {
    let (segment, rest) = path.split_first()?;

    let mut matches = tcx.hir_crate_items(()).owners().filter_map(|owner| {
        let def_id = owner.to_def_id();
        if tcx.opt_parent(def_id) != Some(LOCAL_CRATE.as_def_id()) {
            return None;
        }

        match (*segment, tcx.def_kind(def_id)) {
            (PathSegment::Type(expected), DefKind::Mod) if tcx.item_name(def_id) == expected => {
                Some(def_id)
            }
            (PathSegment::Macro(expected), DefKind::Macro(_))
                if tcx.item_name(def_id) == expected =>
            {
                Some(def_id)
            }
            _ => None,
        }
    });

    let def_id = matches.next()?;

    if matches.next().is_some() {
        return None;
    }

    if rest.is_empty() {
        Some(def_id)
    } else {
        lookup_with_base(tcx, def_id, rest)
    }
}

fn lookup_with_base<'tcx>(tcx: TyCtxt<'tcx>, base: DefId, path: &[PathSegment]) -> Option<DefId> {
    let (segment, rest) = path.split_first()?;

    let children = if let Some(local_def_id) = base.as_local() {
        tcx.module_children_local(local_def_id)
    } else {
        tcx.module_children(base)
    };

    let mut matches = children.iter().filter_map(|child| {
        let Res::Def(kind, def_id) = child.res else {
            return None;
        };

        match (*segment, kind, child.ident.name) {
            (PathSegment::Type(expected), DefKind::Mod, actual) if actual == expected => {
                Some(def_id)
            }
            (PathSegment::Macro(expected), DefKind::Macro(_), actual) if actual == expected => {
                Some(def_id)
            }
            _ => None,
        }
    });

    let def_id = matches.next()?;

    if matches.next().is_some() {
        return None;
    }

    if rest.is_empty() {
        Some(def_id)
    } else {
        lookup_with_base(tcx, def_id, rest)
    }
}

pub fn infer_build_assert_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    let name = tcx.crate_name(LOCAL_CRATE);

    if name != crate::symbol::kernel {
        return None;
    }

    infer_local_macro_diagnostic_item(
        tcx,
        &[
            PathSegment::Type(crate::symbol::kernel),
            PathSegment::Type(rustc_span::sym::prelude),
            PathSegment::Macro(crate::symbol::build_assert),
        ],
    )
}

pub fn infer_c_str_diagnostic_item<'tcx>(tcx: TyCtxt<'tcx>) -> Option<DefId> {
    let name = tcx.crate_name(LOCAL_CRATE);

    if name != crate::symbol::kernel {
        return None;
    }

    infer_local_macro_diagnostic_item(
        tcx,
        &[
            PathSegment::Type(crate::symbol::kernel),
            PathSegment::Macro(crate::symbol::c_str),
        ],
    )
}
