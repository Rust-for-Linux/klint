// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_hir::def_id::DefId;
use rustc_lint::LateContext;
use rustc_middle::ty::TypeVisitableExt;

pub fn fn_has_unsatisfiable_preds(cx: &LateContext<'_>, did: DefId) -> bool {
    use rustc_trait_selection::traits;
    let clauses = cx
        .tcx
        .clauses_of(did)
        .clauses
        .iter()
        .filter_map(|(c, _)| if c.is_global() { Some(*c) } else { None });
    traits::impossible_clauses(
        cx.tcx,
        traits::elaborate(cx.tcx, clauses).collect::<Vec<_>>(),
    )
}
