mod out_of_band;

use std::sync::Arc;

use rustc_attr_ir::diagnostic_items::DiagnosticItems;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::CRATE_OWNER_ID;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_serialize::{Decodable, Encodable};
use rustc_span::{Span, Symbol};

use crate::ctxt::{AnalysisCtxt, QueryValueDecodable};
use crate::{attribute::KlintAttribute, ctxt::PersistentQuery};

#[derive(Diagnostic)]
#[diag("duplicate klint diagnostic item in crate `{$crate_name}`: `{$name}`")]
struct DuplicateDiagnosticItemInCrate {
    #[primary_span]
    pub duplicate_span: Option<Span>,
    #[note("the klint diagnostic item is first defined here")]
    pub orig_span: Option<Span>,
    #[note("the diagnostic item is first defined in crate `{$orig_crate_name}`")]
    pub different_crates: bool,
    pub crate_name: Symbol,
    pub orig_crate_name: Symbol,
    pub name: Symbol,
}

fn report_duplicate_item(
    tcx: TyCtxt<'_>,
    name: Symbol,
    original_def_id: DefId,
    item_def_id: DefId,
) {
    let orig_span = tcx.hir_span_if_local(original_def_id);
    let duplicate_span = tcx.hir_span_if_local(item_def_id);
    tcx.dcx().emit_err(DuplicateDiagnosticItemInCrate {
        duplicate_span,
        orig_span,
        crate_name: tcx.crate_name(item_def_id.krate),
        orig_crate_name: tcx.crate_name(original_def_id.krate),
        different_crates: (item_def_id.krate != original_def_id.krate),
        name,
    });
}

fn collect_item(tcx: TyCtxt<'_>, items: &mut DiagnosticItems, name: Symbol, item_def_id: DefId) {
    items.id_to_name.insert(item_def_id, name);
    if let Some(original_def_id) = items.name_to_id.insert(name, item_def_id) {
        if original_def_id != item_def_id {
            report_duplicate_item(tcx, name, original_def_id, item_def_id);
        }
    }
}

memoize!(
    pub fn klint_diagnostic_items<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        krate_num: CrateNum,
    ) -> Arc<DiagnosticItems> {
        if krate_num != LOCAL_CRATE {
            return cx
                .sql_load::<klint_diagnostic_items>(krate_num)
                .unwrap_or_default();
        }

        let mut items = DiagnosticItems::default();

        let crate_items = cx.hir_crate_items(());
        for owner in crate_items.owners().chain(std::iter::once(CRATE_OWNER_ID)) {
            for attr in cx.klint_attributes(owner.into()).iter() {
                if let KlintAttribute::DiagnosticItem(name) = *attr {
                    collect_item(cx.tcx, &mut items, name, owner.to_def_id());
                }
            }
        }

        out_of_band::infer_missing_items(cx.tcx, &mut items);

        let ret = Arc::new(items);
        cx.sql_store::<klint_diagnostic_items>(krate_num, ret.clone());
        ret
    }
);

impl QueryValueDecodable for klint_diagnostic_items {
    fn encode_value<'tcx>(value: &Self::Value<'tcx>, cx: &mut crate::serde::EncodeContext<'tcx>) {
        value.name_to_id.encode(cx);
    }

    fn decode_value<'a, 'tcx>(cx: &mut crate::serde::DecodeContext<'a, 'tcx>) -> Self::Value<'tcx> {
        let name_to_id = FxIndexMap::decode(cx);
        let id_to_name = name_to_id.iter().map(|(&name, &id)| (id, name)).collect();
        Arc::new(DiagnosticItems {
            name_to_id,
            id_to_name,
        })
    }
}

impl PersistentQuery for klint_diagnostic_items {
    type LocalKey<'tcx> = ();

    fn into_crate_and_local<'tcx>(key: CrateNum) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key, ())
    }
}

memoize!(
    pub fn klint_all_diagnostic_items<'tcx>(cx: &AnalysisCtxt<'tcx>) -> Arc<DiagnosticItems> {
        let mut items = DiagnosticItems::default();

        for cnum in cx
            .crates(())
            .iter()
            .copied()
            .filter(|cnum| cx.is_user_visible_dep(*cnum))
            .chain(std::iter::once(LOCAL_CRATE))
        {
            for (&name, &def_id) in &cx.klint_diagnostic_items(cnum).name_to_id {
                collect_item(cx.tcx, &mut items, name, def_id);
            }
        }

        Arc::new(items)
    }
);

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn get_klint_diagnostic_item(&self, name: Symbol) -> Option<DefId> {
        self.klint_all_diagnostic_items()
            .name_to_id
            .get(&name)
            .copied()
    }
}
