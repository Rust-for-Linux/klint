use rustc_hir::def_id::{CrateNum, DefId, DefIndex};

use crate::attribute::PreemptionCount;
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    fn preemption_count_annotation_fallback(&self, def_id: DefId) -> PreemptionCount {
        match self.crate_name(def_id.krate).as_str() {
            // Happens in a test environment where build-std is not enabled.
            "core" | "alloc" | "std" => (),
            _ => {
                warn!(
                    "Unable to retrieve preemption count annotation of non-local function {:?}",
                    def_id
                );
            }
        }
        Default::default()
    }
}

memoize!(
    pub fn preemption_count_annotation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        def_id: DefId,
    ) -> PreemptionCount {
        let Some(local_def_id) = def_id.as_local() else {
            if let Some(v) = cx.sql_load::<preemption_count_annotation>(def_id) {
                return v;
            }
            return cx.preemption_count_annotation_fallback(def_id);
        };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.klint_attributes(hir_id).iter() {
            match attr {
                crate::attribute::KlintAttribute::PreemptionCount(pc) => {
                    return *pc;
                }
                _ => (),
            }
        }

        Default::default()
    }
);

impl crate::ctxt::PersistentQuery for preemption_count_annotation {
    type LocalKey<'tcx> = DefIndex;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key.krate, key.index)
    }
}

memoize!(
    pub fn should_report_preempt_count<'tcx>(cx: &AnalysisCtxt<'tcx>, def_id: DefId) -> bool {
        let Some(local_def_id) = def_id.as_local() else { return false };

        let hir_id = cx.hir().local_def_id_to_hir_id(local_def_id);
        for attr in cx.klint_attributes(hir_id).iter() {
            match attr {
                crate::attribute::KlintAttribute::ReportPreeptionCount => return true,
                _ => (),
            }
        }

        false
    }
);
