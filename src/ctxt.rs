use std::cell::RefCell;

use rusqlite::Connection;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::sync::Lrc;
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_middle::mir;
use rustc_middle::ty::{Instance, TyCtxt};

use crate::atomic_context::FunctionContextProperty;

pub struct AnalysisCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub local_conn: Connection,
    pub sql_conn: RefCell<FxHashMap<CrateNum, Option<Lrc<Connection>>>>,

    pub eval_stack: RefCell<Vec<Instance<'tcx>>>,

    pub analysis_mir: RefCell<FxHashMap<DefId, &'tcx mir::Body<'tcx>>>,
    pub preemption_count_annotation:
        RefCell<FxHashMap<DefId, crate::attribute::PreemptionCount>>,
    pub function_context_property:
        RefCell<FxHashMap<Instance<'tcx>, Option<FunctionContextProperty>>>,
}

impl<'tcx> std::ops::Deref for AnalysisCtxt<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

macro_rules! memoize {
    (fn $name:ident<$tcx: lifetime>($cx:ident: $($_: ty)?, $key:ident: $key_ty:ty $(,)?) -> $ret: ty { $($body: tt)* }) => {
        impl<'tcx> crate::ctxt::AnalysisCtxt<'tcx> {
            pub fn $name(&self, key: $key_ty) -> $ret {
                fn inner<$tcx>($cx: &crate::ctxt::AnalysisCtxt<$tcx>, $key: $key_ty) -> $ret {
                    $($body)*
                }

                {
                    let cache = self.$name.borrow();
                    if let Some(val) = cache.get(&key) {
                        return *val;
                    }
                }
                let val = inner(self, key);
                let mut cache = self.$name.borrow_mut();
                cache.insert(key, val);
                val
            }
        }
    }
}

const SCHEMA_VERSION: u32 = 1;

impl Drop for AnalysisCtxt<'_> {
    fn drop(&mut self) {
        self.local_conn.execute("commit", ()).unwrap();
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub(crate) fn sql_connection(&self, cnum: CrateNum) -> Option<Lrc<Connection>> {
        if let Some(v) = self.sql_conn.borrow().get(&cnum) {
            return v.clone();
        }

        let mut guard = self.sql_conn.borrow_mut();
        if let Some(v) = guard.get(&cnum) {
            return v.clone();
        }

        let mut result = None;
        for path in self.tcx.crate_extern_paths(cnum) {
            let Some(ext) = path.extension() else { continue };
            if ext == "rlib" || ext == "rmeta" {
                let klint_path = path.with_extension("klint");
                if !klint_path.exists() {
                    continue;
                }
                let conn = Connection::open_with_flags(
                    &klint_path,
                    rusqlite::OpenFlags::SQLITE_OPEN_READ_ONLY,
                )
                .unwrap();

                // Check the schema version matches the current version
                let mut schema_ver = 0;
                conn.pragma_query(None, "user_version", |r| {
                    schema_ver = r.get::<_, u32>(0)?;
                    Ok(())
                })
                .unwrap();

                if schema_ver != SCHEMA_VERSION {
                    info!(
                        "schema version of {} mismatch, ignoring",
                        klint_path.display()
                    );
                }

                result = Some(Lrc::new(conn));
                break;
            }
        }

        if result.is_none() {
            warn!(
                "no klint metadata found for crate {}",
                self.tcx.crate_name(cnum)
            );
        }

        guard.insert(cnum, result.clone());
        result
    }

    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let output_filenames = tcx.output_filenames(());
        let rmeta_path = rustc_session::output::filename_for_metadata(
            tcx.sess,
            crate_name.as_str(),
            output_filenames,
        );

        // Double check that the rmeta file is .rlib or .rmeta
        let ext = rmeta_path.extension().unwrap();
        assert!(ext == "rlib" || ext == "rmeta");

        let klint_out = rmeta_path.with_extension("klint");
        let _ = std::fs::remove_file(&klint_out);
        let conn = Connection::open(&klint_out).unwrap();

        // Check the schema version matches the current version
        let mut schema_ver = 0;
        conn.pragma_query(None, "user_version", |r| {
            schema_ver = r.get::<_, u32>(0)?;
            Ok(())
        })
        .unwrap();

        conn.execute_batch(include_str!("mir/schema.sql")).unwrap();
        conn.execute_batch(include_str!("schema.sql")).unwrap();
        conn.pragma_update(None, "user_version", &SCHEMA_VERSION)
            .unwrap();
        conn.execute("begin immediate", ()).unwrap();

        Self {
            tcx,
            local_conn: conn,
            sql_conn: Default::default(),
            eval_stack: Default::default(),
            analysis_mir: Default::default(),
            preemption_count_annotation: Default::default(),
            function_context_property: Default::default(),
        }
    }
}
