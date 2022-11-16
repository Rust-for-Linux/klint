use std::cell::RefCell;
use std::path::PathBuf;

use rusqlite::Connection;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir;
use rustc_middle::ty::{Instance, TyCtxt};

use crate::atomic_context::{FunctionContextProperty, PreemptionCountRange};

pub struct AnalysisCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub sql_conn: Connection,

    pub eval_stack: RefCell<Vec<Instance<'tcx>>>,

    pub analysis_mir: RefCell<FxHashMap<DefId, &'tcx mir::Body<'tcx>>>,
    pub preemption_count_annotation:
        RefCell<FxHashMap<LocalDefId, (Option<i32>, Option<PreemptionCountRange>)>>,
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

fn klint_home() -> PathBuf {
    let mut klint_dir = home::home_dir().unwrap();
    klint_dir.push(".klint");
    std::fs::create_dir_all(&klint_dir).unwrap();
    klint_dir
}

impl Drop for AnalysisCtxt<'_> {
    fn drop(&mut self) {
        self.sql_conn.execute("commit", ()).unwrap();
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let mut klint_dir = klint_home();
        klint_dir.push("db.sqlite3");

        let mut conn = Connection::open(&klint_dir).unwrap();

        // Check the schema version matches the current version
        let mut schema_ver = 0;
        conn.pragma_query(None, "user_version", |r| {
            schema_ver = r.get::<_, u32>(0)?;
            Ok(())
        })
        .unwrap();

        // Delete and recreate the database if it uses an old schema.
        if schema_ver != 0 && schema_ver != SCHEMA_VERSION {
            info!("Schema version mismatch, purging database");
            drop(conn);
            std::fs::remove_file(&klint_dir).unwrap();
            conn = Connection::open(&klint_dir).unwrap();
        }

        if schema_ver != SCHEMA_VERSION {
            info!("Creating database schema");
            conn.execute_batch(include_str!("mir/schema.sql")).unwrap();
            conn.execute_batch(include_str!("schema.sql")).unwrap();
            conn.pragma_update(None, "user_version", &SCHEMA_VERSION)
                .unwrap();
        }

        conn.execute("begin", ()).unwrap();

        Self {
            tcx,
            sql_conn: conn,
            eval_stack: Default::default(),
            analysis_mir: Default::default(),
            preemption_count_annotation: Default::default(),
            function_context_property: Default::default(),
        }
    }
}
