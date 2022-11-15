use std::cell::RefCell;
use std::path::PathBuf;

use rusqlite::{Connection, OptionalExtension};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::TyCtxt;
use rustc_serialize::{Decodable, Encodable};

pub struct AnalysisCtxt<'tcx> {
    tcx: TyCtxt<'tcx>,
    mir_cache: RefCell<FxHashMap<DefId, &'tcx mir::Body<'tcx>>>,
    sql_conn: Connection,
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
            conn.execute_batch(include_str!("schema.sql")).unwrap();
            conn.pragma_update(None, "user_version", &SCHEMA_VERSION)
                .unwrap();
        }

        conn.execute("begin", ()).unwrap();

        Self {
            tcx,
            sql_conn: conn,
            mir_cache: Default::default(),
        }
    }

    #[instrument(skip(self, mir))]
    fn store_mir(&self, def_id: DefId, mir: &mir::Body<'tcx>) {
        let mut enc = crate::serde::EncodeContext::new(self.tcx);
        mir.encode(&mut enc);
        let enc_result = enc.finish();
        self.sql_conn
            .execute(
                "INSERT OR REPLACE INTO mir (stable_crate_id, local_def_id, mir) VALUES (?, ?, ?)",
                rusqlite::params![
                    self.tcx.stable_crate_id(def_id.krate).to_u64() as i64,
                    def_id.index.as_u32(),
                    enc_result,
                ],
            )
            .unwrap();
    }

    #[instrument(skip(self))]
    fn load_mir(&self, def_id: DefId) -> Option<&'tcx mir::Body<'tcx>> {
        let mir_enc: Vec<u8> = self
            .sql_conn
            .query_row(
                "SELECT mir FROM mir WHERE stable_crate_id = ? AND local_def_id = ?",
                rusqlite::params![
                    self.tcx.stable_crate_id(def_id.krate).to_u64() as i64,
                    def_id.index.as_u32()
                ],
                |row| row.get(0),
            )
            .optional()
            .unwrap()?;
        let _ = self.tcx.optimized_mir(def_id);
        let mut dec = crate::serde::DecodeContext::new(self.tcx, &mir_enc);
        let mir = <&mir::Body<'tcx>>::decode(&mut dec);
        Some(mir)
    }

    pub fn analysis_mir(&self, def_id: DefId) -> Option<&'tcx mir::Body<'tcx>> {
        if let Some(mir) = self.mir_cache.borrow().get(&def_id) {
            return Some(*mir);
        }

        if def_id.is_local() {
            let mir = crate::mir::analysis_mir(self.tcx, def_id);
            self.mir_cache.borrow_mut().insert(def_id, mir);
            Some(mir)
        } else if let Some(mir) = self.load_mir(def_id) {
            self.mir_cache.borrow_mut().insert(def_id, mir);
            Some(mir)
        } else if self.tcx.is_mir_available(def_id) {
            let mir = self.tcx.optimized_mir(def_id);
            self.mir_cache.borrow_mut().insert(def_id, mir);
            Some(mir)
        } else {
            None
        }
    }

    /// Save all MIRs defined in the current crate to the database.
    pub fn encode_mir(&self) {
        let tcx = self.tcx;
        for &def_id in tcx.mir_keys(()) {
            // Use the same logic as rustc use to determine if the MIR is needed for
            // downstream crates.
            let should_encode = match tcx.def_kind(def_id) {
                DefKind::Ctor(_, _) | DefKind::Generator => true,
                DefKind::AssocFn | DefKind::Fn | DefKind::Closure => {
                    let generics = tcx.generics_of(def_id);
                    let needs_inline = generics.requires_monomorphization(tcx)
                        || tcx.codegen_fn_attrs(def_id).requests_inline();
                    needs_inline
                }
                _ => false,
            };

            if should_encode {
                let mir = self.analysis_mir(def_id.into()).unwrap();
                self.store_mir(def_id.into(), mir);
            }
        }
    }
}
