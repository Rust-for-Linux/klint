use std::any::{Any, TypeId};
use std::cell::RefCell;

use rusqlite::Connection;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::sync::Lrc;
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_middle::ty::{Instance, TyCtxt};

pub(crate) trait Query: 'static {
    type Key<'tcx>;
    type Value<'tcx>;
}

pub struct AnalysisCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub local_conn: Connection,
    pub sql_conn: RefCell<FxHashMap<CrateNum, Option<Lrc<Connection>>>>,

    pub eval_stack: RefCell<Vec<Instance<'tcx>>>,
    pub query_cache: RefCell<FxHashMap<TypeId, Lrc<dyn Any>>>,
}

impl<'tcx> std::ops::Deref for AnalysisCtxt<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

macro_rules! memoize {
    ($(#[$attr:meta])* fn $name:ident<$tcx: lifetime>($cx:ident: $($_: ty)?, $($key:ident: $key_ty:ty),* $(,)?) -> $ret: ty { $($body: tt)* }) => {
        #[allow(non_camel_case_types)]
        struct $name;

        impl crate::ctxt::Query for $name {
            type Key<$tcx> = ($($key_ty,)*);
            type Value<$tcx> = $ret;
        }

        impl<'tcx> crate::ctxt::AnalysisCtxt<'tcx> {
            pub fn $name(&self, $($key: $key_ty,)*) -> $ret {
                $(#[$attr])*
                fn $name<$tcx>($cx: &crate::ctxt::AnalysisCtxt<$tcx>, $($key: $key_ty),*) -> $ret {
                    $($body)*
                }
                let pack = ($($key,)*);
                let cache = self.query_cache::<$name>();
                {
                    let guard = cache.borrow();
                    if let Some(val) = guard.get(&pack) {
                        return *val;
                    }
                }
                let val = $name(self, $($key)*);
                let mut guard = cache.borrow_mut();
                guard.insert(pack, val);
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
    pub(crate) fn query_cache<Q: Query>(
        &self,
    ) -> Lrc<RefCell<FxHashMap<Q::Key<'tcx>, Q::Value<'tcx>>>> {
        let key = TypeId::of::<Q>();
        let mut guard = self.query_cache.borrow_mut();
        let cache = guard
            .entry(key)
            .or_insert_with(|| {
                let cache = Lrc::new(RefCell::new(
                    FxHashMap::<Q::Key<'static>, Q::Value<'static>>::default(),
                ));
                cache
            })
            .clone()
            .downcast::<RefCell<FxHashMap<Q::Key<'static>, Q::Value<'static>>>>()
            .unwrap();
        // Everything stored inside query_cache is conceptually `'tcx`, but due to limitation
        // of `Any` we hack around the lifetime.
        unsafe { std::mem::transmute(cache) }
    }

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
        let conn;
        if ext == "rlib" || ext == "rmeta" {
            let klint_out = rmeta_path.with_extension("klint");
            let _ = std::fs::remove_file(&klint_out);
            conn = Connection::open(&klint_out).unwrap();
        } else {
            info!("klint called on a binary crate");
            conn = Connection::open_in_memory().unwrap();
        }

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
            query_cache: Default::default(),
        }
    }
}
