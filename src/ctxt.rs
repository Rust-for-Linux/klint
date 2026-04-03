// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::any::Any;
use std::marker::PhantomData;
use std::sync::Arc;

use rusqlite::Connection;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::sync::{DynSend, DynSync, Lock, RwLock};
use rustc_hir::def_id::{CrateNum, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_serialize::{Decodable, Encodable};
use rustc_session::config::OutputType;
use rustc_span::{DUMMY_SP, Span};

use crate::diagnostic::use_stack::UseSite;
use crate::utils::anymap::AnyMap;

pub(crate) trait Query: 'static {
    const NAME: &'static str;

    type Key<'tcx>: DynSend + DynSync;
    type Value<'tcx>: DynSend + DynSync;
}

pub(crate) trait QueryValueDecodable: Query {
    fn encode_value<'tcx>(value: &Self::Value<'tcx>, cx: &mut crate::serde::EncodeContext<'tcx>);

    fn decode_value<'a, 'tcx>(cx: &mut crate::serde::DecodeContext<'a, 'tcx>) -> Self::Value<'tcx>;
}

impl<Q: Query> QueryValueDecodable for Q
where
    for<'a, 'tcx> Q::Value<'tcx>: Encodable<crate::serde::EncodeContext<'tcx>>
        + Decodable<crate::serde::DecodeContext<'a, 'tcx>>,
{
    fn encode_value<'tcx>(value: &Self::Value<'tcx>, cx: &mut crate::serde::EncodeContext<'tcx>) {
        Encodable::encode(value, cx)
    }

    fn decode_value<'a, 'tcx>(cx: &mut crate::serde::DecodeContext<'a, 'tcx>) -> Self::Value<'tcx> {
        Decodable::decode(cx)
    }
}

pub(crate) trait PersistentQuery: QueryValueDecodable {
    type LocalKey<'tcx>: Encodable<crate::serde::EncodeContext<'tcx>>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>);
}

pub struct AnalysisCtxt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub local_conn: Lock<Connection>,
    pub sql_conn: RwLock<FxHashMap<CrateNum, Option<Arc<Lock<Connection>>>>>,
    pub metadata_finalized: Lock<bool>,

    pub call_stack: RwLock<Vec<UseSite<'tcx>>>,
    pub query_cache: RwLock<AnyMap<dyn Any + DynSend + DynSync>>,
}

// Everything in `AnalysisCtxt` is either `DynSend/DynSync` or `Send/Sync`, but since there're no relation between two right now compiler cannot infer this.
unsafe impl<'tcx> DynSend for AnalysisCtxt<'tcx> {}
unsafe impl<'tcx> DynSync for AnalysisCtxt<'tcx> {}

impl<'tcx> std::ops::Deref for AnalysisCtxt<'tcx> {
    type Target = TyCtxt<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.tcx
    }
}

macro_rules! memoize {
    ($(#[$attr:meta])* $vis:vis fn $name:ident<$tcx: lifetime>($cx:ident: $($_: ty)? $(, $key:ident: $key_ty:ty)* $(,)?) -> $ret: ty { $($body: tt)* }) => {
        #[allow(non_camel_case_types)]
        $vis struct $name;

        impl crate::ctxt::Query for $name {
            const NAME: &'static str = core::stringify!($name);

            #[allow(unused_parens)]
            type Key<$tcx> = ($($key_ty),*);
            type Value<$tcx> = $ret;
        }

        impl<'tcx> crate::ctxt::AnalysisCtxt<'tcx> {
            $vis fn $name(&self, $($key: $key_ty,)*) -> $ret {
                $(#[$attr])*
                fn $name<$tcx>($cx: &crate::ctxt::AnalysisCtxt<$tcx>, $($key: $key_ty),*) -> $ret {
                    $($body)*
                }
                let pack = ($($key),*);
                let cache = self.query_cache::<$name>();
                {
                    let guard = cache.borrow();
                    if let Some(val) = guard.get(&pack) {
                        return <$ret>::clone(val);
                    }
                }
                let val = $name(self, $($key),*);
                let mut guard = cache.borrow_mut();
                guard.insert(pack, <$ret>::clone(&val));
                val
            }
        }
    }
}

const SCHEMA_VERSION: u32 = 2;

impl Drop for AnalysisCtxt<'_> {
    fn drop(&mut self) {
        if !*self.metadata_finalized.get_mut() {
            self.local_conn.lock().execute("commit", ()).unwrap();
        }
    }
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub(crate) fn finalize_metadata(&self) {
        let mut finalized = self.metadata_finalized.lock();
        if !*finalized {
            self.local_conn.lock().execute("commit", ()).unwrap();
            *finalized = true;
        }
    }

    pub(crate) fn query_cache<Q: Query>(
        &self,
    ) -> Arc<RwLock<FxHashMap<Q::Key<'tcx>, Q::Value<'tcx>>>> {
        let mut guard = self.query_cache.borrow_mut();
        let cache = guard
            .entry()
            .or_insert_with(|| {
                let cache = Arc::new(RwLock::new(
                    FxHashMap::<Q::Key<'static>, Q::Value<'static>>::default(),
                ));
                (PhantomData::<fn() -> Q>, cache)
            })
            .1
            .clone();
        // Everything stored inside query_cache is conceptually `'tcx`, but due to limitation
        // of `Any` we hack around the lifetime.
        unsafe { std::mem::transmute(cache) }
    }

    pub(crate) fn sql_connection(&self, cnum: CrateNum) -> Option<Arc<Lock<Connection>>> {
        if let Some(v) = self.sql_conn.borrow().get(&cnum) {
            return v.clone();
        }

        let mut guard = self.sql_conn.borrow_mut();
        if let Some(v) = guard.get(&cnum) {
            return v.clone();
        }

        let mut result = None;
        let mut sysroot = false;
        for path in self.tcx.crate_extern_paths(cnum) {
            if path.starts_with(&self.sess.opts.sysroot.default) {
                sysroot = true;
                continue;
            }

            let klint_path = path.with_extension("klint.rmeta");
            if !klint_path.exists() {
                continue;
            }
            let Ok(conn) = Connection::open_with_flags(
                &klint_path,
                rusqlite::OpenFlags::SQLITE_OPEN_READ_ONLY,
            ) else {
                warn!(
                    "failed to open klint metadata {}, ignoring",
                    klint_path.display()
                );
                continue;
            };

            // Check the schema version matches the current version
            let mut schema_ver = 0;
            let Ok(()) = conn.pragma_query(None, "user_version", |r| {
                schema_ver = r.get::<_, u32>(0)?;
                Ok(())
            }) else {
                warn!(
                    "failed to read schema version from klint metadata {}, ignoring",
                    klint_path.display()
                );
                continue;
            };

            if schema_ver != SCHEMA_VERSION {
                info!(
                    "schema version of {} mismatch, ignoring",
                    klint_path.display()
                );
                continue;
            }

            result = Some(Arc::new(Lock::new(conn)));
            break;
        }

        // If we're running with pre-built sysroot, none of the these will be available to klint.
        // In such cases, stop emitting too much warnings.
        if result.is_none() && !sysroot {
            let name = self.tcx.crate_name(cnum);
            warn!("no klint metadata found for crate {}", name);
        }

        guard.insert(cnum, result.clone());
        result
    }

    pub(crate) fn sql_create_table<Q: Query>(&self) {
        self.local_conn
            .lock()
            .execute_batch(&format!(
                "CREATE TABLE {} (key BLOB PRIMARY KEY, value BLOB);",
                Q::NAME
            ))
            .unwrap();
    }

    pub(crate) fn sql_load_with_span<Q: PersistentQuery>(
        &self,
        key: Q::Key<'tcx>,
        span: Span,
    ) -> Option<Q::Value<'tcx>> {
        let (cnum, local_key) = Q::into_crate_and_local(key);

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        local_key.encode(&mut encode_ctx);
        let encoded = encode_ctx.finish();

        let value_encoded: Vec<u8> = match self.sql_connection(cnum)?.lock().query_row(
            &format!("SELECT value FROM {} WHERE key = ?", Q::NAME),
            rusqlite::params![encoded],
            |row| row.get(0),
        ) {
            Ok(value) => Some(value),
            Err(rusqlite::Error::QueryReturnedNoRows) => None,
            Err(err) => {
                warn!(
                    "failed to load persistent query {} from crate {}, ignoring: {}",
                    Q::NAME,
                    self.tcx.crate_name(cnum),
                    err
                );
                None
            }
        }?;
        let mut decode_ctx = crate::serde::DecodeContext::new(self.tcx, &value_encoded, span);
        let value = Q::decode_value(&mut decode_ctx);
        Some(value)
    }

    pub(crate) fn sql_load<Q: PersistentQuery>(&self, key: Q::Key<'tcx>) -> Option<Q::Value<'tcx>> {
        self.sql_load_with_span::<Q>(key, DUMMY_SP)
    }

    pub(crate) fn sql_store_with_span<Q: PersistentQuery>(
        &self,
        key: Q::Key<'tcx>,
        value: Q::Value<'tcx>,
        span: Span,
    ) {
        let (cnum, local_key) = Q::into_crate_and_local(key);
        assert!(cnum == LOCAL_CRATE);

        // Avoid serialising anything if there are errors (to prevent errors from being encoded
        // which can cause panic).
        if self.dcx().has_errors().is_some() {
            return;
        }

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        local_key.encode(&mut encode_ctx);
        let key_encoded = encode_ctx.finish();

        let mut encode_ctx = crate::serde::EncodeContext::new(self.tcx, span);
        Q::encode_value(&value, &mut encode_ctx);
        let value_encoded = encode_ctx.finish();

        self.local_conn
            .lock()
            .execute(
                &format!(
                    "INSERT OR REPLACE INTO {} (key, value) VALUES (?, ?)",
                    Q::NAME
                ),
                rusqlite::params![key_encoded, value_encoded],
            )
            .unwrap();
    }

    pub(crate) fn sql_store<Q: PersistentQuery>(&self, key: Q::Key<'tcx>, value: Q::Value<'tcx>) {
        self.sql_store_with_span::<Q>(key, value, DUMMY_SP);
    }

    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        let conn = if tcx.needs_metadata() {
            let output_filenames = tcx.output_filenames(());

            // FIXME: This makes sure that we can find the correct name for .so files
            // used for proc macros. But this is quite hacky.
            let preferred_output = if output_filenames
                .outputs
                .contains_explicit_name(&OutputType::Exe)
            {
                OutputType::Exe
            } else {
                OutputType::Metadata
            };

            let output_path = output_filenames.path(preferred_output);
            let output_path = output_path.as_path();

            let klint_out = output_path.with_extension("klint.rmeta");
            let _ = std::fs::remove_file(&klint_out);
            Connection::open(&klint_out).unwrap()
        } else {
            Connection::open_in_memory().unwrap()
        };

        // Check the schema version matches the current version
        let mut schema_ver = 0;
        conn.pragma_query(None, "user_version", |r| {
            schema_ver = r.get::<_, u32>(0)?;
            Ok(())
        })
        .unwrap();
        conn.execute("begin immediate", ()).unwrap();
        conn.pragma_update(None, "user_version", SCHEMA_VERSION)
            .unwrap();

        let ret = Self {
            tcx,
            local_conn: Lock::new(conn),
            sql_conn: Default::default(),
            metadata_finalized: Lock::new(false),
            call_stack: Default::default(),
            query_cache: Default::default(),
        };
        ret.sql_create_table::<crate::preempt_count::annotation::preemption_count_annotation>();
        ret.sql_create_table::<crate::preempt_count::annotation::drop_preemption_count_annotation>(
        );
        ret.sql_create_table::<crate::preempt_count::adjustment::instance_adjustment>();
        ret.sql_create_table::<crate::preempt_count::expectation::instance_expectation>();
        ret.sql_create_table::<crate::build_assert_not_inlined::instance_build_assert_summary>();
        ret.sql_create_table::<crate::mir::analysis_mir>();
        ret.sql_create_table::<crate::diagnostic_items::klint_diagnostic_items>();
        ret
    }
}
