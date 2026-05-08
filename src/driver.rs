//! Contains hacks that changes the flow of compiler.

use std::any::Any;
use std::sync::{Arc, LazyLock, Mutex};

use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CompiledModules, CrateInfo, TargetConfig};
use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_data_structures::sync::{DynSend, DynSync};
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::Config;
use rustc_interface::interface::Compiler;
use rustc_metadata::EncodedMetadata;
use rustc_metadata::creader::MetadataLoaderDyn;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_session::config::{OutputFilenames, OutputType, PrintRequest};
use rustc_session::{EarlyDiagCtxt, Session};

pub trait CallbacksExt: Callbacks + Send + 'static {
    type ExtCtxt<'tcx>: DynSend + DynSync;

    /// Create a new context that extends `TyCtxt`.
    fn ext_cx<'tcx>(&mut self, _tcx: TyCtxt<'tcx>) -> Self::ExtCtxt<'tcx>;

    fn after_codegen<'tcx>(&mut self, _cx: &'tcx Self::ExtCtxt<'tcx>) {}
}

/// Mapping from `TyCtxt<'tcx>` to `Ctxt<'tcx>`.
static TCX_EXT_MAP: LazyLock<Mutex<FxHashMap<usize, Box<dyn Any + Send + Sync>>>> =
    LazyLock::new(|| Mutex::new(FxHashMap::default()));

struct CallbackWrapper<C> {
    callback: Arc<Mutex<C>>,
}

impl<C: CallbacksExt> Callbacks for CallbackWrapper<C> {
    fn config(&mut self, config: &mut Config) {
        self.callback.lock().unwrap().config(config);

        let make_codegen_backend = config.make_codegen_backend.take().unwrap_or_else(|| {
            Box::new(|sess| {
                let early_dcx = EarlyDiagCtxt::new(sess.opts.error_format);
                rustc_interface::util::get_codegen_backend(
                    &early_dcx,
                    &sess.opts.sysroot,
                    sess.opts.unstable_opts.codegen_backend.as_deref(),
                    &sess.target,
                )
            })
        });

        // By default, Rust starts codegen with a TyCtxt, but then leaves `TyCtxt` and join
        // codegen. This is useful to reduce memory consumption while building, but also means that
        // we will no longer have access to `TyCtxt` when we want to lint based on the generated
        // binary. We therefore hook the backend so that the whole process is done with `TyCtxt`
        // still present.
        let callback_clone = self.callback.clone();
        config.make_codegen_backend = Some(Box::new(|sess| {
            let codegen_backend = make_codegen_backend(sess);
            Box::new(BackendWrapper {
                backend: codegen_backend,
                callback: callback_clone,
            })
        }));
    }

    fn after_crate_root_parsing(
        &mut self,
        compiler: &Compiler,
        krate: &mut rustc_ast::Crate,
    ) -> Compilation {
        self.callback
            .lock()
            .unwrap()
            .after_crate_root_parsing(compiler, krate)
    }

    fn after_expansion<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut callback = self.callback.lock().unwrap();

        // This is the first opportunity that we've got a `tcx`.
        // Register the extension here.
        let cx = Box::new(callback.ext_cx(tcx));

        // SAFETY: this is a lifetime extension needed to store it into our hashmap.
        // This can be obtained by `cx` function below, which would give it a lifetime of `'tcx`.
        //
        // We use a hook to destroy this before `TyCtxt<'tcx>` is gone in `codegen_crate`. That is
        // the very last function to execute before `TyCtxt::finish` (assuming that no providers hook into it...)
        let cx_lifetime_ext: Box<C::ExtCtxt<'static>> = unsafe { std::mem::transmute(cx) };
        let cx_dyn: Box<dyn Any> = cx_lifetime_ext;
        // SAFETY: horrible trick to make this actually `Sync`. However this will not actually be used
        // in another thread unless `TyCtxt` is `Sync` and `DynSync` is indeed `Sync`.
        let cx_sync: Box<dyn Any + Send + Sync> = unsafe { std::mem::transmute(cx_dyn) };
        let tcx_addr = *tcx as *const _ as usize;
        TCX_EXT_MAP.lock().unwrap().insert(tcx_addr, cx_sync);

        callback.after_expansion(compiler, tcx)
    }

    fn after_analysis<'tcx>(&mut self, compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let ret = self.callback.lock().unwrap().after_analysis(compiler, tcx);

        if tcx.sess.opts.unstable_opts.no_codegen || !tcx.sess.opts.output_types.should_codegen() {
            // Normally we destory `cx` in `codegen_crate`. However when codegen is not happening,
            // that will not be invoked, and this is our last change to do cleanups.
            let tcx_addr = *tcx as *const _ as usize;
            let cx = TCX_EXT_MAP.lock().unwrap().remove(&tcx_addr).unwrap();
            assert!(cx.is::<C::ExtCtxt<'static>>());
            // SAFETY: we just check the (type-erased) type matches.
            drop(unsafe { Box::from_raw(Box::into_raw(cx) as *mut C::ExtCtxt<'tcx>) });
        }

        ret
    }
}

pub struct BackendWrapper<C> {
    backend: Box<dyn CodegenBackend>,
    callback: Arc<Mutex<C>>,
}

impl<C: CallbacksExt> CodegenBackend for BackendWrapper<C> {
    fn name(&self) -> &'static str {
        self.backend.name()
    }

    fn target_cpu(&self, sess: &Session) -> String {
        self.backend.target_cpu(sess)
    }

    fn codegen_crate<'tcx>(&self, tcx: TyCtxt<'tcx>) -> Box<dyn Any> {
        let ongoing_codegen = self.backend.codegen_crate(tcx);
        let outputs = tcx.output_filenames(());

        // HACK: ZFS contains a bug that if std::fs::copy overwrites an existing file,
        // the data read back might be corrupted. Workaround this by removing the file beforehand.
        // https://github.com/openzfs/zfs/issues/18412
        // Remove once the fix has landed in all supported releases of ZFS.
        if outputs.outputs.contains_key(&OutputType::Object) {
            let file = outputs.path(OutputType::Object);
            if !file.is_stdout() {
                _ = std::fs::remove_file(file.as_path());
            }
        }

        let crate_info = CrateInfo::new(tcx, self.backend.target_cpu(tcx.sess));

        let (cg, work_map) =
            self.backend
                .join_codegen(ongoing_codegen, tcx.sess, outputs, &crate_info);

        self.callback.lock().unwrap().after_codegen(cx::<C>(tcx));

        // `tcx` is going to destroyed. Let's get back the copy.
        let tcx_addr = *tcx as *const _ as usize;
        let cx = TCX_EXT_MAP.lock().unwrap().remove(&tcx_addr).unwrap();
        assert!(cx.is::<C::ExtCtxt<'static>>());
        // SAFETY: we just check the (type-erased) type matches.
        drop(unsafe { Box::from_raw(Box::into_raw(cx) as *mut C::ExtCtxt<'tcx>) });

        Box::new((cg, work_map))
    }

    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        _sess: &Session,
        _outputs: &OutputFilenames,
        _crate_info: &CrateInfo,
    ) -> (CompiledModules, FxIndexMap<WorkProductId, WorkProduct>) {
        *ongoing_codegen.downcast().unwrap()
    }

    fn init(&self, sess: &Session) {
        self.backend.init(sess)
    }

    fn print(&self, req: &PrintRequest, out: &mut String, sess: &Session) {
        self.backend.print(req, out, sess)
    }

    fn target_config(&self, sess: &Session) -> TargetConfig {
        self.backend.target_config(sess)
    }

    fn print_passes(&self) {
        self.backend.print_passes()
    }

    fn print_version(&self) {
        self.backend.print_version()
    }

    fn metadata_loader(&self) -> Box<MetadataLoaderDyn> {
        self.backend.metadata_loader()
    }

    fn provide(&self, providers: &mut Providers) {
        self.backend.provide(providers)
    }

    fn link(
        &self,
        sess: &Session,
        compiled_modules: CompiledModules,
        crate_info: CrateInfo,
        metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        self.backend
            .link(sess, compiled_modules, crate_info, metadata, outputs)
    }
}

pub fn run_compiler<C: CallbacksExt>(at_args: &[String], callback: C) {
    rustc_driver::run_compiler(
        at_args,
        &mut CallbackWrapper {
            callback: Arc::new(Mutex::new(callback)),
        },
    );
}

/// Obtain an extended context from `TyCtxt`.
pub fn cx<'tcx, C: CallbacksExt>(tcx: TyCtxt<'tcx>) -> &'tcx C::ExtCtxt<'tcx> {
    let tcx_addr = *tcx as *const _ as usize;
    let guard = TCX_EXT_MAP.lock().unwrap();
    let cx = guard.get(&tcx_addr).unwrap();
    assert!(cx.is::<C::ExtCtxt<'static>>());
    // SAFETY: we have checked that the type actually matches.
    unsafe { &*(&raw const **cx as *const C::ExtCtxt<'tcx>) }
}

#[macro_export]
macro_rules! hook_query {
    ($provider: expr => |$tcx: ident, $query: ident, $original: ident| $content: block) => {{
        static ORIGINAL: std::sync::atomic::AtomicPtr<()> =
            std::sync::atomic::AtomicPtr::new(std::ptr::null_mut());

        ORIGINAL.store($provider as *mut (), std::sync::atomic::Ordering::Relaxed);
        $provider = |$tcx, $query| {
            let ptr = ORIGINAL.load(Ordering::Relaxed);
            let $original = unsafe { std::mem::transmute::<*mut (), fn(_, _) -> _>(ptr) };
            // Insert a type check to ensure that the signature is indeed matching.
            if false {
                return $original($tcx, $query);
            }
            $content
        };
    }};
}
