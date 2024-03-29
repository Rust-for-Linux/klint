#![feature(rustc_private)]
#![feature(lazy_cell)]
#![feature(min_specialization)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![feature(never_type)]
#![warn(rustc::internal)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_log;
#[macro_use]
extern crate rustc_macros;
#[macro_use]
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_monomorphize;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

#[macro_use]
extern crate tracing;

use std::process::ExitCode;
use std::sync::atomic::AtomicPtr;

use rustc_driver::Callbacks;
use rustc_interface::interface::Config;
use rustc_session::config::ErrorOutputType;
use rustc_session::EarlyDiagCtxt;
use std::sync::atomic::Ordering;

#[macro_use]
mod ctxt;

mod atomic_context;
mod attribute;
mod infallible_allocation;
mod mir;
mod monomorphize_collector;
mod preempt_count;
mod serde;
mod symbol;
mod util;

rustc_session::declare_tool_lint! {
    pub klint::INCORRECT_ATTRIBUTE,
    Forbid,
    "Incorrect usage of klint attributes"
}

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_, provider| {
            static ORIGINAL_OPTIMIZED_MIR: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

            ORIGINAL_OPTIMIZED_MIR.store(provider.optimized_mir as *mut (), Ordering::Relaxed);
            provider.optimized_mir = |tcx, def_id| {
                // Calling `optimized_mir` will steal the result of query `mir_drops_elaborated_and_const_checked`,
                // so hijack `optimized_mir` to run `analysis_mir` first.

                // Skip `analysis_mir` call if this is a constructor, since it will be delegated back to
                // `optimized_mir` for building ADT constructor shim.
                if !tcx.is_constructor(def_id.to_def_id()) {
                    crate::mir::local_analysis_mir(tcx, def_id);
                }

                let ptr = ORIGINAL_OPTIMIZED_MIR.load(Ordering::Relaxed);
                assert!(!ptr.is_null());
                let original_optimized_mir =
                    unsafe { std::mem::transmute::<*mut (), fn(_, _) -> _>(ptr) };
                original_optimized_mir(tcx, def_id)
            };
        });
        config.register_lints = Some(Box::new(move |_, lint_store| {
            lint_store.register_lints(&[&INCORRECT_ATTRIBUTE]);
            lint_store.register_lints(&[&infallible_allocation::INFALLIBLE_ALLOCATION]);
            lint_store.register_lints(&[&atomic_context::ATOMIC_CONTEXT]);
            // lint_store
            //     .register_late_pass(|_| Box::new(infallible_allocation::InfallibleAllocation));
            lint_store.register_late_pass(|tcx| Box::new(atomic_context::AtomicContext::new(tcx)));
        }));
    }
}

fn main() -> ExitCode {
    let handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_logger(&handler, rustc_log::LoggerConfig::from_env("KLINT_LOG"));
    let args: Vec<_> = std::env::args().collect();

    match rustc_driver::RunCompiler::new(&args, &mut MyCallbacks).run() {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
