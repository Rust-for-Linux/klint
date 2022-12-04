#![feature(rustc_private)]
#![feature(once_cell)]
#![feature(min_specialization)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![warn(rustc::internal)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_ast;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
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
use std::sync::atomic::Ordering;

#[macro_use]
mod ctxt;

mod atomic_context;
mod attribute;
mod infallible_allocation;
mod mir;
mod monomorphize_collector;
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
        config.override_queries = Some(|_, provider, _| {
            static ORIGINAL_OPTIMIZED_MIR: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

            ORIGINAL_OPTIMIZED_MIR.store(provider.optimized_mir as *mut (), Ordering::Relaxed);
            provider.optimized_mir = |tcx, def_id| {
                // Calling `optimized_mir` will steal the result of query `mir_drops_elaborated_and_const_checked`,
                // so hijack `optimized_mir` to run `analysis_mir` first.

                // Skip `analysis_mir` call if this is a constructor, since it will be delegated back to
                // `optimized_mir` for building ADT constructor shim.
                if !tcx.is_constructor(def_id) {
                    crate::mir::local_analysis_mir(tcx, def_id.expect_local());
                }

                let ptr = ORIGINAL_OPTIMIZED_MIR.load(Ordering::Relaxed);
                assert!(!ptr.is_null());
                let original_optimized_mir =
                    unsafe { std::mem::transmute::<*mut (), fn(_, _) -> _>(ptr) };
                original_optimized_mir(tcx, def_id)
            };
        });
        config.register_lints = Some(Box::new(move |sess, lint_store| {
            // Skip checks for proc-macro crates.
            if sess.crate_types().contains(&rustc_session::config::CrateType::ProcMacro) {
                return;
            }

            lint_store.register_lints(&[&INCORRECT_ATTRIBUTE]);
            lint_store.register_lints(&[&infallible_allocation::INFALLIBLE_ALLOCATION]);
            lint_store.register_lints(&[&atomic_context::ATOMIC_CONTEXT]);
            // lint_store
            //     .register_late_pass(|_| Box::new(infallible_allocation::InfallibleAllocation));
            lint_store.register_late_pass(|tcx| Box::new(atomic_context::AtomicContext::new(tcx)));
        }));
    }
}

fn probe_sysroot() -> String {
    std::process::Command::new("rustc")
        .arg("+beta-2022-11-01")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|x| x.trim().to_owned())
        .expect("failed to probe rust sysroot")
}

fn main() -> ExitCode {
    rustc_driver::init_env_logger("KLINT_LOG");
    let mut args: Vec<_> = std::env::args().collect();

    if !args.iter().any(|x| x == "--sysroot") {
        args.push("--sysroot".to_owned());
        args.push(probe_sysroot());
    }

    match rustc_driver::RunCompiler::new(&args, &mut MyCallbacks).run() {
        Ok(_) => ExitCode::SUCCESS,
        Err(_) => ExitCode::FAILURE,
    }
}
