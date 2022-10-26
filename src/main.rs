#![feature(rustc_private)]
#![warn(rustc::internal)]
#![allow(rustc::potential_query_instability)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_lint;
#[macro_use]
extern crate rustc_middle;
extern crate rustc_monomorphize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;

#[macro_use]
extern crate tracing;

use rustc_driver::Callbacks;
use rustc_interface::interface::Config;

mod infallible_allocation;
mod monomorphize_collector;

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        config.register_lints = Some(Box::new(move |_, lint_store| {
            lint_store.register_lints(&[&infallible_allocation::INFALLIBLE_ALLOCATION]);
            lint_store
                .register_late_pass(|_| Box::new(infallible_allocation::InfallibleAllocation));
        }));
    }
}

fn probe_sysroot() -> String {
    std::process::Command::new("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .ok()
        .and_then(|out| String::from_utf8(out.stdout).ok())
        .map(|x| x.trim().to_owned())
        .expect("failed to probe rust sysroot")
}

fn main() -> rustc_interface::interface::Result<()> {
    let mut args: Vec<_> = std::env::args().collect();

    if !args.iter().any(|x| x == "--sysroot") {
        args.push("--sysroot".to_owned());
        args.push(probe_sysroot());
    }

    rustc_driver::RunCompiler::new(&args, &mut MyCallbacks).run()
}
