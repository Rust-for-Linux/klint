// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(never_type)]
#![feature(try_blocks)]
// Used in monomorphize collector
#![feature(impl_trait_in_assoc_type)]
#![feature(once_cell_get_mut)]
// Used in symbol.rs
#![feature(macro_metavar_expr)]
#![feature(unsize)]
#![warn(rustc::internal)]

#[macro_use]
extern crate rustc_macros;
#[macro_use]
extern crate rustc_middle;
#[macro_use]
extern crate tracing;

extern crate itertools;
extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_codegen_ssa;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lint;
extern crate rustc_log;
extern crate rustc_metadata;
extern crate rustc_mir_dataflow;
extern crate rustc_monomorphize;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate thiserror;

use rustc_driver::Callbacks;
use rustc_interface::interface::Config;
use rustc_middle::ty::TyCtxt;
use rustc_session::EarlyDiagCtxt;
use rustc_session::config::{DebugInfo, ErrorOutputType, OutputType};
use std::sync::atomic::Ordering;

use crate::ctxt::AnalysisCtxt;

#[macro_use]
mod ctxt;

mod atomic_context;
mod attribute;
mod binary_analysis;
mod diagnostic;
mod diagnostic_items;
mod driver;
mod hir_lints;
mod infallible_allocation;
mod lattice;
mod mir;
mod mono_graph;
mod monomorphize_collector;
mod preempt_count;
mod serde;
mod symbol;
mod util;
mod utils;

struct MyCallbacks;

impl Callbacks for MyCallbacks {
    fn config(&mut self, config: &mut Config) {
        match config.opts.debuginfo {
            DebugInfo::LineDirectivesOnly | DebugInfo::LineTablesOnly => {
                // If we only have line tables, then we cannot reliable reconstruct call graphs from DWARF,
                // as the DWARF info lacks the linkage name attributes, so we do not know the generics info
                // on functions.
                let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
                early_dcx.early_warn("klint does not work with `-C debuginfo=line-tables-only`. Use `-C debuginfo=limited` instead.");
            }
            _ => (),
        }

        config.extra_symbols = crate::symbol::EXTRA_SYMBOLS.to_owned();

        config.override_queries = Some(|_, provider| {
            // Calling `optimized_mir` will steal the result of query `mir_drops_elaborated_and_const_checked`,
            // so hijack `optimized_mir` to run `analysis_mir` first.
            hook_query!(provider.queries.optimized_mir => |tcx, local_def_id, original| {
                let def_id = local_def_id.to_def_id();
                // Skip `analysis_mir` call if this is a constructor, since it will be delegated back to
                // `optimized_mir` for building ADT constructor shim.
                if !tcx.is_constructor(def_id) {
                    let cx = crate::driver::cx::<MyCallbacks>(tcx);
                    let _ = cx.analysis_mir(def_id);
                }

                original(tcx, local_def_id)
            });
        });
        config.register_lints = Some(Box::new(move |_, lint_store| {
            lint_store.register_lints(&[
                infallible_allocation::INFALLIBLE_ALLOCATION,
                atomic_context::ATOMIC_CONTEXT,
                binary_analysis::stack_size::STACK_FRAME_TOO_LARGE,
                hir_lints::c_str_literal::C_STR_LITERAL,
                hir_lints::not_using_prelude::NOT_USING_PRELUDE,
            ]);

            lint_store.register_late_pass(|tcx| {
                Box::new(hir_lints::c_str_literal::CStrLiteralLint {
                    cx: driver::cx::<MyCallbacks>(tcx),
                })
            });

            lint_store.register_late_pass(|tcx| {
                Box::new(hir_lints::not_using_prelude::NotUsingPrelude {
                    cx: driver::cx::<MyCallbacks>(tcx),
                })
            });

            // lint_store
            //     .register_late_pass(|_| Box::new(infallible_allocation::InfallibleAllocation));
            lint_store.register_late_pass(|tcx| {
                Box::new(atomic_context::AtomicContext {
                    cx: driver::cx::<MyCallbacks>(tcx),
                })
            });
        }));
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let cx = driver::cx::<MyCallbacks>(tcx);

        // Ensure this query is run at least once, even without diagnostics emission, to
        // catch duplicate item errors.
        let _ = cx.klint_all_diagnostic_items();

        rustc_driver::Compilation::Continue
    }
}

impl driver::CallbacksExt for MyCallbacks {
    type ExtCtxt<'tcx> = AnalysisCtxt<'tcx>;

    fn ext_cx<'tcx>(&mut self, tcx: TyCtxt<'tcx>) -> Self::ExtCtxt<'tcx> {
        AnalysisCtxt::new(tcx)
    }

    fn after_codegen<'tcx>(&mut self, cx: &'tcx AnalysisCtxt<'tcx>) {
        // If compilation fails, do not attempt to perform binary analysis, as
        // binary might not have been generated.
        if cx.dcx().has_errors().is_some() {
            return;
        }

        let outputs = cx.output_filenames(());
        if outputs.outputs.contains_key(&OutputType::Object) {
            let file = outputs.path(OutputType::Object);
            // We cannot retrieve object back from stdout.
            if file.is_stdout() {
                return;
            }
            binary_analysis::binary_analysis(cx, file.as_path());
        }
    }
}

fn main() {
    let early_dcx = EarlyDiagCtxt::new(ErrorOutputType::default());
    rustc_driver::init_logger(&early_dcx, rustc_log::LoggerConfig::from_env("KLINT_LOG"));
    let args: Vec<_> = std::env::args().collect();

    driver::run_compiler(&args, MyCallbacks);
}
