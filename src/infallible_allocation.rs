// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::FxHashSet;
use rustc_errors::{Diag, DiagCtxtHandle, Diagnostic, Level};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::ty::Instance;
use rustc_session::{declare_lint_pass, declare_tool_lint};
use rustc_span::sym;

use crate::mono_graph::collect_instance_use_graph;
use crate::monomorphize_collector::MonoItemCollectionStrategy;

declare_tool_lint! {
    pub klint::INFALLIBLE_ALLOCATION,
    Warn,
    ""
}

declare_lint_pass!(InfallibleAllocation => [INFALLIBLE_ALLOCATION]);

struct ClosureDiag<F: FnOnce(&mut Diag<'_, ()>)>(F);

impl<'a, F: FnOnce(&mut Diag<'_, ()>)> Diagnostic<'a, ()> for ClosureDiag<F> {
    fn into_diag(self, dcx: DiagCtxtHandle<'a>, level: Level) -> Diag<'a, ()> {
        let mut lint = Diag::new(dcx, level, "");
        (self.0)(&mut lint);
        lint
    }
}

fn is_generic_fn<'tcx>(instance: Instance<'tcx>) -> bool {
    instance.args.non_erasable_generics().next().is_some()
}

impl<'tcx> LateLintPass<'tcx> for InfallibleAllocation {
    fn check_crate(&mut self, cx: &LateContext<'tcx>) {
        let graph = collect_instance_use_graph(cx.tcx, MonoItemCollectionStrategy::Eager);
        let forward = &graph.forward;
        let backward = &graph.backward;

        // Find all fallible functions
        let mut visited = FxHashSet::default();

        for accessee in backward.keys() {
            let name = cx.tcx.def_path_str(accessee.def_id());

            // Anything (directly) called by assume_fallible is considered to be fallible.
            if name.contains("assume_fallible") {
                visited.insert(*accessee);
                for accessor in forward.get(accessee).unwrap_or(&Vec::new()) {
                    visited.insert(accessor.node);
                }
                continue;
            }

            match name.as_str() {
                // These are fallible allocation functions that return null ptr on failure.
                "alloc::alloc::__rust_alloc"
                | "alloc::alloc::__rust_alloc_zeroed"
                | "alloc::alloc::__rust_realloc"
                | "alloc::alloc::__rust_dealloc"
                // Fallible allocation function
                | "alloc::string::String::try_reserve"
                | "alloc::string::String::try_reserve_exact" => {
                    visited.insert(*accessee);
                }
                _ => (),
            }
        }

        let mut infallible = FxHashSet::default();
        let mut work_queue = Vec::new();
        for accessee in backward.keys() {
            // Only go-through non-local-copy items.
            // This allows us to not to be concerned about `len()`, `is_empty()`,
            // because they are all inlineable.
            if forward.contains_key(accessee) {
                continue;
            }

            if cx.tcx.crate_name(accessee.def_id().krate) == sym::alloc {
                // If this item originates from alloc crate, mark it as infallible.
                // Add item to the allowlist above if there are false positives.
                work_queue.push(*accessee);
            }
        }

        // Propagate infallible property.
        while let Some(work_item) = work_queue.pop() {
            if visited.contains(&work_item) {
                continue;
            }

            infallible.insert(work_item);
            visited.insert(work_item);

            // Stop at local items to prevent over-linting
            if work_item.def_id().is_local() {
                continue;
            }

            for accessor in backward.get(&work_item).unwrap_or(&Vec::new()) {
                work_queue.push(accessor.node);
            }
        }

        for (accessor, accessees) in forward.iter() {
            // Don't report on non-local items
            if !accessor.def_id().is_local() {
                continue;
            }

            // Fast path
            if !infallible.contains(accessor) {
                continue;
            }

            for item in accessees {
                let accessee = item.node;

                if !accessee.def_id().is_local() && infallible.contains(&accessee) {
                    let is_generic = is_generic_fn(*accessor);
                    let generic_note = if is_generic {
                        format!(
                            " when the caller is monomorphized as `{}`",
                            cx.tcx
                                .def_path_str_with_args(accessor.def_id(), accessor.args)
                        )
                    } else {
                        String::new()
                    };

                    let accessee_path = cx
                        .tcx
                        .def_path_str_with_args(accessee.def_id(), accessee.args);

                    cx.emit_span_lint(
                        INFALLIBLE_ALLOCATION,
                        item.span,
                        ClosureDiag(|diag| {
                            diag.primary_message(format!(
                                "`{}` can perform infallible allocation{}",
                                accessee_path, generic_note
                            ));
                            // For generic functions try to display a stacktrace until a non-generic one.
                            let mut caller = *accessor;
                            let mut visited = FxHashSet::default();
                            visited.insert(*accessor);
                            visited.insert(accessee);
                            while is_generic_fn(caller) {
                                let spanned_caller = match backward
                                    .get(&caller)
                                    .map(|x| &**x)
                                    .unwrap_or(&[])
                                    .iter()
                                    .find(|x| !visited.contains(&x.node))
                                {
                                    Some(v) => *v,
                                    None => break,
                                };
                                caller = spanned_caller.node;
                                visited.insert(caller);

                                diag.span_note(
                                    spanned_caller.span,
                                    format!(
                                        "which is called from `{}`",
                                        cx.tcx.def_path_str_with_args(caller.def_id(), caller.args)
                                    ),
                                );
                            }

                            // Generate some help messages for why the function is determined to be infallible.
                            let mut msg: &str = &format!(
                                "`{}` is determined to be infallible because it",
                                accessee_path
                            );
                            let mut callee = accessee;
                            loop {
                                let callee_callee = match forward
                                    .get(&callee)
                                    .map(|x| &**x)
                                    .unwrap_or(&[])
                                    .iter()
                                    .find(|x| {
                                        infallible.contains(&x.node) && !visited.contains(&x.node)
                                    }) {
                                    Some(v) => v,
                                    None => break,
                                };
                                callee = callee_callee.node;
                                visited.insert(callee);

                                diag.span_note(
                                    callee_callee.span,
                                    format!(
                                        "{} calls into `{}`",
                                        msg,
                                        cx.tcx.def_path_str_with_args(callee.def_id(), callee.args)
                                    ),
                                );
                                msg = "which";
                            }

                            diag.note(format!("{} may call alloc_error_handler", msg));
                        }),
                    );
                }
            }
        }
    }
}
