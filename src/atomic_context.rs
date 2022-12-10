use rustc_hir::Constness;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, InternalSubsts, ParamEnv, TyCtxt};
use rustc_session::{declare_tool_lint, impl_lint_pass};

use crate::ctxt::AnalysisCtxt;
use crate::preempt_count::ExpectationRange;

// A description of how atomic context analysis works.
//
// This analysis can be treated as checking the preemption count, except that the check is
// performed in compile-time and the checking is not disabled when compiling an non-preemptible
// kernel.
//
// We assign all functions two properties, one is the current preemption count that it expects,
// and another is the adjustment to the preemption count that it will make. For example, the majority
// of functions would have an adjustment of zero, and either makes no expectation to the preemption
// count or requires it to be zero. Taking a spinlock would have an adjustment of 1, and releasing a
// spinlock would have an adjustment of -1.
//
// In the ideal world all of these properties can be inferred from the source code, however it obviously
// is not practical. The difficulty (apart from some complex control flow) arise from:
// * Rust calls into C functions
// * C calls into Rust functions
// * Indirect function calls
// * Generic functions
// * Recursion
//
// Generic functions are tricky because it makes it impossible for us to assign the properties to a
// generic function. For example, in the following code
// ```
// fn foo<T, F: FnOnce() -> T>(f: F) -> T {
//     f()
// }
// ```
// the property of `foo` depends on `F`. If `F` takes a spinlock, e.g. `let guard = foo(|| spinlock.lock())`,
// then `foo` will have an adjustment of 1. But `F` could well be a no-op function and thus `foo` should
// have an adjustment of 0. One way around this would be to work with monomorphized function only, but that
// can require a lot of redundant checking since most functions should have a fixed context property regardless
// of the type parameters. The solution to the generic function would be to try infer the properties of a function
// without generic parameters substituted, and then if the check fails or encountered a type parameter (like `F`
// in the example above), we would bail out and try to re-check the function with substituted type parameters.
//
// The first three categories are more fundamental, because the indirection or FFI makes us unable to infer
// properties in the compile-time. We would therefore have to make some assumptions: all functions are considered
// to make no adjustments to the preemption count, and all functions have no expectations on the preemption count.
// If the functions do not satisfy the expectation, then escape hatch or manual annotation would be required.
// This assumption also means that when a function pointer is *created*, it must also satisfy the assumption.
// Similarly, as using traits with dynamic dispatch is also indirection, we would require explicit markings on
// trait method signatures.
//
// Now finally, recursion. If we want to properly handle recursion, then we are effectively going to find a fixed
// point globally in a call graph. This is not very practical, so we would instead require explicit markings on
// these recursive functions, and if unmarked, assume these functions to make no adjustments to the preemption
// count and have no expectations on the preemption count.

#[derive(Clone, Copy, PartialEq, Eq, Debug, Encodable, Decodable)]
pub struct FunctionContextProperty {
    /// Range of preemption count that the function expects.
    ///
    /// Since the preemption count is a non-negative integer, the lower bound is just represented using a `u32`
    /// and "no expectation" is represented with 0; the upper bound is represented using an `Option<u32>`, with
    /// `None` representing "no expectation". The upper bound is exclusive so `(0, Some(0))` represents an
    /// unsatisfiable condition.
    pub expectation: ExpectationRange,
    pub adjustment: i32,
}

impl Default for FunctionContextProperty {
    fn default() -> Self {
        FunctionContextProperty {
            expectation: ExpectationRange::top(),
            adjustment: 0,
        }
    }
}

declare_tool_lint! {
    pub klint::ATOMIC_CONTEXT,
    Deny,
    ""
}

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn ffi_property(&self, instance: Instance<'tcx>) -> FunctionContextProperty {
        let symbol = self.symbol_name(instance).name;

        // Skip LLVM intrinsics
        if symbol.starts_with("llvm.") {
            return Default::default();
        }

        match symbol {
            // Interfacing between libcore and panic runtime
            "rust_begin_unwind" => Default::default(),
            // Basic string operations depended by libcore.
            "memcmp" => Default::default(),

            // Memory allocations glues depended by liballoc.
            // Allocation functions may sleep.
            "__rust_alloc" | "__rust_alloc_zeroed" | "__rust_realloc" |
            "__rg_alloc" | "__rg_alloc_zeroed" | "__rg_realloc" => FunctionContextProperty {
                expectation: ExpectationRange::single_value(0),
                adjustment: 0,
            },

            // Deallocation function will not sleep.
            "__rust_dealloc" | "__rg_dealloc" => Default::default(),

            "spin_lock" => FunctionContextProperty {
                expectation: ExpectationRange::top(),
                adjustment: 1,
            },
            "spin_unlock" => FunctionContextProperty {
                expectation: ExpectationRange { lo: 1, hi: None },
                adjustment: -1,
            },
            "__cant_sleep" => FunctionContextProperty {
                expectation: ExpectationRange { lo: 1, hi: None },
                adjustment: 0,
            },
            "__might_sleep" | "msleep" => FunctionContextProperty {
                expectation: ExpectationRange::single_value(0),
                adjustment: 0,
            },
            _ => {
                warn!("Unable to determine property for FFI function `{}`", symbol);

                // Other functions, assume no context change for now.
                FunctionContextProperty {
                    expectation: ExpectationRange::top(),
                    adjustment: 0,
                }
            }
        }
    }
}

pub struct AtomicContext<'tcx> {
    cx: AnalysisCtxt<'tcx>,
}

impl<'tcx> AtomicContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            cx: AnalysisCtxt::new(tcx),
        }
    }
}

impl_lint_pass!(AtomicContext<'_> => [ATOMIC_CONTEXT]);

impl<'tcx> LateLintPass<'tcx> for AtomicContext<'tcx> {
    fn check_crate(&mut self, _: &LateContext<'tcx>) {
        // Do this before hand to ensure that errors, if any, are nicely sorted.
        for &def_id in self.cx.mir_keys(()) {
            let _ = self.cx.preemption_count_annotation(def_id.to_def_id());
        }
    }

    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: rustc_hir::intravisit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx rustc_hir::Body<'tcx>,
        _: rustc_span::Span,
        _hir_id: rustc_hir::HirId,
    ) {
        let def_id = cx.tcx.hir().body_owner_def_id(body.id());

        // Building MIR for `fn`s with unsatisfiable preds results in ICE.
        if crate::util::fn_has_unsatisfiable_preds(cx, def_id.to_def_id()) {
            return;
        }

        let identity = cx.tcx.erase_regions(InternalSubsts::identity_for_item(
            self.cx.tcx,
            def_id.into(),
        ));
        let instance = Instance::new(def_id.into(), identity);
        let param_and_instance = self
            .cx
            .param_env_reveal_all_normalized(def_id)
            .with_constness(Constness::NotConst)
            .and(instance);
        let _ = self.cx.instance_adjustment(param_and_instance);
        let _ = self.cx.instance_expectation(param_and_instance);
    }

    fn check_crate_post(&mut self, cx: &LateContext<'tcx>) {
        let mono_items = super::monomorphize_collector::collect_crate_mono_items(
            cx.tcx,
            crate::monomorphize_collector::MonoItemCollectionMode::Eager,
        )
        .0;

        for mono_item in mono_items {
            if let MonoItem::Fn(instance) = mono_item {
                let param_and_instance = ParamEnv::reveal_all().and(instance);
                self.cx
                    .instance_adjustment(param_and_instance)
                    .expect("monomorphized function should not be too generic");
                self.cx
                    .instance_expectation(param_and_instance)
                    .expect("monomorphized function should not be too generic");
            }
        }

        self.cx.encode_mir();

        for &def_id in self.cx.mir_keys(()) {
            let annotation = self.cx.preemption_count_annotation(def_id.to_def_id());
            self.cx
                .sql_store::<crate::preempt_count::annotation::preemption_count_annotation>(
                    def_id.to_def_id(),
                    annotation,
                );
        }
    }
}
