use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rustc_hir::{Item, ItemKind, UseKind};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{Symbol, sym};

use crate::ctxt::AnalysisCtxt;

declare_tool_lint! {
    //// The `not_using_prelude` lint detects when an item is available via prelude,
    /// but is imported from other paths instead.
    pub klint::NOT_USING_PRELUDE,
    Warn,
    "item available via prelude but imported from elsewhere"
}

pub struct NotUsingPrelude<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
}

impl_lint_pass!(NotUsingPrelude<'_> => [NOT_USING_PRELUDE]);

#[derive(Diagnostic)]
#[diag("this item is available via prelude")]
#[help("import with `{$crate_name}::prelude::*` instead")]
struct NotUsingPreludeLint {
    pub crate_name: Symbol,
}

impl<'tcx> LateLintPass<'tcx> for NotUsingPrelude<'tcx> {
    fn check_item(&mut self, cx: &LateContext<'tcx>, item: &'tcx Item<'tcx>) {
        let ItemKind::Use(path, UseKind::Single(import_name)) = item.kind else {
            return;
        };

        // Manual prelude import. This is possible the user trying to solve conflicts or performing a rename.
        if path.segments.iter().any(|x| x.ident.name == sym::prelude) {
            return;
        }

        // If the import is renamed, that is likely intentional.
        if path.segments.last().unwrap().ident != import_name {
            return;
        }

        let prelude = self.cx.prelude_def_ids();
        // A `use` may bring in things from multiple namespaces. To avoid false positives, we
        // only issue warnings if *all* items imported such way are already available through prelude.
        if !path
            .res
            .present_items()
            .all(|x| x.opt_def_id().is_some_and(|x| prelude.contains_key(&x)))
        {
            return;
        }

        // Ad-hoc lint suppression based on crate name.
        // This is to ensure that doctest for kernel crate does not need to use `kernel::prelude`.
        let local_crate_name = self.cx.crate_name(LOCAL_CRATE);
        if local_crate_name.as_str().contains("doctest") {
            return;
        }

        let imported_def_id = path.res.present_items().next().unwrap().def_id();
        let cnum = prelude.get(&imported_def_id).copied().unwrap();
        let crate_name = self.cx.crate_name(cnum);

        cx.emit_span_lint(
            NOT_USING_PRELUDE,
            item.span,
            NotUsingPreludeLint { crate_name },
        );
    }
}

memoize!(
    /// Collect all prelude def_ids visible from the current crate.
    pub fn prelude_def_ids<'tcx>(cx: &AnalysisCtxt<'tcx>) -> Arc<FxHashMap<DefId, CrateNum>> {
        let mut defs = FxHashMap::default();

        for cnum in cx
            .crates(())
            .iter()
            .copied()
            .filter(|cnum| cx.extern_crate(*cnum).is_some_and(|e| e.is_direct()))
        {
            // For core/std, the prelude is of format crate::prelude::version, which we don't
            // handle for now.
            // let crate_name = cx.crate_name(cnum);
            // if crate_name == sym::core || crate_name == sym::std {
            //     continue;
            // }

            // For all direct dependencies, check if `::prelude` is defined.
            let Some(prelude) = cx.module_children(cnum.as_def_id()).iter().find(|c| {
                c.ident.name == sym::prelude && matches!(c.res, Res::Def(DefKind::Mod, _))
            }) else {
                continue;
            };
            let prelude = prelude.res.def_id();

            // Obtain all public items in the prelude.
            defs.extend(
                cx.module_children(prelude)
                    .iter()
                    .filter(|c| c.vis.is_public())
                    .map(|c| (c.res.def_id(), cnum)),
            );
        }

        Arc::new(defs)
    }
);
