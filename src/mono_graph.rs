// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit as hir_visit;
use rustc_hir::{Body, Expr, HirId};
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt, TypeckResults};
use rustc_span::{Span, Spanned};

use crate::monomorphize_collector::{MonoItemCollectionStrategy, collect_crate_mono_items};

pub(crate) type CallableTargets = FxHashSet<LocalDefId>;
pub(crate) type IndirectCallsiteMap = FxHashMap<HirId, CallableTargets>;
pub(crate) type IndirectCandidates = FxHashMap<LocalDefId, IndirectCallsiteMap>;

pub struct InstanceUseGraph<'tcx> {
    pub forward: FxHashMap<Instance<'tcx>, Vec<Spanned<Instance<'tcx>>>>,
    pub backward: FxHashMap<Instance<'tcx>, Vec<Spanned<Instance<'tcx>>>>,
}

fn mono_item_instance<'tcx>(tcx: TyCtxt<'tcx>, item: MonoItem<'tcx>) -> Option<Instance<'tcx>> {
    match item {
        MonoItem::Static(def_id) => Some(Instance::mono(tcx, def_id)),
        MonoItem::Fn(instance) => Some(instance),
        _ => None,
    }
}

pub fn collect_instance_use_graph<'tcx>(
    tcx: TyCtxt<'tcx>,
    strategy: MonoItemCollectionStrategy,
) -> InstanceUseGraph<'tcx> {
    let (mono_items, access_map) = collect_crate_mono_items(tcx, strategy);

    let mut forward = FxHashMap::default();
    let mut backward = FxHashMap::<Instance<'tcx>, Vec<Spanned<Instance<'tcx>>>>::default();

    let _ = mono_items;

    access_map.for_each_item_and_its_used_items(|accessor, accessees| {
        let Some(accessor) = mono_item_instance(tcx, accessor) else {
            return;
        };

        let fwd_list = forward
            .entry(accessor)
            .or_insert_with(|| Vec::with_capacity(accessees.len()));
        let mut accessor_span = None;

        for accessee in accessees {
            let Some(accessee_node) = mono_item_instance(tcx, accessee.node) else {
                continue;
            };

            // For const-evaluated items, they're collected from CTFE alloc, which does not have
            // span information. Synthesize one with the accessor.
            let span = if accessee.span.is_dummy() {
                *accessor_span.get_or_insert_with(|| tcx.def_span(accessor.def_id()))
            } else {
                accessee.span
            };

            fwd_list.push(Spanned {
                node: accessee_node,
                span,
            });
            backward.entry(accessee_node).or_default().push(Spanned {
                node: accessor,
                span,
            });
        }
    });

    InstanceUseGraph { forward, backward }
}

#[derive(Clone, Copy)]
struct CallsiteSpan {
    hir_id: HirId,
    span: Span,
    trait_method: Option<DefId>,
}

struct CallsiteCollector<'a, 'tcx> {
    typeck: &'a TypeckResults<'tcx>,
    callsites: Vec<CallsiteSpan>,
}

impl<'tcx> hir_visit::Visitor<'tcx> for CallsiteCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            rustc_hir::ExprKind::Call(..) => {
                self.callsites.push(CallsiteSpan {
                    hir_id: expr.hir_id,
                    span: expr.span,
                    trait_method: None,
                });
            }
            rustc_hir::ExprKind::MethodCall(..) => {
                self.callsites.push(CallsiteSpan {
                    hir_id: expr.hir_id,
                    span: expr.span,
                    trait_method: self.typeck.type_dependent_def_id(expr.hir_id),
                });
            }
            _ => {}
        }
        hir_visit::walk_expr(self, expr);
    }
}

/// Map a mono-level use span back to the source call expression that owns it. Exact matches are
/// preferred; otherwise choose the smallest enclosing call expression.
fn resolve_callsite_hir_id(callsites: &[CallsiteSpan], span: Span) -> Option<HirId> {
    let mut best = None;
    let mut best_width = u32::MAX;

    for callsite in callsites {
        if callsite.span == span {
            return Some(callsite.hir_id);
        }
        // MIR spans for indirect uses can point at a sub-expression; pick the narrowest enclosing
        // source call expression so the analysis can key everything by `HirId`.
        if callsite.span.lo() <= span.hi() && span.lo() <= callsite.span.hi() {
            let width = callsite.span.hi().0 - callsite.span.lo().0;
            if width < best_width {
                best = Some(callsite.hir_id);
                best_width = width;
            }
        }
    }

    best
}

/// Check whether a local impl method is the concrete implementation of the given trait method.
/// This is used to recover dyn-dispatch callsites from mono edges that point at impl methods.
fn impl_matches_trait_method(tcx: TyCtxt<'_>, candidate: LocalDefId, trait_method: DefId) -> bool {
    let Some(trait_local_def_id) = trait_method.as_local() else {
        return false;
    };
    let trait_def_id = tcx.parent(trait_local_def_id.into());
    let impl_def_id = tcx.parent(candidate.into()).expect_local();
    let rustc_hir::ItemKind::Impl(impl_) = &tcx.hir_expect_item(impl_def_id).kind else {
        return false;
    };
    let Some(of_trait) = impl_.of_trait else {
        return false;
    };

    tcx.item_name(candidate.to_def_id()) == tcx.item_name(trait_method)
        && matches!(
            of_trait.trait_ref.path.res,
            Res::Def(DefKind::Trait, impl_trait_def_id) if impl_trait_def_id == trait_def_id
        )
}

/// Some vtable-related mono edges do not point at the eventual method-call expression directly.
/// When that happens, match the impl method back to a source method call using trait identity.
fn resolve_trait_method_callsite_hir_id(
    tcx: TyCtxt<'_>,
    callsites: &[CallsiteSpan],
    span: Span,
    callee: LocalDefId,
) -> Option<HirId> {
    let mut best = None;
    let mut best_width = u32::MAX;

    for callsite in callsites {
        let Some(trait_method) = callsite.trait_method else {
            continue;
        };
        if !impl_matches_trait_method(tcx, callee, trait_method) {
            continue;
        }
        // Vtable-related mono uses may point at the trait-object construction site instead of the
        // eventual method call. Match them back to the source method call by trait/method identity.
        if callsite.span.lo() <= span.hi() && span.lo() <= callsite.span.hi() {
            let width = callsite.span.hi().0 - callsite.span.lo().0;
            if width < best_width {
                best = Some(callsite.hir_id);
                best_width = width;
            }
        }
    }

    best
}

/// Precompute indirect-call candidates once from the monomorphized use graph and key them by
/// source `HirId`, so HIR-based analyses can stay purely callsite-based and parameter-sensitive.
pub(crate) fn collect_indirect_candidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    bodies: &FxHashMap<LocalDefId, &'tcx Body<'tcx>>,
    body_owners: &[LocalDefId],
) -> IndirectCandidates {
    let graph = collect_instance_use_graph(tcx, MonoItemCollectionStrategy::Eager);
    let body_owners: FxHashSet<_> = body_owners.iter().copied().collect();
    let mut callsites = FxHashMap::<LocalDefId, Vec<CallsiteSpan>>::default();
    let mut candidates = IndirectCandidates::default();

    for (&def_id, &body) in bodies {
        if !body_owners.contains(&def_id) {
            continue;
        }
        let mut collector = CallsiteCollector {
            typeck: tcx.typeck(def_id),
            callsites: Vec::new(),
        };
        hir_visit::Visitor::visit_body(&mut collector, body);
        callsites.insert(def_id, collector.callsites);
    }

    for (caller_instance, callees) in &graph.forward {
        let Some(caller_def_id) = caller_instance.def_id().as_local() else {
            continue;
        };
        if !body_owners.contains(&caller_def_id) {
            continue;
        }

        let Some(caller_callsites) = callsites.get(&caller_def_id) else {
            continue;
        };
        let entry = candidates.entry(caller_def_id).or_default();
        for callee in callees {
            let Some(callee_def_id) = callee.node.def_id().as_local() else {
                continue;
            };
            if matches!(tcx.def_kind(callee_def_id), DefKind::Fn | DefKind::AssocFn) {
                // Resolve each mono edge to the source call expression once up front so the actual
                // propagation logic can stay purely callsite-based.
                let callsite_hir_id = resolve_callsite_hir_id(caller_callsites, callee.span)
                    .or_else(|| {
                        resolve_trait_method_callsite_hir_id(
                            tcx,
                            caller_callsites,
                            callee.span,
                            callee_def_id,
                        )
                    });
                let Some(callsite_hir_id) = callsite_hir_id else {
                    continue;
                };
                entry
                    .entry(callsite_hir_id)
                    .or_default()
                    .insert(callee_def_id);
            }
        }
    }

    candidates
}
