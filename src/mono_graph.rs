// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::mono::MonoItem;
use rustc_middle::ty::{Instance, TyCtxt};
use rustc_span::Spanned;

use crate::monomorphize_collector::{MonoItemCollectionStrategy, collect_crate_mono_items};

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
