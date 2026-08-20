// Copyright The Rust Project Developers.
// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

// This module is from rustc_monomorphize/collector.rs, modified so that
// * All uses are collected, including those that should not be codegen-ed locally.
// * `inlines` field is removed from `InliningMap`.
// * Due to the above reasons, `InliningMap` is renamed to `AccessMap`.
// * `Spanned<MonoItem>` is returned in `AccessMap` instead of just `MonoItem`.

use rustc_attr_ir::lang_items::LangItem;
use rustc_data_structures::Limit;
use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_data_structures::sync::{Lock, par_for_each_in};
use rustc_data_structures::unord::UnordSet;
use rustc_hir as hir;
use rustc_hir::attrs::InlineAttr;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, DefIdMap, LocalDefId};
use rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags;
use rustc_middle::mir::interpret::AllocId;
use rustc_middle::mir::interpret::{ErrorHandled, GlobalAlloc, Scalar};
use rustc_middle::mir::visit::Visitor as MirVisitor;
use rustc_middle::mir::{self, Location, MentionedItem, traversal};
use rustc_middle::mono::{CollectionMode, MonoItem};
use rustc_middle::query::TyCtxtAt;
use rustc_middle::ty::adjustment::{CustomCoerceUnsized, PointerCoercion};
use rustc_middle::ty::layout::ValidityRequirement;
use rustc_middle::ty::{
    self, GenericArgs, GenericParamDefKind, Instance, InstanceKind, Ty, TyCtxt, TypeFoldable,
    TypeVisitableExt, Unnormalized, VtblEntry,
};
use rustc_session::config::{DebugInfo, EntryFnType};
use rustc_span::{DUMMY_SP, ErrorGuaranteed, Span, Spanned, dummy_spanned, respan};
use rustc_trait_selection::traits;
use std::cell::OnceCell;

// From rustc_monomorphize/errors.rs
#[derive(Diagnostic)]
#[diag("the above error was encountered while instantiating `{$kind} {$instance}`")]
struct EncounteredErrorWhileInstantiating<'tcx> {
    #[primary_span]
    pub span: Span,
    pub kind: &'static str,
    pub instance: Instance<'tcx>,
}

#[derive(Diagnostic)]
#[diag("the above error was encountered while instantiating `global_asm`")]
struct EncounteredErrorWhileInstantiatingGlobalAsm {
    #[primary_span]
    pub span: Span,
}

#[derive(Diagnostic)]
#[diag("reached the recursion limit while instantiating `{$instance}`")]
struct RecursionLimit<'tcx> {
    #[primary_span]
    pub span: Span,
    pub instance: Instance<'tcx>,
    #[note("`{$def_path_str}` defined here")]
    pub def_span: Span,
    pub def_path_str: String,
}

// From rustc_monomorphize/lib.rs
fn custom_coerce_unsize_info<'tcx>(
    tcx: TyCtxtAt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    source_ty: Ty<'tcx>,
    target_ty: Ty<'tcx>,
) -> Result<CustomCoerceUnsized, ErrorGuaranteed> {
    let trait_ref = ty::TraitRef::new(
        tcx.tcx,
        tcx.require_lang_item(LangItem::CoerceUnsized, tcx.span),
        [source_ty, target_ty],
    );

    match tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref)) {
        Ok(traits::ImplSource::UserDefined(traits::ImplSourceUserDefinedData {
            impl_def_id,
            ..
        })) => Ok(tcx.coerce_unsized_info(*impl_def_id)?.custom_kind.unwrap()),
        impl_source => {
            bug!("invalid `CoerceUnsized` impl_source: {:?}", impl_source);
        }
    }
}

/// The state that is shared across the concurrent threads that are doing collection.
struct SharedState<'tcx> {
    /// Items that have been or are currently being recursively collected.
    visited: Lock<UnordSet<MonoItem<'tcx>>>,
    /// Items that have been or are currently being recursively treated as "mentioned", i.e., their
    /// consts are evaluated but nothing is added to the collection.
    mentioned: Lock<UnordSet<MonoItem<'tcx>>>,
    /// Which items are being used where, for better errors.
    usage_map: Lock<UsageMap<'tcx>>,
}

#[derive(PartialEq)]
pub enum MonoItemCollectionStrategy {
    Eager,
    Lazy,
}

// DIFF: add span, allow iteration
pub struct UsageMap<'tcx> {
    // Maps every mono item to the mono items used by it.
    pub used_map: FxHashMap<MonoItem<'tcx>, Vec<Spanned<MonoItem<'tcx>>>>,
}

impl<'tcx> UsageMap<'tcx> {
    fn new() -> UsageMap<'tcx> {
        UsageMap {
            used_map: Default::default(),
        }
    }

    fn record_used<'a>(&mut self, user_item: MonoItem<'tcx>, used_items: &'a MonoItems<'tcx>)
    where
        'tcx: 'a,
    {
        assert!(
            self.used_map
                .insert(user_item, used_items.items().collect())
                .is_none()
        );
    }

    // Internally iterate over all items and the things each accesses.
    pub fn for_each_item_and_its_used_items<F>(&self, mut f: F)
    where
        F: FnMut(MonoItem<'tcx>, &[Spanned<MonoItem<'tcx>>]),
    {
        for (&item, used_item) in &self.used_map {
            f(item, used_item);
        }
    }
}

struct MonoItems<'tcx> {
    // We want a set of MonoItem + Span where trying to re-insert a MonoItem with a different Span
    // is ignored. Map does that, but it looks odd.
    items: FxIndexMap<MonoItem<'tcx>, Span>,
}

impl<'tcx> MonoItems<'tcx> {
    fn new() -> Self {
        Self {
            items: FxIndexMap::default(),
        }
    }

    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    fn push(&mut self, item: Spanned<MonoItem<'tcx>>) {
        // Insert only if the entry does not exist. A normal insert would stomp the first span that
        // got inserted.
        self.items.entry(item.node).or_insert(item.span);
    }

    // DIFF: add span
    fn items(&self) -> impl Iterator<Item = Spanned<MonoItem<'tcx>>> {
        self.items.iter().map(|(item, span)| respan(*span, *item))
    }
}

impl<'tcx> IntoIterator for MonoItems<'tcx> {
    type Item = Spanned<MonoItem<'tcx>>;
    type IntoIter = impl Iterator<Item = Spanned<MonoItem<'tcx>>>;

    fn into_iter(self) -> Self::IntoIter {
        self.items
            .into_iter()
            .map(|(item, span)| respan(span, item))
    }
}

impl<'tcx> Extend<Spanned<MonoItem<'tcx>>> for MonoItems<'tcx> {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = Spanned<MonoItem<'tcx>>>,
    {
        for item in iter {
            self.push(item)
        }
    }
}

fn collect_items_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    starting_item: Spanned<MonoItem<'tcx>>,
    state: &SharedState<'tcx>,
    recursion_limit: Limit,
) {
    if !state.visited.lock().insert(starting_item.node) {
        // We've been here already, no need to search again.
        return;
    }
    let mut recursion_depths = DefIdMap::default();
    collect_items_rec(
        tcx,
        starting_item,
        state,
        &mut recursion_depths,
        recursion_limit,
        CollectionMode::UsedItems,
    );
}

/// Collect all monomorphized items reachable from `starting_point`, and emit a note diagnostic if a
/// post-monomorphization error is encountered during a collection step.
///
/// `mode` determined whether we are scanning for [used items][CollectionMode::UsedItems]
/// or [mentioned items][CollectionMode::MentionedItems].
fn collect_items_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    starting_item: Spanned<MonoItem<'tcx>>,
    state: &SharedState<'tcx>,
    recursion_depths: &mut DefIdMap<usize>,
    recursion_limit: Limit,
    mode: CollectionMode,
) {
    let mut used_items = MonoItems::new();
    let mut mentioned_items = MonoItems::new();
    let recursion_depth_reset;

    // Post-monomorphization errors MVP
    //
    // We can encounter errors while monomorphizing an item, but we don't have a good way of
    // showing a complete stack of spans ultimately leading to collecting the erroneous one yet.
    // (It's also currently unclear exactly which diagnostics and information would be interesting
    // to report in such cases)
    //
    // This leads to suboptimal error reporting: a post-monomorphization error (PME) will be
    // shown with just a spanned piece of code causing the error, without information on where
    // it was called from. This is especially obscure if the erroneous mono item is in a
    // dependency. See for example issue #85155, where, before minimization, a PME happened two
    // crates downstream from libcore's stdarch, without a way to know which dependency was the
    // cause.
    //
    // If such an error occurs in the current crate, its span will be enough to locate the
    // source. If the cause is in another crate, the goal here is to quickly locate which mono
    // item in the current crate is ultimately responsible for causing the error.
    //
    // To give at least _some_ context to the user: while collecting mono items, we check the
    // error count. If it has changed, a PME occurred, and we trigger some diagnostics about the
    // current step of mono items collection.
    //
    // FIXME: don't rely on global state, instead bubble up errors. Note: this is very hard to do.
    let error_count = tcx.dcx().err_count();

    // In `mentioned_items` we collect items that were mentioned in this MIR but possibly do not
    // need to be monomorphized. This is done to ensure that optimizing away function calls does not
    // hide const-eval errors that those calls would otherwise have triggered.
    match starting_item.node {
        MonoItem::Static(def_id) => {
            recursion_depth_reset = None;

            // Statics always get evaluated (which is possible because they can't be generic), so for
            // `MentionedItems` collection there's nothing to do here.
            if mode == CollectionMode::UsedItems {
                let instance = Instance::mono(tcx, def_id);

                // Sanity check whether this ended up being collected accidentally
                debug_assert!(tcx.should_codegen_locally(instance));

                let DefKind::Static { nested, .. } = tcx.def_kind(def_id) else {
                    bug!()
                };
                // Nested statics have no type.
                if !nested {
                    let ty = instance.ty(tcx, ty::TypingEnv::fully_monomorphized());
                    visit_drop_use(tcx, ty, true, starting_item.span, &mut used_items);
                }

                if let Ok(alloc) = tcx.eval_static_initializer(def_id) {
                    for &prov in alloc.inner().provenance().ptrs().values() {
                        collect_alloc(tcx, prov.alloc_id(), &mut used_items);
                    }
                }

                if tcx.needs_thread_local_shim(def_id) {
                    used_items.push(respan(
                        starting_item.span,
                        MonoItem::Fn(Instance {
                            def: InstanceKind::Shim(ty::ShimKind::ThreadLocal(def_id)),
                            args: GenericArgs::empty(),
                        }),
                    ));
                }
            }

            // mentioned_items stays empty since there's no codegen for statics. statics don't get
            // optimized, and if they did then the const-eval interpreter would have to worry about
            // mentioned_items.
        }
        MonoItem::Fn(instance) => {
            // Sanity check whether this ended up being collected accidentally
            debug_assert!(tcx.should_codegen_locally(instance));

            // Keep track of the monomorphization recursion depth
            recursion_depth_reset = Some(check_recursion_limit(
                tcx,
                instance,
                starting_item.span,
                recursion_depths,
                recursion_limit,
            ));

            let (used, mentioned) = items_of_instance(tcx, (instance, mode));
            used_items.extend(used.into_iter().copied());
            mentioned_items.extend(mentioned.into_iter().copied());
        }

        MonoItem::GlobalAsm(item_id) => {
            assert!(
                mode == CollectionMode::UsedItems,
                "should never encounter global_asm when collecting mentioned items"
            );
            recursion_depth_reset = None;

            let item = tcx.hir_item(item_id);
            if let hir::ItemKind::GlobalAsm { asm, .. } = item.kind {
                for (op, op_sp) in asm.operands {
                    match *op {
                        hir::InlineAsmOperand::Const { .. } => {
                            // Only constants which resolve to a plain integer
                            // are supported. Therefore the value should not
                            // depend on any other items.
                        }
                        hir::InlineAsmOperand::SymFn { expr } => {
                            let fn_ty = tcx.typeck(item_id.owner_id).expr_ty(expr);
                            visit_fn_use(tcx, fn_ty, false, *op_sp, &mut used_items);
                        }
                        hir::InlineAsmOperand::SymStatic { path: _, def_id } => {
                            // DIFF: remove should_codegen_locally
                            trace!("collecting static {:?}", def_id);
                            used_items.push(dummy_spanned(MonoItem::Static(def_id)));
                        }
                        hir::InlineAsmOperand::In { .. }
                        | hir::InlineAsmOperand::Out { .. }
                        | hir::InlineAsmOperand::InOut { .. }
                        | hir::InlineAsmOperand::SplitInOut { .. }
                        | hir::InlineAsmOperand::Label { .. } => {
                            span_bug!(*op_sp, "invalid operand type for global_asm!")
                        }
                    }
                }
            } else {
                span_bug!(
                    item.span,
                    "Mismatch between hir::Item type and MonoItem type"
                )
            }

            // mention_items stays empty as nothing gets optimized here.
        }
    }

    // Check for PMEs and emit a diagnostic if one happened. To try to show relevant edges of the
    // mono item graph.
    if tcx.dcx().err_count() > error_count
        && starting_item.node.is_generic_fn()
        && starting_item.node.is_user_defined()
    {
        match starting_item.node {
            MonoItem::Fn(instance) => tcx.dcx().emit_note(EncounteredErrorWhileInstantiating {
                span: starting_item.span,
                kind: "fn",
                instance,
            }),
            MonoItem::Static(def_id) => tcx.dcx().emit_note(EncounteredErrorWhileInstantiating {
                span: starting_item.span,
                kind: "static",
                instance: Instance::new_raw(def_id, GenericArgs::empty()),
            }),
            MonoItem::GlobalAsm(_) => {
                tcx.dcx()
                    .emit_note(EncounteredErrorWhileInstantiatingGlobalAsm {
                        span: starting_item.span,
                    })
            }
        }
    }

    // Only updating `usage_map` for used items as otherwise we may be inserting the same item
    // multiple times (if it is first 'mentioned' and then later actually used), and the usage map
    // logic does not like that.
    // This is part of the output of collection and hence only relevant for "used" items.
    // ("Mentioned" items are only considered internally during collection.)
    if mode == CollectionMode::UsedItems {
        state
            .usage_map
            .lock()
            .record_used(starting_item.node, &used_items);
    }

    {
        let mut visited = OnceCell::default();
        if mode == CollectionMode::UsedItems {
            used_items
                .items
                .retain(|k, _| visited.get_mut_or_init(|| state.visited.lock()).insert(*k));
        }

        let mut mentioned = OnceCell::default();
        mentioned_items.items.retain(|k, _| {
            !visited.get_or_init(|| state.visited.lock()).contains(k)
                && mentioned
                    .get_mut_or_init(|| state.mentioned.lock())
                    .insert(*k)
        });
    }
    if mode == CollectionMode::MentionedItems {
        assert!(
            used_items.is_empty(),
            "'mentioned' collection should never encounter used items"
        );
    } else {
        for used_item in used_items {
            let should_gen = match used_item.node {
                MonoItem::Static(def_id) => {
                    let instance = Instance::mono(tcx, def_id);
                    tcx.should_codegen_locally(instance)
                }
                MonoItem::Fn(instance) => tcx.should_codegen_locally(instance),
                MonoItem::GlobalAsm(_) => true,
            };
            if should_gen {
                collect_items_rec(
                    tcx,
                    used_item,
                    state,
                    recursion_depths,
                    recursion_limit,
                    CollectionMode::UsedItems,
                );
            }
        }
    }

    // Walk over mentioned items *after* used items, so that if an item is both mentioned and used then
    // the loop above has fully collected it, so this loop will skip it.
    for mentioned_item in mentioned_items {
        let should_gen = match mentioned_item.node {
            MonoItem::Static(def_id) => {
                let instance = Instance::mono(tcx, def_id);
                tcx.should_codegen_locally(instance)
            }
            MonoItem::Fn(instance) => tcx.should_codegen_locally(instance),
            MonoItem::GlobalAsm(_) => true,
        };
        if should_gen {
            collect_items_rec(
                tcx,
                mentioned_item,
                state,
                recursion_depths,
                recursion_limit,
                CollectionMode::MentionedItems,
            );
        }
    }

    if let Some((def_id, depth)) = recursion_depth_reset {
        recursion_depths.insert(def_id, depth);
    }
}

fn check_recursion_limit<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    span: Span,
    recursion_depths: &mut DefIdMap<usize>,
    recursion_limit: Limit,
) -> (DefId, usize) {
    let def_id = instance.def_id();
    let recursion_depth = recursion_depths.get(&def_id).cloned().unwrap_or(0);
    debug!(" => recursion depth={}", recursion_depth);

    let adjusted_recursion_depth = if tcx.is_lang_item(def_id, LangItem::DropGlue) {
        // HACK: `drop_glue` creates tight monomorphization loops. Give
        // it more margin.
        recursion_depth / 4
    } else {
        recursion_depth
    };

    // Code that needs to instantiate the same function recursively
    // more than the recursion limit is assumed to be causing an
    // infinite expansion.
    if !recursion_limit.value_within_limit(adjusted_recursion_depth) {
        let def_span = tcx.def_span(def_id);
        let def_path_str = tcx.def_path_str(def_id);
        tcx.dcx().emit_fatal(RecursionLimit {
            span,
            instance,
            def_span,
            def_path_str,
        });
    }

    recursion_depths.insert(def_id, recursion_depth + 1);

    (def_id, recursion_depth)
}

struct MirUsedCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a mir::Body<'tcx>,
    used_items: &'a mut MonoItems<'tcx>,
    /// See the comment in `collect_items_of_instance` for the purpose of this set.
    /// Note that this contains *not-monomorphized* items!
    used_mentioned_items: &'a mut UnordSet<MentionedItem<'tcx>>,
    instance: Instance<'tcx>,
}

impl<'a, 'tcx> MirUsedCollector<'a, 'tcx> {
    pub fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<TyCtxt<'tcx>>,
    {
        debug!("monomorphize: self.instance={:?}", self.instance);
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(self.tcx, value),
        )
    }

    /// Evaluates a *not yet monomorphized* constant.
    fn eval_constant(&mut self, constant: &mir::ConstOperand<'tcx>) -> Option<mir::ConstValue> {
        let const_ = self.monomorphize(constant.const_);
        // Evaluate the constant. This makes const eval failure a collection-time error (rather than
        // a codegen-time error). rustc stops after collection if there was an error, so this
        // ensures codegen never has to worry about failing consts.
        // (codegen relies on this and ICEs will happen if this is violated.)
        match const_.eval(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            constant.span,
        ) {
            Ok(v) => Some(v),
            Err(ErrorHandled::TooGeneric(..)) => span_bug!(
                constant.span,
                "collection encountered polymorphic constant: {:?}",
                const_
            ),
            Err(err @ ErrorHandled::Reported(..)) => {
                err.emit_note(self.tcx);
                return None;
            }
        }
    }
}

impl<'a, 'tcx> MirVisitor<'tcx> for MirUsedCollector<'a, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &mir::Rvalue<'tcx>, location: Location) {
        debug!("visiting rvalue {:?}", *rvalue);

        let span = self.body.source_info(location).span;

        match *rvalue {
            // When doing an cast from a regular pointer to a fat pointer, we
            // have to instantiate all methods of the trait being cast to, so we
            // can build the appropriate vtable.
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _),
                ref operand,
                target_ty,
            ) => {
                let source_ty = operand.ty(self.body, self.tcx);
                // *Before* monomorphizing, record that we already handled this mention.
                self.used_mentioned_items.insert(MentionedItem::UnsizeCast {
                    source_ty,
                    target_ty,
                });
                let target_ty = self.monomorphize(target_ty);
                let source_ty = self.monomorphize(source_ty);
                let (source_ty, target_ty) = find_tails_for_unsizing(
                    self.tcx.at(span),
                    ty::TypingEnv::fully_monomorphized(),
                    source_ty,
                    target_ty,
                );
                // This could also be a different Unsize instruction, like
                // from a fixed sized array to a slice. But we are only
                // interested in things that produce a vtable.
                if target_ty.is_trait() && !source_ty.is_trait() {
                    create_mono_items_for_vtable_methods(
                        self.tcx,
                        target_ty,
                        source_ty,
                        span,
                        self.used_items,
                    );
                }
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer(_), _),
                ref operand,
                _,
            ) => {
                let fn_ty = operand.ty(self.body, self.tcx);
                // *Before* monomorphizing, record that we already handled this mention.
                self.used_mentioned_items.insert(MentionedItem::Fn(fn_ty));
                let fn_ty = self.monomorphize(fn_ty);
                visit_fn_use(self.tcx, fn_ty, false, span, self.used_items);
            }
            mir::Rvalue::Cast(
                mir::CastKind::PointerCoercion(PointerCoercion::ClosureFnPointer(_), _),
                ref operand,
                _,
            ) => {
                let source_ty = operand.ty(self.body, self.tcx);
                // *Before* monomorphizing, record that we already handled this mention.
                self.used_mentioned_items
                    .insert(MentionedItem::Closure(source_ty));
                let source_ty = self.monomorphize(source_ty);
                if let ty::Closure(def_id, args) = *source_ty.kind() {
                    let instance =
                        Instance::resolve_closure(self.tcx, def_id, args, ty::ClosureKind::FnOnce);
                    // DIFF: remove should_codegen_locally
                    self.used_items
                        .push(create_fn_mono_item(self.tcx, instance, span));
                } else {
                    bug!()
                }
            }
            mir::Rvalue::ThreadLocalRef(def_id) => {
                assert!(self.tcx.is_thread_local_static(def_id));
                // DIFF: remove should_codegen_locally
                trace!("collecting thread-local static {:?}", def_id);
                self.used_items.push(respan(span, MonoItem::Static(def_id)));
            }
            _ => { /* not interesting */ }
        }

        self.super_rvalue(rvalue, location);
    }

    /// This does not walk the MIR of the constant as that is not needed for codegen, all we need is
    /// to ensure that the constant evaluates successfully and walk the result.
    fn visit_const_operand(&mut self, constant: &mir::ConstOperand<'tcx>, _location: Location) {
        // No `super_constant` as we don't care about `visit_ty`/`visit_ty_const`.
        let Some(val) = self.eval_constant(constant) else {
            return;
        };
        collect_const_value(self.tcx, val, self.used_items);
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        debug!("visiting terminator {:?} @ {:?}", terminator, location);
        let source = self.body.source_info(location).span;

        let tcx = self.tcx;
        let push_mono_lang_item = |this: &mut Self, lang_item: LangItem| {
            let instance = Instance::mono(tcx, tcx.require_lang_item(lang_item, source));
            // DIFF: remove should_codegen_locally
            this.used_items
                .push(create_fn_mono_item(tcx, instance, source));
        };

        match terminator.kind {
            mir::TerminatorKind::Call { ref func, .. }
            | mir::TerminatorKind::TailCall { ref func, .. } => {
                let callee_ty = func.ty(self.body, tcx);
                // *Before* monomorphizing, record that we already handled this mention.
                self.used_mentioned_items
                    .insert(MentionedItem::Fn(callee_ty));
                let callee_ty = self.monomorphize(callee_ty);

                // HACK(explicit_tail_calls): collect tail calls to `#[track_caller]` functions as indirect,
                // because we later call them as such, to prevent issues with ABI incompatibility.
                // Ideally we'd replace such tail calls with normal call + return, but this requires
                // post-mono MIR optimizations, which we don't yet have.
                let force_indirect_call =
                    if matches!(terminator.kind, mir::TerminatorKind::TailCall { .. })
                        && let &ty::FnDef(def_id, args) = callee_ty.kind()
                        && let instance = ty::Instance::expect_resolve(
                            self.tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            def_id,
                            args.no_bound_vars().unwrap(),
                            source,
                        )
                        && instance.def.requires_caller_location(self.tcx)
                    {
                        true
                    } else {
                        false
                    };

                visit_fn_use(
                    self.tcx,
                    callee_ty,
                    !force_indirect_call,
                    source,
                    &mut self.used_items,
                )
            }
            mir::TerminatorKind::Drop { ref place, .. } => {
                let ty = place.ty(self.body, self.tcx).ty;
                // *Before* monomorphizing, record that we already handled this mention.
                self.used_mentioned_items.insert(MentionedItem::Drop(ty));
                let ty = self.monomorphize(ty);
                visit_drop_use(self.tcx, ty, true, source, self.used_items);
            }
            mir::TerminatorKind::InlineAsm { ref operands, .. } => {
                for op in operands {
                    match *op {
                        mir::InlineAsmOperand::SymFn { ref value } => {
                            let fn_ty = value.const_.ty();
                            // *Before* monomorphizing, record that we already handled this mention.
                            self.used_mentioned_items.insert(MentionedItem::Fn(fn_ty));
                            let fn_ty = self.monomorphize(fn_ty);
                            visit_fn_use(self.tcx, fn_ty, false, source, self.used_items);
                        }
                        mir::InlineAsmOperand::SymStatic { def_id } => {
                            // DIFF: remove should_codegen_locally
                            trace!("collecting asm sym static {:?}", def_id);
                            self.used_items
                                .push(respan(source, MonoItem::Static(def_id)));
                        }
                        _ => {}
                    }
                }
            }
            mir::TerminatorKind::Assert { ref msg, .. } => match &**msg {
                mir::AssertKind::BoundsCheck { .. } => {
                    push_mono_lang_item(self, LangItem::PanicBoundsCheck);
                }
                mir::AssertKind::MisalignedPointerDereference { .. } => {
                    push_mono_lang_item(self, LangItem::PanicMisalignedPointerDereference);
                }
                mir::AssertKind::NullPointerDereference => {
                    push_mono_lang_item(self, LangItem::PanicNullPointerDereference);
                }
                mir::AssertKind::InvalidEnumConstruction(_) => {
                    push_mono_lang_item(self, LangItem::PanicInvalidEnumConstruction);
                }
                _ => {
                    push_mono_lang_item(self, msg.panic_function());
                }
            },
            mir::TerminatorKind::UnwindTerminate(reason) => {
                push_mono_lang_item(self, reason.lang_item());
            }
            mir::TerminatorKind::Goto { .. }
            | mir::TerminatorKind::SwitchInt { .. }
            | mir::TerminatorKind::UnwindResume
            | mir::TerminatorKind::Return
            | mir::TerminatorKind::Unreachable => {}
            mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::Yield { .. }
            | mir::TerminatorKind::FalseEdge { .. }
            | mir::TerminatorKind::FalseUnwind { .. } => bug!(),
        }

        if let Some(mir::UnwindAction::Terminate(reason)) = terminator.unwind() {
            push_mono_lang_item(self, reason.lang_item());
        }

        self.super_terminator(terminator, location);
    }
}

fn visit_drop_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut MonoItems<'tcx>,
) {
    let instance = Instance::resolve_drop_glue(tcx, ty);
    visit_instance_use(tcx, instance, is_direct_call, source, output);
}

fn visit_fn_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut MonoItems<'tcx>,
) {
    if let ty::FnDef(def_id, args) = *ty.kind() {
        let args = args.no_bound_vars().unwrap();
        let instance = if is_direct_call {
            ty::Instance::expect_resolve(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                def_id,
                args,
                source,
            )
        } else {
            match ty::Instance::resolve_for_fn_ptr(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                def_id,
                args,
            ) {
                Some(instance) => instance,
                _ => bug!("failed to resolve instance for {ty}"),
            }
        };
        visit_instance_use(tcx, instance, is_direct_call, source, output);
    }
}

fn visit_instance_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    is_direct_call: bool,
    source: Span,
    output: &mut MonoItems<'tcx>,
) {
    debug!(
        "visit_item_use({:?}, is_direct_call={:?})",
        instance, is_direct_call
    );
    // DIFF: remove should_codegen_locally

    if let Some(intrinsic) = tcx.intrinsic(instance.def_id()) {
        // TODO: should I also vendor in autodiff code?
        // collect_autodiff_fn(tcx, instance, intrinsic, output);

        if let Some(_requirement) = ValidityRequirement::from_intrinsic(intrinsic.name) {
            // The intrinsics assert_inhabited, assert_zero_valid, and assert_mem_uninitialized_valid will
            // be lowered in codegen to nothing or a call to panic_nounwind. So if we encounter any
            // of those intrinsics, we need to include a mono item for panic_nounwind, else we may try to
            // codegen a call to that function without generating code for the function itself.
            let def_id = tcx.require_lang_item(LangItem::PanicNounwind, source);
            let panic_instance = Instance::mono(tcx, def_id);
            // DIFF: remove should_codegen_locally
            output.push(create_fn_mono_item(tcx, panic_instance, source));
        } else if !intrinsic.must_be_overridden {
            // Codegen the fallback body of intrinsics with fallback bodies.
            // We explicitly skip this otherwise to ensure we get a linker error
            // if anyone tries to call this intrinsic and the codegen backend did not
            // override the implementation.
            let instance = ty::Instance::new_raw(instance.def_id(), instance.args);
            // DIFF: remove should_codegen_locally
            output.push(create_fn_mono_item(tcx, instance, source));
        }
    }

    match instance.def {
        ty::InstanceKind::Virtual(..)
        | ty::InstanceKind::Intrinsic(_)
        | ty::InstanceKind::LlvmIntrinsic(_) => {
            if !is_direct_call {
                bug!("{:?} being reified", instance);
            }
        }
        ty::InstanceKind::Shim(ty::ShimKind::ThreadLocal(..)) => {
            bug!("{:?} being reified", instance);
        }
        ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, None)) => {
            // Don't need to emit noop drop glue if we are calling directly.
            //
            // Note that we also optimize away the call to visit_instance_use in vtable construction
            // (see create_mono_items_for_vtable_methods).
            if !is_direct_call {
                output.push(create_fn_mono_item(tcx, instance, source));
            }
        }
        ty::InstanceKind::Item(..)
        | ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(_)))
        | ty::InstanceKind::Shim(ty::ShimKind::FutureDropPoll(..))
        | ty::InstanceKind::Shim(ty::ShimKind::AsyncDropGlue(_, _))
        | ty::InstanceKind::Shim(ty::ShimKind::AsyncDropGlueCtor(_, _))
        | ty::InstanceKind::Shim(ty::ShimKind::VTable(..))
        | ty::InstanceKind::Shim(ty::ShimKind::Reify(..))
        | ty::InstanceKind::Shim(ty::ShimKind::ClosureOnce { .. })
        | ty::InstanceKind::Shim(ty::ShimKind::ConstructCoroutineInClosure { .. })
        | ty::InstanceKind::Shim(ty::ShimKind::FnPtr(..))
        | ty::InstanceKind::Shim(ty::ShimKind::Clone(..))
        | ty::InstanceKind::Shim(ty::ShimKind::FnPtrAsPtr(..))
        | ty::InstanceKind::Shim(ty::ShimKind::FnPtrFromPtr(..)) => {
            output.push(create_fn_mono_item(tcx, instance, source));
        }
    }
}

/// For a given pair of source and target type that occur in an unsizing coercion,
/// this function finds the pair of types that determines the vtable linking
/// them.
///
/// For example, the source type might be `&SomeStruct` and the target type
/// might be `&dyn SomeTrait` in a cast like:
///
/// ```rust,ignore (not real code)
/// let src: &SomeStruct = ...;
/// let target = src as &dyn SomeTrait;
/// ```
///
/// Then the output of this function would be (SomeStruct, SomeTrait) since for
/// constructing the `target` fat-pointer we need the vtable for that pair.
///
/// Things can get more complicated though because there's also the case where
/// the unsized type occurs as a field:
///
/// ```rust
/// struct ComplexStruct<T: ?Sized> {
///    a: u32,
///    b: f64,
///    c: T
/// }
/// ```
///
/// In this case, if `T` is sized, `&ComplexStruct<T>` is a thin pointer. If `T`
/// is unsized, `&SomeStruct` is a fat pointer, and the vtable it points to is
/// for the pair of `T` (which is a trait) and the concrete type that `T` was
/// originally coerced from:
///
/// ```rust,ignore (not real code)
/// let src: &ComplexStruct<SomeStruct> = ...;
/// let target = src as &ComplexStruct<dyn SomeTrait>;
/// ```
///
/// Again, we want this `find_tails_for_unsizing()` to provide the pair
/// `(SomeStruct, SomeTrait)`.
///
/// Finally, there is also the case of custom unsizing coercions, e.g., for
/// smart pointers such as `Rc` and `Arc`.
pub fn find_tails_for_unsizing<'tcx>(
    tcx: TyCtxtAt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    source_ty: Ty<'tcx>,
    target_ty: Ty<'tcx>,
) -> (Ty<'tcx>, Ty<'tcx>) {
    match (source_ty.kind(), target_ty.kind()) {
        (&ty::Pat(source, _), &ty::Pat(target, _)) => {
            find_tails_for_unsizing(tcx, typing_env, source, target)
        }
        (
            &ty::Ref(_, source_pointee, _),
            &ty::Ref(_, target_pointee, _) | &ty::RawPtr(target_pointee, _),
        )
        | (&ty::RawPtr(source_pointee, _), &ty::RawPtr(target_pointee, _)) => {
            tcx.struct_lockstep_tails_for_codegen(source_pointee, target_pointee, typing_env)
        }

        // `Box<T>` could go through the ADT code below, b/c it'll unpeel to `Unique<T>`,
        // and eventually bottom out in a raw ref, but we can micro-optimize it here.
        (_, _)
            if let Some(source_boxed) = source_ty.boxed_ty()
                && let Some(target_boxed) = target_ty.boxed_ty() =>
        {
            tcx.struct_lockstep_tails_for_codegen(source_boxed, target_boxed, typing_env)
        }

        (&ty::Adt(source_adt_def, source_args), &ty::Adt(target_adt_def, target_args)) => {
            assert_eq!(source_adt_def, target_adt_def);
            let CustomCoerceUnsized::Struct(coerce_index) =
                match custom_coerce_unsize_info(tcx, typing_env, source_ty, target_ty) {
                    Ok(ccu) => ccu,
                    Err(e) => {
                        let e = Ty::new_error(tcx.tcx, e);
                        return (e, e);
                    }
                };
            let coerce_field = &source_adt_def.non_enum_variant().fields[coerce_index];
            // We're getting a possibly unnormalized type, so normalize it.
            let source_field =
                tcx.normalize_erasing_regions(typing_env, coerce_field.ty(*tcx, source_args));
            let target_field =
                tcx.normalize_erasing_regions(typing_env, coerce_field.ty(*tcx, target_args));
            find_tails_for_unsizing(tcx, typing_env, source_field, target_field)
        }

        _ => bug!(
            "find_tails_for_unsizing: invalid coercion {:?} -> {:?}",
            source_ty,
            target_ty
        ),
    }
}

fn create_fn_mono_item<'tcx>(
    _tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    source: Span,
) -> Spanned<MonoItem<'tcx>> {
    respan(source, MonoItem::Fn(instance))
}

/// Creates a `MonoItem` for each method that is referenced by the vtable for
/// the given trait/impl pair.
fn create_mono_items_for_vtable_methods<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ty: Ty<'tcx>,
    impl_ty: Ty<'tcx>,
    source: Span,
    output: &mut MonoItems<'tcx>,
) {
    assert!(!trait_ty.has_escaping_bound_vars() && !impl_ty.has_escaping_bound_vars());

    let ty::Dynamic(trait_ty, ..) = trait_ty.kind() else {
        bug!("create_mono_items_for_vtable_methods: {trait_ty:?} not a trait type");
    };

    if let Some(principal) = trait_ty.principal() {
        let trait_ref =
            tcx.instantiate_bound_regions_with_erased(principal.with_self_ty(tcx, impl_ty));
        assert!(!trait_ref.has_escaping_bound_vars());

        // Walk all methods of the trait, including those of its supertraits
        let entries = tcx.vtable_entries(trait_ref);
        debug!(?entries);
        let methods = entries
            .iter()
            .filter_map(|entry| match entry {
                VtblEntry::MetadataDropInPlace
                | VtblEntry::MetadataSize
                | VtblEntry::MetadataAlign
                | VtblEntry::Vacant => None,
                VtblEntry::TraitVPtr(_) => {
                    // all super trait items already covered, so skip them.
                    None
                }
                // DIFF: remove should_codegen_locally
                VtblEntry::Method(instance) => Some(*instance),
            })
            .map(|item| create_fn_mono_item(tcx, item, source));
        output.extend(methods);
    }

    // Also add the destructor, if it's necessary.
    //
    // This matches the check in vtable_allocation_provider in middle/ty/vtable.rs,
    // if we don't need drop we're not adding an actual pointer to the vtable.
    if impl_ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized()) {
        visit_drop_use(tcx, impl_ty, false, source, output);
    }
}

/// Scans the CTFE alloc in order to find function calls, closures, and drop-glue.
fn collect_alloc<'tcx>(tcx: TyCtxt<'tcx>, alloc_id: AllocId, output: &mut MonoItems<'tcx>) {
    match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Static(def_id) => {
            assert!(!tcx.is_thread_local_static(def_id));
            // DIFF: remove should_codegen_locally
            trace!("collecting static {:?}", def_id);
            output.push(dummy_spanned(MonoItem::Static(def_id)));
        }
        GlobalAlloc::Memory(alloc) => {
            trace!("collecting {:?} with {:#?}", alloc_id, alloc);
            let ptrs = alloc.inner().provenance().ptrs();
            // avoid `ensure_sufficient_stack` in the common case of "no pointers"
            if !ptrs.is_empty() {
                for &prov in ptrs.values() {
                    collect_alloc(tcx, prov.alloc_id(), output);
                }
            }
        }
        GlobalAlloc::Function { instance, .. } => {
            // DIFF: remove should_codegen_locally
            trace!("collecting {:?} with {:#?}", alloc_id, instance);
            output.push(create_fn_mono_item(tcx, instance, DUMMY_SP));
        }
        GlobalAlloc::VTable(ty, dyn_ty) => {
            let alloc_id = tcx.vtable_allocation((
                ty,
                dyn_ty
                    .principal()
                    .map(|principal| tcx.instantiate_bound_regions_with_erased(principal)),
            ));
            collect_alloc(tcx, alloc_id, output)
        }
        GlobalAlloc::TypeId { .. } => {}
    }
}

/// Scans the MIR in order to find function calls, closures, and drop-glue.
///
/// Anything that's found is added to `output`. Furthermore the "mentioned items" of the MIR are returned.
fn collect_items_of_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    mode: CollectionMode,
) -> (MonoItems<'tcx>, MonoItems<'tcx>) {
    // This item is getting monomorphized, do mono-time checks.
    tcx.ensure_ok().check_mono_item(instance);

    let body = tcx.instance_mir(instance.def);
    // Naively, in "used" collection mode, all functions get added to *both* `used_items` and
    // `mentioned_items`. Mentioned items processing will then notice that they have already been
    // visited, but at that point each mentioned item has been monomorphized, added to the
    // `mentioned_items` worklist, and checked in the global set of visited items. To remove that
    // overhead, we have a special optimization that avoids adding items to `mentioned_items` when
    // they are already added in `used_items`. We could just scan `used_items`, but that's a linear
    // scan and not very efficient. Furthermore we can only do that *after* monomorphizing the
    // mentioned item. So instead we collect all pre-monomorphized `MentionedItem` that were already
    // added to `used_items` in a hash set, which can efficiently query in the
    // `body.mentioned_items` loop below without even having to monomorphize the item.
    let mut used_items = MonoItems::new();
    let mut mentioned_items = MonoItems::new();
    let mut used_mentioned_items = Default::default();
    let mut collector = MirUsedCollector {
        tcx,
        body,
        used_items: &mut used_items,
        used_mentioned_items: &mut used_mentioned_items,
        instance,
    };

    if mode == CollectionMode::UsedItems {
        if tcx.sess.opts.debuginfo == DebugInfo::Full {
            for var_debug_info in &body.var_debug_info {
                collector.visit_var_debug_info(var_debug_info);
            }
        }
        for (bb, data) in traversal::mono_reachable(body, tcx, instance) {
            collector.visit_basic_block_data(bb, data)
        }
    }

    // Always visit all `required_consts`, so that we evaluate them and abort compilation if any of
    // them errors.
    for const_op in body.required_consts() {
        if let Some(val) = collector.eval_constant(const_op) {
            collect_const_value(tcx, val, &mut mentioned_items);
        }
    }

    // Always gather mentioned items. We try to avoid processing items that we have already added to
    // `used_items` above.
    for item in body.mentioned_items() {
        if !collector.used_mentioned_items.contains(&item.node) {
            let item_mono = collector.monomorphize(item.node);
            visit_mentioned_item(tcx, &item_mono, item.span, &mut mentioned_items);
        }
    }

    (used_items, mentioned_items)
}

fn items_of_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    (instance, mode): (Instance<'tcx>, CollectionMode),
) -> (
    &'tcx [Spanned<MonoItem<'tcx>>],
    &'tcx [Spanned<MonoItem<'tcx>>],
) {
    let (used_items, mentioned_items) = collect_items_of_instance(tcx, instance, mode);

    let used_items = tcx.arena.alloc_from_iter(used_items);
    let mentioned_items = tcx.arena.alloc_from_iter(mentioned_items);

    (used_items, mentioned_items)
}

/// `item` must be already monomorphized.
fn visit_mentioned_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: &MentionedItem<'tcx>,
    span: Span,
    output: &mut MonoItems<'tcx>,
) {
    match *item {
        MentionedItem::Fn(ty) => {
            if let ty::FnDef(def_id, args) = *ty.kind() {
                let args = args.no_bound_vars().unwrap();
                let instance = Instance::expect_resolve(
                    tcx,
                    ty::TypingEnv::fully_monomorphized(),
                    def_id,
                    args,
                    span,
                );
                // `visit_instance_use` was written for "used" item collection but works just as well
                // for "mentioned" item collection.
                // We can set `is_direct_call`; that just means we'll skip a bunch of shims that anyway
                // can't have their own failing constants.
                visit_instance_use(tcx, instance, /*is_direct_call*/ true, span, output);
            }
        }
        MentionedItem::Drop(ty) => {
            visit_drop_use(tcx, ty, /*is_direct_call*/ true, span, output);
        }
        MentionedItem::UnsizeCast {
            source_ty,
            target_ty,
        } => {
            let (source_ty, target_ty) = find_tails_for_unsizing(
                tcx.at(span),
                ty::TypingEnv::fully_monomorphized(),
                source_ty,
                target_ty,
            );
            // This could also be a different Unsize instruction, like
            // from a fixed sized array to a slice. But we are only
            // interested in things that produce a vtable.
            if target_ty.is_trait() && !source_ty.is_trait() {
                create_mono_items_for_vtable_methods(tcx, target_ty, source_ty, span, output);
            }
        }
        MentionedItem::Closure(source_ty) => {
            if let ty::Closure(def_id, args) = *source_ty.kind() {
                let instance =
                    Instance::resolve_closure(tcx, def_id, args, ty::ClosureKind::FnOnce);
                // DIFF: remove should_codegen_locally
                output.push(create_fn_mono_item(tcx, instance, span));
            } else {
                bug!()
            }
        }
    }
}

fn collect_const_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: mir::ConstValue,
    output: &mut MonoItems<'tcx>,
) {
    match value {
        mir::ConstValue::Scalar(Scalar::Ptr(ptr, _size)) => {
            collect_alloc(tcx, ptr.provenance.alloc_id(), output)
        }
        mir::ConstValue::Indirect { alloc_id, .. }
        | mir::ConstValue::Slice { alloc_id, meta: _ } => collect_alloc(tcx, alloc_id, output),
        _ => {}
    }
}

//=-----------------------------------------------------------------------------
// Root Collection
//=-----------------------------------------------------------------------------

// Find all non-generic items by walking the HIR. These items serve as roots to
// start monomorphizing from.
fn collect_roots(tcx: TyCtxt<'_>, mode: MonoItemCollectionStrategy) -> Vec<MonoItem<'_>> {
    debug!("collecting roots");
    let mut roots = MonoItems::new();

    {
        let entry_fn = tcx.entry_fn(());

        debug!("collect_roots: entry_fn = {:?}", entry_fn);

        let mut collector = RootCollector {
            tcx,
            strategy: mode,
            entry_fn,
            output: &mut roots,
        };

        let crate_items = tcx.hir_crate_items(());

        for id in crate_items.free_items() {
            collector.process_item(id);
        }

        for id in crate_items.impl_items() {
            collector.process_impl_item(id);
        }

        for id in crate_items.nested_bodies() {
            collector.process_nested_body(id);
        }

        collector.push_extra_entry_roots();
    }

    // We can only codegen items that are instantiable - items all of
    // whose predicates hold. Luckily, items that aren't instantiable
    // can't actually be used, so we can just skip codegenning them.
    roots
        .into_iter()
        .filter_map(
            |Spanned {
                 node: mono_item, ..
             }| { mono_item.is_instantiable(tcx).then_some(mono_item) },
        )
        .collect()
}

struct RootCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    strategy: MonoItemCollectionStrategy,
    output: &'a mut MonoItems<'tcx>,
    entry_fn: Option<(DefId, EntryFnType)>,
}

impl<'v> RootCollector<'_, 'v> {
    fn process_item(&mut self, id: hir::ItemId) {
        match self.tcx.def_kind(id.owner_id) {
            DefKind::Enum | DefKind::Struct | DefKind::Union => {
                if self.strategy == MonoItemCollectionStrategy::Eager
                    && !self
                        .tcx
                        .generics_of(id.owner_id)
                        .requires_monomorphization(self.tcx)
                {
                    debug!("RootCollector: ADT drop-glue for `{id:?}`",);
                    let id_args =
                        ty::GenericArgs::for_item(self.tcx, id.owner_id.to_def_id(), |param, _| {
                            match param.kind {
                                GenericParamDefKind::Lifetime => {
                                    self.tcx.lifetimes.re_erased.into()
                                }
                                GenericParamDefKind::Type { .. }
                                | GenericParamDefKind::Const { .. } => {
                                    unreachable!(
                                        "`own_requires_monomorphization` check means that \
                                we should have no type/const params"
                                    )
                                }
                            }
                        });

                    // This type is impossible to instantiate, so we should not try to
                    // generate a `drop_glue` instance for it.
                    if self.tcx.instantiate_and_check_impossible_clauses((
                        id.owner_id.to_def_id(),
                        id_args,
                    )) {
                        return;
                    }

                    let ty = self
                        .tcx
                        .type_of(id.owner_id.to_def_id())
                        .instantiate(self.tcx, id_args)
                        .skip_norm_wip();
                    assert!(!ty.has_non_region_param());
                    visit_drop_use(self.tcx, ty, true, DUMMY_SP, self.output);
                }
            }
            DefKind::GlobalAsm => {
                debug!(
                    "RootCollector: ItemKind::GlobalAsm({})",
                    self.tcx.def_path_str(id.owner_id.to_def_id())
                );
                self.output.push(dummy_spanned(MonoItem::GlobalAsm(id)));
            }
            DefKind::Static { .. } => {
                let def_id = id.owner_id.to_def_id();
                debug!(
                    "RootCollector: ItemKind::Static({})",
                    self.tcx.def_path_str(def_id)
                );
                self.output.push(dummy_spanned(MonoItem::Static(def_id)));
            }
            DefKind::Const { .. } => {
                // Const items only generate mono items if they are actually used somewhere.
                // Just declaring them is insufficient.

                // If we're collecting items eagerly, then recurse into all constants.
                // Otherwise the value is only collected when explicitly mentioned in other items.
                if self.strategy == MonoItemCollectionStrategy::Eager {
                    if !self
                        .tcx
                        .generics_of(id.owner_id)
                        .own_requires_monomorphization()
                        && let Ok(val) = self.tcx.const_eval_poly(id.owner_id.to_def_id())
                    {
                        collect_const_value(self.tcx, val, self.output);
                    }
                }
            }
            DefKind::Impl { of_trait: true } => {
                if self.strategy == MonoItemCollectionStrategy::Eager {
                    create_mono_items_for_default_impls(self.tcx, id, self.output);
                }
            }
            DefKind::Fn => {
                self.push_if_root(id.owner_id.def_id);
            }
            _ => {}
        }
    }

    fn process_impl_item(&mut self, id: hir::ImplItemId) {
        if matches!(self.tcx.def_kind(id.owner_id), DefKind::AssocFn) {
            self.push_if_root(id.owner_id.def_id);
        }
    }

    fn process_nested_body(&mut self, def_id: LocalDefId) {
        match self.tcx.def_kind(def_id) {
            DefKind::Closure => {
                // for 'pub async fn foo(..)' also trying to monomorphize foo::{closure}
                let is_pub_fn_coroutine = match *self
                    .tcx
                    .type_of(def_id)
                    .instantiate_identity()
                    .skip_norm_wip()
                    .kind()
                {
                    ty::Coroutine(cor_id, _args) => {
                        let tcx = self.tcx;
                        let parent_id = tcx.parent(cor_id);
                        tcx.def_kind(parent_id) == DefKind::Fn
                            && tcx.asyncness(parent_id).is_async()
                            && tcx.visibility(parent_id).is_public()
                    }
                    ty::Closure(..) | ty::CoroutineClosure(..) => false,
                    _ => unreachable!(),
                };
                if (self.strategy == MonoItemCollectionStrategy::Eager || is_pub_fn_coroutine)
                    && !self
                        .tcx
                        .generics_of(self.tcx.typeck_root_def_id(def_id.to_def_id()))
                        .requires_monomorphization(self.tcx)
                {
                    let instance = match *self
                        .tcx
                        .type_of(def_id)
                        .instantiate_identity()
                        .skip_norm_wip()
                        .kind()
                    {
                        ty::Closure(def_id, args)
                        | ty::Coroutine(def_id, args)
                        | ty::CoroutineClosure(def_id, args) => {
                            Instance::new_raw(def_id, self.tcx.erase_and_anonymize_regions(args))
                        }
                        _ => unreachable!(),
                    };
                    let Ok(instance) = self.tcx.try_normalize_erasing_regions(
                        ty::TypingEnv::fully_monomorphized(),
                        Unnormalized::new_wip(instance),
                    ) else {
                        // Don't ICE on an impossible-to-normalize closure.
                        return;
                    };
                    let mono_item = create_fn_mono_item(self.tcx, instance, DUMMY_SP);
                    if mono_item.node.is_instantiable(self.tcx) {
                        self.output.push(mono_item);
                    }
                }
            }
            _ => {}
        }
    }

    fn is_root(&self, def_id: LocalDefId) -> bool {
        !self
            .tcx
            .generics_of(def_id)
            .requires_monomorphization(self.tcx)
            && match self.strategy {
                MonoItemCollectionStrategy::Eager => !matches!(
                    self.tcx.codegen_fn_attrs(def_id).inline,
                    InlineAttr::Force { .. }
                ),
                MonoItemCollectionStrategy::Lazy => {
                    self.entry_fn.and_then(|(id, _)| id.as_local()) == Some(def_id)
                        || self.tcx.is_reachable_non_generic(def_id)
                        || self
                            .tcx
                            .codegen_fn_attrs(def_id)
                            .flags
                            .contains(CodegenFnAttrFlags::RUSTC_STD_INTERNAL_SYMBOL)
                }
            }
    }

    /// If `def_id` represents a root, pushes it onto the list of
    /// outputs. (Note that all roots must be monomorphic.)
    fn push_if_root(&mut self, def_id: LocalDefId) {
        if self.is_root(def_id) {
            debug!("found root");

            let instance = Instance::mono(self.tcx, def_id.to_def_id());
            self.output
                .push(create_fn_mono_item(self.tcx, instance, DUMMY_SP));
        }
    }

    /// As a special case, when/if we encounter the
    /// `main()` function, we also have to generate a
    /// monomorphized copy of the start lang item based on
    /// the return type of `main`. This is not needed when
    /// the user writes their own `start` manually.
    fn push_extra_entry_roots(&mut self) {
        let Some((main_def_id, EntryFnType::Main { .. })) = self.entry_fn else {
            return;
        };

        let main_instance = Instance::mono(self.tcx, main_def_id);
        // DIFF: remove should_codegen_locally
        self.output.push(create_fn_mono_item(
            self.tcx,
            main_instance,
            self.tcx.def_span(main_def_id),
        ));

        let start_def_id = self.tcx.require_lang_item(LangItem::Start, DUMMY_SP);
        let main_ret_ty = self
            .tcx
            .fn_sig(main_def_id)
            .no_bound_vars()
            .unwrap()
            .output();

        // Given that `main()` has no arguments,
        // then its return type cannot have
        // late-bound regions, since late-bound
        // regions must appear in the argument
        // listing.
        let main_ret_ty = self.tcx.normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            Unnormalized::new_wip(main_ret_ty.no_bound_vars().unwrap()),
        );

        let start_instance = Instance::expect_resolve(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            start_def_id,
            self.tcx.mk_args(&[main_ret_ty.into()]),
            DUMMY_SP,
        );

        self.output
            .push(create_fn_mono_item(self.tcx, start_instance, DUMMY_SP));
    }
}

fn create_mono_items_for_default_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: hir::ItemId,
    output: &mut MonoItems<'tcx>,
) {
    let impl_ = tcx.impl_trait_header(item.owner_id);

    if matches!(impl_.polarity, ty::ImplPolarity::Negative) {
        return;
    }

    if tcx
        .generics_of(item.owner_id)
        .own_requires_monomorphization()
    {
        return;
    }

    // Lifetimes never affect trait selection, so we are allowed to eagerly
    // instantiate an instance of an impl method if the impl (and method,
    // which we check below) is only parameterized over lifetime. In that case,
    // we use the ReErased, which has no lifetime information associated with
    // it, to validate whether or not the impl is legal to instantiate at all.
    let only_region_params = |param: &ty::GenericParamDef, _: &_| match param.kind {
        GenericParamDefKind::Lifetime => tcx.lifetimes.re_erased.into(),
        GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
            unreachable!(
                "`own_requires_monomorphization` check means that \
                we should have no type/const params"
            )
        }
    };
    let impl_args = GenericArgs::for_item(tcx, item.owner_id.to_def_id(), only_region_params);
    let trait_ref = impl_.trait_ref.instantiate(tcx, impl_args).skip_norm_wip();

    // Unlike 'lazy' monomorphization that begins by collecting items transitively
    // called by `main` or other global items, when eagerly monomorphizing impl
    // items, we never actually check that the predicates of this impl are satisfied
    // in a empty param env (i.e. with no assumptions).
    //
    // Even though this impl has no type or const generic parameters, because we don't
    // consider higher-ranked predicates such as `for<'a> &'a mut [u8]: Copy` to
    // be trivially false. We must now check that the impl has no impossible-to-satisfy
    // clauses.
    if tcx.instantiate_and_check_impossible_clauses((item.owner_id.to_def_id(), impl_args)) {
        return;
    }

    let typing_env = ty::TypingEnv::fully_monomorphized();
    let trait_ref = tcx.normalize_erasing_regions(typing_env, Unnormalized::new_wip(trait_ref));
    let overridden_methods = tcx.impl_item_implementor_ids(item.owner_id);
    for method in tcx.provided_trait_methods(trait_ref.def_id) {
        if overridden_methods.contains_key(&method.def_id) {
            continue;
        }

        if tcx
            .generics_of(method.def_id)
            .own_requires_monomorphization()
        {
            continue;
        }

        // As mentioned above, the method is legal to eagerly instantiate if it
        // only has lifetime generic parameters. This is validated by calling
        // `own_requires_monomorphization` on both the impl and method.
        let args = trait_ref
            .args
            .extend_to(tcx, method.def_id, only_region_params);
        let instance = ty::Instance::expect_resolve(tcx, typing_env, method.def_id, args, DUMMY_SP);

        let mono_item = create_fn_mono_item(tcx, instance, DUMMY_SP);
        // DIFF: remove should_codegen_locally
        if mono_item.node.is_instantiable(tcx) {
            output.push(mono_item);
        }
    }
}

//=-----------------------------------------------------------------------------
// Top-level entry point, tying it all together
//=-----------------------------------------------------------------------------
//
pub fn collect_crate_mono_items(
    tcx: TyCtxt<'_>,
    strategy: MonoItemCollectionStrategy,
) -> (Vec<MonoItem<'_>>, UsageMap<'_>) {
    let _prof_timer = tcx.prof.generic_activity("monomorphization_collector");

    let roots = tcx
        .sess
        .time("monomorphization_collector_root_collections", || {
            collect_roots(tcx, strategy)
        });

    debug!("building mono item graph, beginning at roots");

    let state = SharedState {
        visited: Lock::new(UnordSet::default()),
        mentioned: Lock::new(UnordSet::default()),
        usage_map: Lock::new(UsageMap::new()),
    };
    let recursion_limit = tcx.recursion_limit();

    tcx.sess.time("monomorphization_collector_graph_walk", || {
        par_for_each_in(roots, |root| {
            collect_items_root(tcx, dummy_spanned(*root), &state, recursion_limit);
        });
    });

    // The set of MonoItems was created in an inherently indeterministic order because
    // of parallelism. We sort it here to ensure that the output is deterministic.
    let mono_items = tcx.with_stable_hashing_context(move |mut hcx| {
        state.visited.into_inner().into_sorted(&mut hcx, true)
    });

    (mono_items, state.usage_map.into_inner())
}
