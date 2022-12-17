use rustc_errors::{DiagnosticBuilder, EmissionGuarantee, MultiSpan};
use rustc_hir::def_id::CrateNum;
use rustc_hir::{Constness, LangItem};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, Ty};
use rustc_mir_dataflow::Analysis;
use rustc_mir_dataflow::JoinSemiLattice;

use super::dataflow::{AdjustmentBoundsOrError, AdjustmentComputation};
use super::*;
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    fn drop_adjustment_overflow(
        &self,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<i32, TooGeneric> {
        let diag = self.sess.struct_err(format!(
            "preemption count overflow when trying to compute adjustment of type `{}",
            PolyDisplay(&poly_ty)
        ));
        self.emit_with_use_site_info(diag);
        return Ok(0);
    }

    pub fn emit_with_use_site_info<G: EmissionGuarantee>(
        &self,
        mut diag: DiagnosticBuilder<'tcx, G>,
    ) -> G {
        for site in self.call_stack.borrow().iter().rev() {
            match &site.kind {
                UseSiteKind::Call(span) => {
                    if diag.span.is_dummy() {
                        diag.set_span(*span);
                    } else {
                        diag.span_note(*span, "which is called from here");
                    }
                }
                UseSiteKind::Drop {
                    drop_span,
                    place_span,
                } => {
                    let mut multispan = MultiSpan::from_span(*drop_span);
                    multispan.push_span_label(*place_span, "value being dropped is here");
                    if diag.span.is_dummy() {
                        diag.set_span(multispan);
                    } else {
                        diag.span_note(multispan, "which is dropped here");
                    }
                }
            }
        }
        diag.emit()
    }

    fn report_adjustment_infer_error<'mir>(
        &self,
        instance: Instance<'tcx>,
        body: &'mir Body<'tcx>,
        results: &mut rustc_mir_dataflow::ResultsCursor<
            'mir,
            'tcx,
            AdjustmentComputation<'mir, 'tcx, '_>,
        >,
    ) {
        // First step, see if there are any path that leads to a `return` statement have `Top` directly.
        let mut return_bb = None;
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => (),
                _ => continue,
            }

            results.seek_to_block_start(b);
            // We can unwrap here because if this function is called, we know that no paths to `Return`
            // can contain `TooGeneric` or `Error` otherwise we would have returned early (in caller).
            if results.get().unwrap().is_single_value().is_some() {
                continue;
            }

            return_bb = Some(b);
            break;
        }

        // A catch-all error. MIR building usually should just have one `Return` terminator
        // so this usually shouldn't happen.
        let Some(return_bb) = return_bb else {
            self.emit_with_use_site_info(self.tcx
                .sess
                .struct_span_err(
                    self.tcx.def_span(instance.def_id()),
                    "cannot infer preemption count adjustment of this function",
                ));

            return;
        };

        // Find the deepest single-value block in the dominator tree.
        let mut first_problematic_block = return_bb;
        let dominators = body.basic_blocks.dominators();
        loop {
            let b = dominators.immediate_dominator(first_problematic_block);
            if b == first_problematic_block {
                // Shouldn't actually happen because the entry block should always have a single value.
                break;
            }

            results.seek_to_block_start(b);
            if results.get().unwrap().is_single_value().is_some() {
                break;
            }
            first_problematic_block = b;
        }

        // For this problematic block, try use a span that closest to the beginning of it.
        let span = body.basic_blocks[first_problematic_block]
            .statements
            .first()
            .map(|x| x.source_info.span)
            .unwrap_or_else(|| {
                body.basic_blocks[first_problematic_block]
                    .terminator()
                    .source_info
                    .span
            });

        let mut diag = self.tcx.sess.struct_span_err(
            span,
            "cannot infer preemption count adjustment at this point",
        );

        let mut count = 0;
        for mut prev_block in body.basic_blocks.predecessors()[first_problematic_block]
            .iter()
            .copied()
        {
            results.seek_to_block_end(prev_block);
            let mut end_adjustment = results.get().unwrap();
            results.seek_to_block_start(prev_block);
            let mut start_adjustment = results.get().unwrap();

            // If this block has made no changes to the adjustment, backtrack to the predecessors block
            // that made the change.
            while start_adjustment == end_adjustment {
                let pred = &body.basic_blocks.predecessors()[prev_block];

                // Don't continue backtracking if there are multiple predecessors.
                if pred.len() != 1 {
                    break;
                }
                let b = pred[0];

                // Don't continue backtracking if the predecessor block has multiple successors.
                let terminator = body.basic_blocks[b].terminator();
                let successor_count = terminator.successors().count();
                let has_unwind = terminator.unwind().map(|x| x.is_some()).unwrap_or(false);
                let normal_successor = successor_count - has_unwind as usize;
                if normal_successor != 1 {
                    break;
                }

                prev_block = b;
                results.seek_to_block_end(prev_block);
                end_adjustment = results.get().unwrap();
                results.seek_to_block_start(prev_block);
                start_adjustment = results.get().unwrap();
            }

            let terminator = body.basic_blocks[prev_block].terminator();
            let span = match terminator.kind {
                TerminatorKind::Goto { .. } => {
                    // Goto terminator of `if .. { .. } else { .. }` has span on the entire expression,
                    // which is not very useful.
                    // In this case we use the last statement's span instead.
                    body.basic_blocks[prev_block]
                        .statements
                        .last()
                        .map(|x| x.source_info)
                        .unwrap_or_else(|| terminator.source_info)
                        .span
                }
                _ => terminator.source_info.span,
            };

            let mut msg = match start_adjustment.is_single_value() {
                None => {
                    format!("preemption count adjustment is changed in the previous iteration of the loop")
                }
                Some(_) => {
                    format!(
                        "preemption count adjustment is {:?} after this",
                        end_adjustment
                    )
                }
            };

            match count {
                0 => (),
                1 => msg = format!("while {}", msg),
                _ => msg = format!("and {}", msg),
            }
            count += 1;
            diag.span_note(span, msg);
        }
        self.emit_with_use_site_info(diag);
    }

    pub fn infer_adjustment(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<i32, TooGeneric> {
        if false {
            rustc_middle::mir::pretty::write_mir_fn(
                self.tcx,
                body,
                &mut |_, _| Ok(()),
                &mut std::io::stderr(),
            )
            .unwrap();
        }

        let mut analysis_result = AdjustmentComputation {
            checker: self,
            body,
            param_env,
            instance,
        }
        .into_engine(self.tcx, body)
        .dead_unwinds(&BitSet::new_filled(body.basic_blocks.len()))
        .iterate_to_fixpoint()
        .into_results_cursor(body);

        let mut adjustment = AdjustmentBoundsOrError::default();
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            match data.terminator().kind {
                TerminatorKind::Return => {
                    adjustment.join(&analysis_result.results().entry_set_for_block(b));
                }
                _ => (),
            }
        }
        let adjustment = adjustment.into_result()?;

        let adjustment = if adjustment.is_empty() {
            // Diverging function, any value is fine, use the default 0.
            0
        } else if let Some(v) = adjustment.is_single_value() {
            v
        } else {
            self.report_adjustment_infer_error(instance, body, &mut analysis_result);
            0
        };

        Ok(adjustment)
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)), ret)]
    pub fn drop_adjustment<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<i32, TooGeneric> {
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no adjustment.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(0);
        }

        match ty.kind() {
            ty::Closure(_, substs) => {
                return cx.drop_adjustment(param_env.and(substs.as_closure().tupled_upvars_ty()));
            }

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(list) => {
                let mut adj = 0i32;
                for elem_ty in list.iter() {
                    let elem_adj = cx.drop_adjustment(param_env.and(elem_ty))?;
                    let Some(new_adj) = adj.checked_add(elem_adj) else { return cx.drop_adjustment_overflow(poly_ty); };
                    adj = new_adj;
                }
                return Ok(adj);
            }

            ty::Adt(def, substs) if def.is_box() => {
                let adj = cx.drop_adjustment(param_env.and(substs.type_at(0)))?;
                let box_free = cx.require_lang_item(LangItem::BoxFree, None);
                let box_free_adj =
                    cx.instance_adjustment(param_env.and(Instance::new(box_free, substs)))?;
                let Some(adj) = adj.checked_add(box_free_adj) else { return cx.drop_adjustment_overflow(poly_ty); };
                return Ok(adj);
            }

            ty::Adt(def, _) => {
                // For Adts, we first try to not use any of the substs and just try the most
                // polymorphic version of the type.
                let poly_param_env = cx.param_env_reveal_all_normalized(def.did());
                let poly_substs =
                    cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, def.did()));
                let poly_poly_ty = poly_param_env.and(cx.tcx.mk_ty(ty::Adt(*def, poly_substs)));
                if poly_poly_ty != poly_ty {
                    if let Ok(adjustment) = cx.drop_adjustment(poly_poly_ty) {
                        return Ok(adjustment);
                    }
                }

                // If that fails, we try to use the substs.
                // Fallthrough to the MIR drop shim based logic.
            }

            ty::Dynamic(..) => {
                cx.emit_with_use_site_info(cx.sess.struct_warn(format!(
                    "klint cannot yet check drop of dynamically sized `{}`",
                    PolyDisplay(&poly_ty)
                )));
                return Ok(0);
            }

            ty::Array(elem_ty, size) => {
                let size = size.try_eval_usize(cx.tcx, param_env).ok_or(TooGeneric);
                if size == Ok(0) {
                    return Ok(0);
                }
                let elem_adj = cx.drop_adjustment(param_env.and(*elem_ty))?;
                if elem_adj == 0 {
                    return Ok(0);
                }
                let Ok(size) = i32::try_from(size?) else { return cx.drop_adjustment_overflow(poly_ty); };
                let Some(adj) = size.checked_mul(elem_adj) else { return cx.drop_adjustment_overflow(poly_ty); };
                return Ok(adj);
            }

            ty::Slice(elem_ty) => {
                let elem_adj = cx.drop_adjustment(param_env.and(*elem_ty))?;
                if elem_adj != 0 {
                    let mut diag = cx.sess.struct_err(
                        "dropping element of slice causes non-zero preemption count adjustment",
                    );
                    diag.note(format!(
                        "adjustment for dropping `{}` is {}",
                        elem_ty, elem_adj
                    ));
                    diag.note(
                        "because slice can contain variable number of elements, adjustment \
                               for dropping the slice cannot be computed statically",
                    );
                    cx.emit_with_use_site_info(diag);
                }
                return Ok(0);
            }

            _ => return Err(TooGeneric),
        }

        // Do not call `resolve_drop_in_place` because we need param_env.
        let drop_in_place = cx.require_lang_item(LangItem::DropInPlace, None);
        let substs = cx.intern_substs(&[ty.into()]);
        let instance = ty::Instance::resolve(cx.tcx, param_env, drop_in_place, substs)
            .unwrap()
            .unwrap();
        let poly_instance = param_env.and(instance);

        assert!(matches!(
            instance.def,
            ty::InstanceDef::DropGlue(_, Some(_))
        ));

        if cx
            .call_stack
            .borrow()
            .iter()
            .rev()
            .any(|x| x.instance == poly_instance)
        {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(0);
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        let mir = crate::mir::drop_shim::build_drop_shim(cx.tcx, instance.def_id(), param_env, ty);
        let result = cx.infer_adjustment(param_env, instance, &mir);

        // Recursion encountered.
        if let Some(&recur) = cx.query_cache::<drop_adjustment>().borrow().get(&poly_ty) {
            match (result, recur) {
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(adj), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        ty.ty_adt_def()
                            .map(|x| cx.def_span(x.did()))
                            .unwrap_or_else(|| cx.def_span(instance.def_id())),
                        "dropping this type causes recursion but preemption count adjustment is not 0",
                    );
                    diag.note(format!("adjustment is inferred to be {}", adj));
                    diag.note(format!("type being dropped is `{}`", ty));
                    diag.emit();
                }
            }
        }

        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)), ret)]
    pub fn instance_adjustment<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<i32, TooGeneric> {
        let (param_env, instance) = poly_instance.into_parts();
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(0),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(0),
            ty::InstanceDef::DropGlue(_, Some(ty)) => return cx.drop_adjustment(param_env.and(ty)),
            ty::InstanceDef::Virtual(def_id, _) => {
                if let Some(adj) = cx.preemption_count_annotation(def_id).adjustment {
                    return Ok(adj);
                }

                cx.emit_with_use_site_info(cx.sess.struct_span_warn(
                    cx.def_span(instance.def_id()),
                    "klint cannot yet check indirect function calls without preemption count annotation",
                ));
                return Ok(0);
            }
            _ => (),
        }

        let mut generic = false;
        if matches!(instance.def, ty::InstanceDef::Item(_)) {
            let poly_param_env = cx
                .param_env_reveal_all_normalized(instance.def_id())
                .with_constness(Constness::NotConst);
            let poly_substs =
                cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, instance.def_id()));
            let poly_poly_instance =
                poly_param_env.and(Instance::new(instance.def_id(), poly_substs));
            generic = poly_poly_instance == poly_instance;
            if !generic {
                if let Ok(v) = cx.instance_adjustment(poly_poly_instance) {
                    return Ok(v);
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            return Ok(cx.ffi_property(instance).adjustment);
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.sql_load::<instance_adjustment>(poly_instance) {
                return p;
            }

            warn!(
                "Unable to compute adjustment of non-local function {:?}",
                instance
            );
            return Ok(0);
        }

        // Use annotation if available.
        let annotation = cx.preemption_count_annotation(instance.def_id());
        if let Some(adj) = annotation.adjustment {
            info!("adjustment {} from annotation", adj);
        }

        if cx
            .call_stack
            .borrow()
            .iter()
            .rev()
            .any(|x| x.instance == poly_instance)
        {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(annotation.adjustment.unwrap_or(0));
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        let mir = cx.analysis_instance_mir(instance.def);
        let result = if !annotation.unchecked || annotation.adjustment.is_none() {
            let infer_result = cx.infer_adjustment(param_env, instance, mir);
            if let Ok(adjustment_infer) = infer_result {
                // Check if the inferred adjustment matches the annotation.
                if let Some(adjustment) = annotation.adjustment {
                    if adjustment != adjustment_infer {
                        let mut diag = cx.sess.struct_span_err(
                            cx.def_span(instance.def_id()),
                            format!("function annotated to have preemption count adjustment of {adjustment}"),
                        );
                        diag.note(format!("but the adjustment inferred is {adjustment_infer}"));
                        cx.emit_with_use_site_info(diag);
                    }
                    Ok(adjustment)
                } else {
                    Ok(adjustment_infer)
                }
            } else {
                infer_result
            }
        } else {
            Ok(annotation.adjustment.unwrap())
        };

        // Addition check for trait impl methods.
        if let Ok(adj) = result &&
            matches!(instance.def, ty::InstanceDef::Item(_)) &&
            let Some(impl_) = cx.impl_of_method(instance.def_id()) &&
            let Some(trait_) = cx.trait_id_of_impl(impl_)
        {
            let trait_def = cx.trait_def(trait_);
            let trait_item = cx
                .associated_items(impl_)
                .in_definition_order()
                .find(|x| x.def_id == instance.def_id())
                .unwrap()
                .trait_item_def_id
                .unwrap();
            for ancestor in trait_def.ancestors(cx.tcx, impl_).unwrap() {
                let Some(ancestor_item) = ancestor.item(cx.tcx, trait_item) else { continue };
                if let Some(ancestor_adj) = cx.preemption_count_annotation(ancestor_item.def_id).adjustment {
                    if adj != ancestor_adj {
                        let mut diag = cx.sess.struct_span_err(
                            cx.def_span(instance.def_id()),
                            format!("trait method annotated to have preemption count adjustment of {ancestor_adj}"),
                        );
                        diag.note(format!("but the adjustment of this implementing function is {adj}"));
                        diag.span_note(cx.def_span(ancestor_item.def_id), "the trait method is defined here");
                        cx.emit_with_use_site_info(diag);
                    }
                }
            }
        }

        // Addition check for FFI functions.
        // Verify that the inferred result is compatible with the FFI list.
        if let Ok(adj) = result && cx
            .codegen_fn_attrs(instance.def_id())
            .contains_extern_indicator()
        {
            // Verify that the inferred result is compatible with the FFI list.
            let ffi_property = cx.ffi_property(instance);

            if adj != ffi_property.adjustment {
                let mut diag = cx.tcx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "extern function `{}` must have preemption count adjustment {}",
                        cx.def_path_str(instance.def_id()),
                        ffi_property.adjustment,
                    ),
                );
                diag.note(format!(
                    "preemption count adjustment inferred is {adj}",
                ));
                diag.emit();
            }
        }

        // Recursion encountered.
        if let Some(&recur) = cx
            .query_cache::<instance_adjustment>()
            .borrow()
            .get(&poly_instance)
        {
            match (result, recur) {
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(_), Ok(_)) if annotation.adjustment.is_some() => {
                    bug!("recursive outcome does not match annotation")
                }
                (Ok(adj), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        cx.def_span(instance.def_id()),
                        "this function is recursive but preemption count adjustment is not 0",
                    );
                    diag.note(format!("adjustment is inferred to be {}", adj));
                    if !generic {
                        diag.note(format!(
                            "instance being checked is `{}`",
                            PolyDisplay(&poly_instance)
                        ));
                    }
                    diag.help(format!(
                        "try annotate the function with `#[klint::preempt_count(adjust = {adj})]`"
                    ));
                    diag.emit();
                }
            }
        }

        if instance.def_id().is_local() && (generic || param_env.caller_bounds().is_empty()) {
            cx.sql_store::<instance_adjustment>(poly_instance, result);
        }

        if cx.should_report_preempt_count(instance.def_id()) {
            let mut diag = cx.sess.diagnostic().struct_note_without_error(format!(
                "reporting preemption count for instance `{}`",
                PolyDisplay(&poly_instance)
            ));
            diag.set_span(cx.def_span(instance.def_id()));
            if let Ok(property) = result {
                diag.note(format!("adjustment is inferred to be {}", property));
            } else {
                diag.note("adjustment inference failed because this function is too generic");
            }
            diag.emit();
        }

        result
    }
);

impl crate::ctxt::PersistentQuery for instance_adjustment {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}
