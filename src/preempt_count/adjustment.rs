use rustc_hir::LangItem;
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
        let mut diag = self.sess.struct_err(format!(
            "preemption count overflow when trying to compute adjustment of type `{}",
            PolyDisplay(&poly_ty)
        ));
        diag.emit();
        return Ok(0);
    }

    fn report_preempt_count_adjustment_infer_error<'mir>(
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
            self.tcx
                .sess
                .struct_span_err(
                    self.tcx.def_span(instance.def_id()),
                    "cannot infer preemption count adjustment of this function",
                )
                .emit();

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
        diag.emit();
    }

    pub fn infer_preempt_count_adjustment(
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
            self.report_preempt_count_adjustment_infer_error(instance, body, &mut analysis_result);
            0
        };

        Ok(adjustment)
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)))]
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
                let mut adj = 0i32;
                for elem_ty in substs.as_closure().upvar_tys() {
                    let elem_adj = cx.drop_adjustment(param_env.and(elem_ty))?;
                    let Some(new_adj) = adj.checked_add(elem_adj) else { return cx.drop_adjustment_overflow(poly_ty); };
                    adj = new_adj;
                }
                return Ok(adj);
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
                cx.sess.warn(format!(
                    "klint cannot yet check drop of dynamically sized `{}`",
                    PolyDisplay(&poly_ty)
                ));
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
                    // TODO: will be more helpful if we can point to the place of drop
                    diag.emit();
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

        assert!(matches!(
            instance.def,
            ty::InstanceDef::DropGlue(_, Some(_))
        ));

        if cx.eval_stack.borrow().contains(&instance) {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(0);
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        cx.eval_stack.borrow_mut().push(instance);

        let mir = crate::mir::drop_shim::build_drop_shim(cx.tcx, instance.def_id(), param_env, ty);
        let result = cx.infer_preempt_count_adjustment(param_env, instance, &mir);

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

        cx.eval_stack.borrow_mut().pop();
        result
    }
);
