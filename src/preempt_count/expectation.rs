use rustc_hir::def_id::CrateNum;
use rustc_hir::{Constness, LangItem};
use rustc_index::bit_set::BitSet;
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_middle::ty::{self, Instance, InternalSubsts, ParamEnv, ParamEnvAnd, Ty};
use rustc_mir_dataflow::lattice::MeetSemiLattice;
use rustc_mir_dataflow::Analysis;

use super::dataflow::AdjustmentComputation;
use super::{ExpectationRange, PolyDisplay, TooGeneric};
use crate::ctxt::AnalysisCtxt;

impl<'tcx> AnalysisCtxt<'tcx> {
    pub fn infer_expectation(
        &self,
        param_env: ParamEnv<'tcx>,
        instance: Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<ExpectationRange, TooGeneric> {
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

        let mut expectation_infer = ExpectationRange::top();
        for (b, data) in rustc_middle::mir::traversal::reachable(body) {
            if data.is_cleanup {
                continue;
            }

            let expectation = match &data.terminator().kind {
                TerminatorKind::Call { func, .. } => {
                    let callee_ty = func.ty(body, self.tcx);
                    let callee_ty = instance
                        .subst_mir_and_normalize_erasing_regions(self.tcx, param_env, callee_ty);
                    if let ty::FnDef(def_id, substs) = *callee_ty.kind() {
                        let instance = ty::Instance::resolve(self.tcx, param_env, def_id, substs)
                            .unwrap()
                            .ok_or(TooGeneric)?;
                        self.instance_expectation(param_env.and(instance))?
                    } else {
                        self.sess.span_warn(
                            data.terminator().source_info.span,
                            "klint cannot yet check indirect function calls",
                        );
                        ExpectationRange::top()
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let ty = place.ty(body, self.tcx).ty;
                    let ty =
                        instance.subst_mir_and_normalize_erasing_regions(self.tcx, param_env, ty);

                    self.drop_expectation(param_env.and(ty))?
                }
                _ => continue,
            };

            // Special case for no expectation at all. No need to check adjustment here.
            if expectation == ExpectationRange::top() {
                continue;
            }

            analysis_result.seek_to_block_start(b);
            let adjustment = analysis_result.get().into_result()?;

            // We need to find a range that for all possible values in `adj`, it will end up in a value
            // that lands inside `expectation`.
            //
            // For example, if adjustment is `0..`, and range is `0..1`, then the range we want is `0..0`,
            // i.e. an empty range, because no matter what preemption count we start with, if we apply an
            // adjustment >0, then it will be outside the range.
            let mut expected = expectation - adjustment;
            expected.meet(&expectation_infer);
            if expected.is_empty() {
                // This function will cause the entry state to be in an unsatisfiable condition.
                // Generate an error.
                let (kind, drop_span) = match data.terminator().kind {
                    TerminatorKind::Drop { place, .. } => {
                        ("drop", Some(body.local_decls[place.local].source_info.span))
                    }
                    _ => ("call", None),
                };
                let span = data.terminator().source_info.span;
                let mut diag = self.tcx.sess.struct_span_err(
                    span,
                    format!(
                        "this {kind} expects the preemption count to be {}",
                        expectation
                    ),
                );

                if let Some(span) = drop_span {
                    diag.span_label(span, "the value being dropped is declared here");
                }

                diag.note(format!(
                    "but the possible preemption count at this point is {}",
                    expectation_infer + adjustment
                ));
                diag.emit();

                // For failed inference, revert to the default.
                expectation_infer = ExpectationRange::top();

                // Stop processing other calls in this function to avoid generating too many errors.
                break;
            }

            expectation_infer = expected;
        }

        Ok(expectation_infer)
    }
}

memoize!(
    #[instrument(skip(cx), fields(poly_ty = %PolyDisplay(&poly_ty)))]
    fn drop_expectation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_ty: ParamEnvAnd<'tcx, Ty<'tcx>>,
    ) -> Result<ExpectationRange, TooGeneric> {
        let (param_env, ty) = poly_ty.into_parts();

        // If the type doesn't need drop, then there is trivially no expectation.
        if !ty.needs_drop(cx.tcx, param_env) {
            return Ok(ExpectationRange::top());
        }

        match ty.kind() {
            ty::Closure(_, substs) => (),

            // Generator drops are non-trivial, use the generated drop shims instead.
            ty::Generator(..) => (),

            ty::Tuple(list) => (),

            ty::Adt(def, _) => {
                // For Adts, we first try to not use any of the substs and just try the most
                // polymorphic version of the type.
                let poly_param_env = cx.param_env_reveal_all_normalized(def.did());
                let poly_substs =
                    cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, def.did()));
                let poly_poly_ty = poly_param_env.and(cx.tcx.mk_ty(ty::Adt(*def, poly_substs)));
                if poly_poly_ty != poly_ty {
                    if let Ok(expectation) = cx.drop_expectation(poly_poly_ty) {
                        return Ok(expectation);
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
                return Ok(ExpectationRange::top());
            }

            ty::Array(elem_ty, size) => {
                let size = size.try_eval_usize(cx.tcx, param_env).ok_or(TooGeneric);
                if size == Ok(0) {
                    return Ok(ExpectationRange::top());
                }

                let param_and_elem_ty = param_env.and(*elem_ty);
                let elem_adj = cx.drop_adjustment(param_and_elem_ty)?;
                let elem_exp = cx.drop_expectation(param_and_elem_ty)?;
                if elem_adj == 0 {
                    return Ok(elem_exp);
                }

                // TODO: deal with this case without using the MIR based logic.
            }

            ty::Slice(elem_ty) => {
                // We can assume adjustment here is 0 otherwise the adjustment calculation
                // logic would have complained.
                return cx.drop_expectation(param_env.and(*elem_ty));
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
                return Ok(ExpectationRange::top());
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        cx.eval_stack.borrow_mut().push(instance);

        let mir = crate::mir::drop_shim::build_drop_shim(cx.tcx, instance.def_id(), param_env, ty);
        let result = cx.infer_expectation(param_env, instance, &mir);

        // Recursion encountered.
        if let Some(&recur) = cx.query_cache::<drop_expectation>().borrow().get(&poly_ty) {
            match (result, recur) {
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(exp), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        ty.ty_adt_def()
                            .map(|x| cx.def_span(x.did()))
                            .unwrap_or_else(|| cx.def_span(instance.def_id())),
                        "dropping this type causes recursion while also has preemption count expectation",
                    );
                    diag.note(format!("expectation inferred is {}", exp));
                    diag.note(format!("type being dropped is `{}`", ty));
                    diag.emit();
                }
            }
        }

        // if instance.def_id().is_local() && param_env.caller_bounds().is_empty() {
        //     cx.sql_store::<drop_adjustment>(poly_instance, result);
        // }

        cx.eval_stack.borrow_mut().pop();
        result
    }
);

memoize!(
    #[instrument(skip(cx), fields(poly_instance = %PolyDisplay(&poly_instance)))]
    pub fn instance_expectation<'tcx>(
        cx: &AnalysisCtxt<'tcx>,
        poly_instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    ) -> Result<ExpectationRange, TooGeneric> {
        let (param_env, instance) = poly_instance.into_parts();
        match instance.def {
            // No Rust built-in intrinsics will mess with preemption count.
            ty::InstanceDef::Intrinsic(_) => return Ok(ExpectationRange::top()),
            // Empty drop glue, then it definitely won't mess with preemption count.
            ty::InstanceDef::DropGlue(_, None) => return Ok(ExpectationRange::top()),
            ty::InstanceDef::DropGlue(_, Some(ty)) => {
                return cx.drop_expectation(param_env.and(ty))
            }
            ty::InstanceDef::Virtual(..) => {
                cx.sess.span_warn(
                    cx.def_span(instance.def_id()),
                    "klint cannot yet check indirect function calls",
                );
                return Ok(ExpectationRange::top());
            }
            _ => (),
        }

        let poly_param_env = cx
            .param_env_reveal_all_normalized(instance.def_id())
            .with_constness(Constness::NotConst);
        let poly_substs =
            cx.erase_regions(InternalSubsts::identity_for_item(cx.tcx, instance.def_id()));
        let mut generic = false;
        if !cx.trait_of_item(instance.def_id()).is_some() {
            let poly_poly_instance =
                poly_param_env.and(Instance::new(instance.def_id(), poly_substs));
            generic = poly_poly_instance == poly_instance;
            if !generic {
                if let Ok(v) = cx.instance_expectation(poly_poly_instance) {
                    return Ok(v);
                }
            }
        }

        if cx.is_foreign_item(instance.def_id()) {
            return Ok(cx.ffi_property(instance).expectation);
        }

        if !crate::monomorphize_collector::should_codegen_locally(cx.tcx, &instance) {
            if let Some(p) = cx.sql_load::<instance_expectation>(poly_instance) {
                return p;
            }

            warn!(
                "Unable to compute property of non-local function {:?}",
                instance
            );
            return Ok(ExpectationRange::top());
        }

        // Use annotation if available.
        let annotation = cx.preemption_count_annotation(instance.def_id());
        if let Some(exp) = annotation.expectation {
            info!("expectation {} from annotation", exp);
        }

        if cx.eval_stack.borrow().contains(&instance) {
            // Recursion encountered.
            if param_env.caller_bounds().is_empty() {
                return Ok(annotation.expectation.unwrap_or_else(ExpectationRange::top));
            } else {
                // If we are handling generic functions, then defer decision to monomorphization time.
                return Err(TooGeneric);
            }
        }

        cx.eval_stack.borrow_mut().push(instance);

        let mir = cx.analysis_instance_mir(instance.def);
        let result = if !annotation.unchecked || annotation.expectation.is_none() {
            let infer_result = cx.infer_expectation(param_env, instance, mir);
            if let Ok(expectation_infer) = infer_result {
                // Check if the inferred expectation matches the annotation.
                if let Some(expectation) = annotation.expectation {
                    let mut expectation_intersect = expectation_infer;
                    expectation_intersect.meet(&expectation);
                    if expectation_intersect != expectation {
                        let mut diag = cx.sess.struct_span_err(
                            cx.def_span(instance.def_id()),
                            format!(
                                "function annotated to have preemption count expectation of {}",
                                expectation
                            ),
                        );
                        diag.note(format!(
                            "but the expectation inferred is {expectation_infer}"
                        ));
                        diag.emit();
                    }
                    Ok(expectation)
                } else {
                    Ok(expectation_infer)
                }
            } else {
                infer_result
            }
        } else {
            Ok(annotation.expectation.unwrap())
        };

        // Addition check for FFI functions.
        // Verify that the inferred result is compatible with the FFI list.
        if let Ok(exp) = result && cx
            .codegen_fn_attrs(instance.def_id())
            .contains_extern_indicator()
        {
            // Verify that the inferred result is compatible with the FFI list.
            let ffi_property = cx.ffi_property(instance);

            // Check using the intersection -- the FFI property is allowed to be more restrictive.
            let mut expectation_intersect = exp;
            expectation_intersect.meet(&ffi_property.expectation);
            if expectation_intersect != ffi_property.expectation {
                let mut diag = cx.sess.struct_span_err(
                    cx.def_span(instance.def_id()),
                    format!(
                        "extern function `{}` must have preemption count expectation {}",
                        cx.def_path_str(instance.def_id()),
                        ffi_property.expectation,
                    ),
                );
                diag.note(format!(
                    "preemption count expectation inferred is {exp}",
                ));
                diag.emit();
            }
        }

        // Recursion encountered.
        if let Some(recur) = cx
            .query_cache::<instance_expectation>()
            .borrow()
            .get(&poly_instance)
        {
            match (result, recur) {
                (Err(_), Err(_)) => (),
                (Ok(a), Ok(b)) if a == *b => (),
                (Ok(_), Err(_)) => bug!("recursive callee too generic but caller is not"),
                (Err(_), Ok(_)) => bug!("monormorphic caller too generic"),
                (Ok(_), Ok(_)) if annotation.expectation.is_some() => {
                    bug!("recursive outcome does not match annotation")
                }
                (Ok(exp), Ok(_)) => {
                    let mut diag = cx.sess.struct_span_err(
                        cx.def_span(instance.def_id()),
                        "this function is recursive but preemption count expectation is not 0..",
                    );
                    diag.note(format!("expectation is inferred to be {}", exp));
                    diag.note(format!(
                        "instance being checked is `{}`",
                        PolyDisplay(&poly_instance)
                    ));
                    diag.help(format!(
                        "try annotate the function with `#[klint::preempt_count(expect = {exp})]`"
                    ));
                    diag.emit();
                }
            }
        }

        if instance.def_id().is_local() && (generic || param_env.caller_bounds().is_empty()) {
            cx.sql_store::<instance_expectation>(poly_instance, result);
        }

        if cx.should_report_preempt_count(instance.def_id()) {
            let mut diag = cx.sess.diagnostic().struct_note_without_error(format!(
                "reporting preemption count for instance `{}`",
                PolyDisplay(&poly_instance)
            ));
            diag.set_span(cx.def_span(instance.def_id()));
            if let Ok(property) = result {
                diag.note(format!("expectation is inferred to be {}", property));
            } else {
                diag.note("expectation inference failed because this function is too generic");
            }
            diag.emit();
        }

        cx.eval_stack.borrow_mut().pop();
        result
    }
);

impl crate::ctxt::PersistentQuery for instance_expectation {
    type LocalKey<'tcx> = Instance<'tcx>;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        let instance = key.value;
        (instance.def_id().krate, instance)
    }
}
