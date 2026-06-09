// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_hir::{self as hir, def::DefKind};
use rustc_middle::mir::CallSource;
use rustc_middle::mir::{
    Body, ConstOperand, LocalDecl, Operand, Place, ProjectionElem, Rvalue, SourceInfo, Statement,
    StatementKind, TerminatorKind, WithRetag,
};
use rustc_middle::ty::{self, EarlyBinder, Ty, TyCtxt, TypingEnv};
use rustc_span::def_id::{CrateNum, DefId, DefIndex, LocalDefId};
use rustc_span::{DUMMY_SP, Spanned, sym};

use crate::ctxt::AnalysisCtxt;
use crate::ctxt::PersistentQuery;

pub fn local_analysis_mir<'tcx>(cx: &AnalysisCtxt<'tcx>, did: LocalDefId) -> &'tcx Body<'tcx> {
    if cx.is_constructor(did.to_def_id()) {
        return cx.optimized_mir(did.to_def_id());
    }

    let body = cx
        .mir_drops_elaborated_and_const_checked(did)
        .borrow()
        .clone();
    let body = remap_mir_for_const_eval_select(cx.tcx, body, hir::Constness::NotConst);
    cx.arena.alloc(body)
}

// Copied from rustc_mir_transform/src/lib.rs.
// This function was not public so we have to reproduce it here.
fn remap_mir_for_const_eval_select<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut body: Body<'tcx>,
    context: hir::Constness,
) -> Body<'tcx> {
    for bb in body.basic_blocks.as_mut().iter_mut() {
        let terminator = bb.terminator.as_mut().expect("invalid terminator");
        match terminator.kind {
            TerminatorKind::Call {
                func: Operand::Constant(box ConstOperand { ref const_, .. }),
                ref mut args,
                destination,
                target,
                unwind,
                fn_span,
                ..
            } if let ty::FnDef(def_id, _) = *const_.ty().kind()
                && tcx.is_intrinsic(def_id, sym::const_eval_select) =>
            {
                let Ok([tupled_args, called_in_const, called_at_rt]) = take_array(args) else {
                    unreachable!()
                };
                let ty = tupled_args.node.ty(&body.local_decls, tcx);
                let fields = ty.tuple_fields();
                let num_args = fields.len();
                let func = match context {
                    // Using `const_eval_select` in always-const code is useful when used in macros
                    // that you don't know whether they are going to be used in `const fn` or in `const` items.
                    hir::Constness::Const { .. } => called_in_const,
                    hir::Constness::NotConst => called_at_rt,
                };
                let (method, place): (fn(Place<'tcx>) -> Operand<'tcx>, Place<'tcx>) =
                    match tupled_args.node {
                        Operand::Constant(_) | Operand::RuntimeChecks(_) => {
                            // there is no good way of extracting a tuple arg from a constant (const generic stuff)
                            // so we just create a temporary and deconstruct that.
                            let local = body.local_decls.push(LocalDecl::new(ty, fn_span));
                            bb.statements.push(Statement::new(
                                SourceInfo::outermost(fn_span),
                                StatementKind::Assign(Box::new((
                                    local.into(),
                                    Rvalue::Use(tupled_args.node.clone(), WithRetag::Yes),
                                ))),
                            ));
                            (Operand::Move, local.into())
                        }
                        Operand::Move(place) => (Operand::Move, place),
                        Operand::Copy(place) => (Operand::Copy, place),
                    };
                let place_elems = place.projection;
                let arguments = (0..num_args)
                    .map(|x| {
                        let mut place_elems = place_elems.to_vec();
                        place_elems.push(ProjectionElem::Field(x.into(), fields[x]));
                        let projection = tcx.mk_place_elems(&place_elems);
                        let place = Place {
                            local: place.local,
                            projection,
                        };
                        Spanned {
                            node: method(place),
                            span: DUMMY_SP,
                        }
                    })
                    .collect();
                terminator.kind = TerminatorKind::Call {
                    func: func.node,
                    args: arguments,
                    destination,
                    target,
                    unwind,
                    call_source: CallSource::Misc,
                    fn_span,
                };
            }
            _ => {}
        }
    }
    body
}

fn take_array<T, const N: usize>(b: &mut Box<[T]>) -> Result<[T; N], Box<[T]>> {
    let b: Box<[T; N]> = std::mem::take(b).try_into()?;
    Ok(*b)
}

memoize!(
    pub fn analysis_mir<'tcx>(cx: &AnalysisCtxt<'tcx>, def_id: DefId) -> &'tcx Body<'tcx> {
        if let Some(local_def_id) = def_id.as_local() {
            local_analysis_mir(cx, local_def_id)
        } else if let Some(mir) = cx.sql_load_with_span::<analysis_mir>(def_id, cx.def_span(def_id))
        {
            mir
        } else {
            cx.optimized_mir(def_id)
        }
    }
);

impl PersistentQuery for analysis_mir {
    type LocalKey<'tcx> = DefIndex;

    fn into_crate_and_local<'tcx>(key: Self::Key<'tcx>) -> (CrateNum, Self::LocalKey<'tcx>) {
        (key.krate, key.index)
    }
}

pub fn build_drop_shim<'tcx>(
    cx: &AnalysisCtxt<'tcx>,
    def_id: DefId,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Body<'tcx> {
    // TODO: Replicate coroutine handling in rustc_mir_transform/shim.rs
    if let ty::Coroutine(gen_def_id, args) = ty.kind() {
        let body = cx.analysis_mir(*gen_def_id).coroutine_drop().unwrap();
        let body = EarlyBinder::bind(body.clone()).instantiate(cx.tcx, args);
        return body.skip_norm_wip();
    }

    rustc_mir_transform::build_drop_shim(cx.tcx, def_id, Some(ty), typing_env)
}

impl<'tcx> AnalysisCtxt<'tcx> {
    /// Save all MIRs defined in the current crate to the database.
    pub fn encode_mir(&self) {
        let tcx = self.tcx;
        for &def_id in tcx.mir_keys(()) {
            // Use the same logic as rustc use to determine if the MIR is needed for
            // downstream crates.
            let should_encode = match tcx.def_kind(def_id) {
                DefKind::Ctor(_, _) => true,
                DefKind::Closure if tcx.is_coroutine(def_id.to_def_id()) => true,
                DefKind::AssocFn | DefKind::Fn | DefKind::Closure => {
                    let generics = tcx.generics_of(def_id);
                    let needs_inline = generics.requires_monomorphization(tcx)
                        || tcx.cross_crate_inlinable(def_id);
                    needs_inline
                }
                _ => false,
            };

            if should_encode {
                let mir = self.analysis_mir(def_id.into());
                self.sql_store_with_span::<analysis_mir>(def_id.into(), mir, tcx.def_span(def_id));
            }
        }
    }

    pub fn analysis_instance_mir(&self, instance: ty::InstanceKind<'tcx>) -> &'tcx Body<'tcx> {
        match instance {
            ty::InstanceKind::Item(did) => {
                let def_kind = self.def_kind(did);
                match def_kind {
                    DefKind::Const { .. }
                    | DefKind::Static { .. }
                    | DefKind::AssocConst { .. }
                    | DefKind::Ctor(..)
                    | DefKind::AnonConst
                    | DefKind::InlineConst => self.mir_for_ctfe(did),
                    _ => self.analysis_mir(did),
                }
            }
            ty::InstanceKind::VTableShim(..)
            | ty::InstanceKind::ReifyShim(..)
            | ty::InstanceKind::Intrinsic(..)
            | ty::InstanceKind::FnPtrShim(..)
            | ty::InstanceKind::Virtual(..)
            | ty::InstanceKind::ClosureOnceShim { .. }
            | ty::InstanceKind::ConstructCoroutineInClosureShim { .. }
            | ty::InstanceKind::DropGlue(..)
            | ty::InstanceKind::CloneShim(..)
            | ty::InstanceKind::ThreadLocalShim(..)
            | ty::InstanceKind::FutureDropPollShim(..)
            | ty::InstanceKind::FnPtrAddrShim(..)
            | ty::InstanceKind::AsyncDropGlueCtorShim(..)
            | ty::InstanceKind::AsyncDropGlue(..) => self.mir_shims(instance),
        }
    }
}
