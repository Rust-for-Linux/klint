use std::sync::atomic::AtomicPtr;
use std::sync::atomic::Ordering;
use std::sync::{LazyLock, Mutex};

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{self as hir, def::DefKind};
use rustc_middle::mir::{
    Body, Constant, LocalDecl, Operand, Place, ProjectionElem, Rvalue, SourceInfo, Statement,
    StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
use rustc_span::sym;

// HACK: we can't add new queries to `TyCtxt` without changing rustc code, so
// use this as a "poor man's query" for now.
static MIR_CACHE: LazyLock<Mutex<FxHashMap<LocalDefId, AtomicPtr<()>>>> =
    LazyLock::new(|| Mutex::new(FxHashMap::default()));

pub fn analysis_mir<'tcx>(tcx: TyCtxt<'tcx>, did: DefId) -> &'tcx Body<'tcx> {
    match did.as_local() {
        Some(local_def_id) => local_analysis_mir(tcx, local_def_id),
        None => tcx.optimized_mir(did),
    }
}

pub fn analysis_instance_mir<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::InstanceDef<'tcx>,
) -> &'tcx Body<'tcx> {
    match instance {
        ty::InstanceDef::Item(def) => {
            let def_kind = tcx.def_kind(def.did);
            match def_kind {
                DefKind::Const
                | DefKind::Static(..)
                | DefKind::AssocConst
                | DefKind::Ctor(..)
                | DefKind::AnonConst
                | DefKind::InlineConst => tcx.mir_for_ctfe_opt_const_arg(def),
                _ => {
                    assert_eq!(def.const_param_did, None);
                    analysis_mir(tcx, def.did)
                }
            }
        }
        ty::InstanceDef::VTableShim(..)
        | ty::InstanceDef::ReifyShim(..)
        | ty::InstanceDef::Intrinsic(..)
        | ty::InstanceDef::FnPtrShim(..)
        | ty::InstanceDef::Virtual(..)
        | ty::InstanceDef::ClosureOnceShim { .. }
        | ty::InstanceDef::DropGlue(..)
        | ty::InstanceDef::CloneShim(..) => tcx.mir_shims(instance),
    }
}

fn local_analysis_mir<'tcx>(tcx: TyCtxt<'tcx>, did: LocalDefId) -> &'tcx Body<'tcx> {
    if tcx.is_constructor(did.to_def_id()) {
        return tcx.optimized_mir(did.to_def_id());
    }

    let mut cache = MIR_CACHE.lock().unwrap();
    if let Some(body) = cache.get(&did) {
        return unsafe { &*body.load(Ordering::Relaxed).cast() };
    }

    let body = tcx
        .mir_drops_elaborated_and_const_checked(ty::WithOptConstParam::unknown(did))
        .borrow()
        .clone();
    let body = remap_mir_for_const_eval_select(tcx, body, hir::Constness::NotConst);
    let body = tcx.arena.alloc(body);

    cache.insert(did, AtomicPtr::new(body as *const _ as *mut _));
    body
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
                func: Operand::Constant(box Constant { ref literal, .. }),
                ref mut args,
                destination,
                target,
                cleanup,
                fn_span,
                ..
            } if let ty::FnDef(def_id, _) = *literal.ty().kind()
                && tcx.item_name(def_id) == sym::const_eval_select
                && tcx.is_intrinsic(def_id) =>
            {
                let [tupled_args, called_in_const, called_at_rt]: [_; 3] = std::mem::take(args).try_into().unwrap();
                let ty = tupled_args.ty(&body.local_decls, tcx);
                let fields = ty.tuple_fields();
                let num_args = fields.len();
                let func = if context == hir::Constness::Const { called_in_const } else { called_at_rt };
                let (method, place): (fn(Place<'tcx>) -> Operand<'tcx>, Place<'tcx>) = match tupled_args {
                    Operand::Constant(_) => {
                        // there is no good way of extracting a tuple arg from a constant (const generic stuff)
                        // so we just create a temporary and deconstruct that.
                        let local = body.local_decls.push(LocalDecl::new(ty, fn_span));
                        bb.statements.push(Statement {
                            source_info: SourceInfo::outermost(fn_span),
                            kind: StatementKind::Assign(Box::new((local.into(), Rvalue::Use(tupled_args.clone())))),
                        });
                        (Operand::Move, local.into())
                    }
                    Operand::Move(place) => (Operand::Move, place),
                    Operand::Copy(place) => (Operand::Copy, place),
                };
                let place_elems = place.projection;
                let arguments = (0..num_args).map(|x| {
                    let mut place_elems = place_elems.to_vec();
                    place_elems.push(ProjectionElem::Field(x.into(), fields[x]));
                    let projection = tcx.intern_place_elems(&place_elems);
                    let place = Place {
                        local: place.local,
                        projection,
                    };
                    method(place)
                }).collect();
                terminator.kind = TerminatorKind::Call { func, args: arguments, destination, target, cleanup, from_hir_call: false, fn_span };
            }
            _ => {}
        }
    }
    body
}
