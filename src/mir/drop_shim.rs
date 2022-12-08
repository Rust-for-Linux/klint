// From rustc_mir_transform/src/shim.rs
// Adopted to support polymorphic drop shims

use rustc_hir::def_id::DefId;
use rustc_index::vec::{Idx, IndexVec};
use rustc_middle::mir::patch::MirPatch;
use rustc_middle::mir::*;
use rustc_middle::ty::{self, InternalSubsts, ParamEnv, Ty, TyCtxt};
use rustc_mir_dataflow::elaborate_drops::{self, *};
use rustc_span::Span;
use rustc_target::abi::VariantIdx;
use std::{fmt, iter};

fn local_decls_for_sig<'tcx>(
    sig: &ty::FnSig<'tcx>,
    span: Span,
) -> IndexVec<Local, LocalDecl<'tcx>> {
    iter::once(LocalDecl::new(sig.output(), span))
        .chain(
            sig.inputs()
                .iter()
                .map(|ity| LocalDecl::new(*ity, span).immutable()),
        )
        .collect()
}

#[instrument(skip(tcx))]
pub fn build_drop_shim<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_env: ParamEnv<'tcx>,
    ty: Ty<'tcx>,
) -> Body<'tcx> {
    assert!(!ty.is_generator());

    let substs = tcx.intern_substs(&[ty.into()]);
    let sig = tcx.bound_fn_sig(def_id).subst(tcx, substs);
    let sig = tcx.erase_late_bound_regions(sig);
    let span = tcx.def_span(def_id);

    let source_info = SourceInfo::outermost(span);

    let return_block = BasicBlock::new(1);
    let mut blocks = IndexVec::with_capacity(2);
    let block = |blocks: &mut IndexVec<_, _>, kind| {
        blocks.push(BasicBlockData {
            statements: vec![],
            terminator: Some(Terminator { source_info, kind }),
            is_cleanup: false,
        })
    };
    block(
        &mut blocks,
        TerminatorKind::Goto {
            target: return_block,
        },
    );
    block(&mut blocks, TerminatorKind::Return);

    let source = MirSource::from_instance(ty::InstanceDef::DropGlue(def_id, Some(ty)));
    let mut body = new_body(
        source,
        blocks,
        local_decls_for_sig(&sig, span),
        sig.inputs().len(),
        span,
    );

    // The first argument (index 0), but add 1 for the return value.
    let dropee_ptr = Place::from(Local::new(1 + 0));
    let patch = {
        let mut elaborator = DropShimElaborator {
            body: &body,
            patch: MirPatch::new(&body),
            tcx,
            param_env,
        };
        let dropee = tcx.mk_place_deref(dropee_ptr);
        let resume_block = elaborator.patch.resume_block();
        elaborate_drops::elaborate_drop(
            &mut elaborator,
            source_info,
            dropee,
            (),
            return_block,
            elaborate_drops::Unwind::To(resume_block),
            START_BLOCK,
        );
        elaborator.patch
    };
    patch.apply(&mut body);
    body
}

fn new_body<'tcx>(
    source: MirSource<'tcx>,
    basic_blocks: IndexVec<BasicBlock, BasicBlockData<'tcx>>,
    local_decls: IndexVec<Local, LocalDecl<'tcx>>,
    arg_count: usize,
    span: Span,
) -> Body<'tcx> {
    Body::new(
        source,
        basic_blocks,
        IndexVec::from_elem_n(
            SourceScopeData {
                span,
                parent_scope: None,
                inlined: None,
                inlined_parent_scope: None,
                local_data: ClearCrossCrate::Clear,
            },
            1,
        ),
        local_decls,
        IndexVec::new(),
        arg_count,
        vec![],
        span,
        None,
        // FIXME(compiler-errors): is this correct?
        None,
    )
}

pub struct DropShimElaborator<'a, 'tcx> {
    pub body: &'a Body<'tcx>,
    pub patch: MirPatch<'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub param_env: ty::ParamEnv<'tcx>,
}

impl fmt::Debug for DropShimElaborator<'_, '_> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        Ok(())
    }
}

impl<'a, 'tcx> DropElaborator<'a, 'tcx> for DropShimElaborator<'a, 'tcx> {
    type Path = ();

    fn patch(&mut self) -> &mut MirPatch<'tcx> {
        &mut self.patch
    }
    fn body(&self) -> &'a Body<'tcx> {
        self.body
    }
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn param_env(&self) -> ty::ParamEnv<'tcx> {
        self.param_env
    }

    fn drop_style(&self, _path: Self::Path, mode: DropFlagMode) -> DropStyle {
        match mode {
            DropFlagMode::Shallow => {
                // Drops for the contained fields are "shallow" and "static" - they will simply call
                // the field's own drop glue.
                DropStyle::Static
            }
            DropFlagMode::Deep => {
                // The top-level drop is "deep" and "open" - it will be elaborated to a drop ladder
                // dropping each field contained in the value.
                DropStyle::Open
            }
        }
    }

    fn get_drop_flag(&mut self, _path: Self::Path) -> Option<Operand<'tcx>> {
        None
    }

    fn clear_drop_flag(&mut self, _location: Location, _path: Self::Path, _mode: DropFlagMode) {}

    fn field_subpath(&self, _path: Self::Path, _field: Field) -> Option<Self::Path> {
        None
    }
    fn deref_subpath(&self, _path: Self::Path) -> Option<Self::Path> {
        None
    }
    fn downcast_subpath(&self, _path: Self::Path, _variant: VariantIdx) -> Option<Self::Path> {
        Some(())
    }
    fn array_subpath(&self, _path: Self::Path, _index: u64, _size: u64) -> Option<Self::Path> {
        None
    }
}
