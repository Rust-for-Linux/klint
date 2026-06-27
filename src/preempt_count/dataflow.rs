// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_middle::mir::{BasicBlock, Body, TerminatorEdges, TerminatorKind};
use rustc_middle::ty::{self, Instance, TypingEnv};
use rustc_mir_dataflow::JoinSemiLattice;
use rustc_mir_dataflow::lattice::FlatSet;
use rustc_mir_dataflow::{Analysis, fmt::DebugWithContext};

use super::Error;
use crate::ctxt::AnalysisCtxt;
use crate::diagnostic::use_stack::{UseSite, UseSiteKind};

/// A result type that can be used as lattice.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MaybeError<T, E> {
    Ok(T),
    Err(E),
}

impl<T: Default, E> Default for MaybeError<T, E> {
    fn default() -> Self {
        Self::Ok(Default::default())
    }
}

impl<T, E> From<Result<T, E>> for MaybeError<T, E> {
    #[inline]
    fn from(value: Result<T, E>) -> Self {
        match value {
            Ok(v) => Self::Ok(v),
            Err(e) => Self::Err(e),
        }
    }
}

impl<T, E> From<MaybeError<T, E>> for Result<T, E> {
    #[inline]
    fn from(value: MaybeError<T, E>) -> Self {
        match value {
            MaybeError::Ok(v) => Ok(v),
            MaybeError::Err(e) => Err(e),
        }
    }
}

impl<T, E> MaybeError<T, E> {
    #[inline]
    pub fn from_result(result: Result<T, E>) -> Self {
        result.into()
    }

    #[inline]
    pub fn into_result(self) -> Result<T, E> {
        self.into()
    }

    #[inline]
    #[track_caller]
    pub fn unwrap(self) -> T
    where
        E: std::fmt::Debug,
    {
        self.into_result().unwrap()
    }
}

// The error type is hard coded to `Error` because we need special treatment w.r.t. `TooGeneric`.
impl<T: JoinSemiLattice> JoinSemiLattice for MaybeError<T, Error> {
    fn join(&mut self, other: &Self) -> bool {
        match (self, other) {
            (Self::Err(Error::Error(_)), _) => false,
            (this, Self::Err(Error::Error(e))) => {
                *this = Self::Err(Error::Error(*e));
                true
            }
            (Self::Err(Error::TooGeneric), _) => false,
            (this, Self::Err(Error::TooGeneric)) => {
                *this = Self::Err(Error::TooGeneric);
                true
            }
            (Self::Ok(a), Self::Ok(b)) => a.join(b),
        }
    }
}

pub struct AdjustmentComputation<'mir, 'tcx, 'checker> {
    pub checker: &'checker AnalysisCtxt<'tcx>,
    pub body: &'mir Body<'tcx>,
    pub typing_env: TypingEnv<'tcx>,
    pub instance: Instance<'tcx>,
}

impl DebugWithContext<AdjustmentComputation<'_, '_, '_>> for MaybeError<FlatSet<i32>, Error> {}

impl<'tcx> Analysis<'tcx> for AdjustmentComputation<'_, 'tcx, '_> {
    // The number here indicates the offset in relation to the function's entry point.
    type Domain = MaybeError<FlatSet<i32>, Error>;

    const NAME: &'static str = "atomic context";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        MaybeError::Ok(FlatSet::Bottom)
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, state: &mut Self::Domain) {
        *state = MaybeError::Ok(FlatSet::Elem(0));
    }

    fn apply_primary_statement_effect(
        &self,
        _state: &mut Self::Domain,
        _statement: &rustc_middle::mir::Statement<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        state: &mut Self::Domain,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // Skip all unwinding paths.
        if self.body.basic_blocks[location.block].is_cleanup {
            return terminator.edges();
        }

        let MaybeError::Ok(bounds) = state else {
            return terminator.edges();
        };

        let adjustment = match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let callee_ty = func.ty(self.body, self.checker.tcx);
                let callee_ty = self.instance.instantiate_mir_and_normalize_erasing_regions(
                    self.checker.tcx,
                    self.typing_env,
                    ty::EarlyBinder::bind(self.checker.tcx, callee_ty),
                );
                if let ty::FnDef(def_id, args) = *callee_ty.kind() {
                    if let Some(v) = self.checker.preemption_count_annotation(def_id).adjustment {
                        // Fast path, no need to resolve the instance.
                        // This also avoids `TooGeneric` when def_id is an trait method.
                        Ok(v)
                    } else {
                        match ty::Instance::try_resolve(
                            self.checker.tcx,
                            self.typing_env,
                            def_id,
                            args,
                        )
                        .unwrap()
                        {
                            Some(instance) => {
                                self.checker.call_stack.borrow_mut().push(UseSite {
                                    instance: self.typing_env.as_query_input(self.instance),
                                    kind: UseSiteKind::Call(terminator.source_info.span),
                                });
                                let result = self
                                    .checker
                                    .instance_adjustment(self.typing_env.as_query_input(instance));
                                self.checker.call_stack.borrow_mut().pop();
                                result
                            }
                            None => Err(Error::TooGeneric),
                        }
                    }
                } else {
                    Ok(crate::atomic_context::INDIRECT_DEFAULT.0)
                }
            }
            TerminatorKind::Drop { place, .. } => {
                let ty = place.ty(self.body, self.checker.tcx).ty;
                let ty = self.instance.instantiate_mir_and_normalize_erasing_regions(
                    self.checker.tcx,
                    self.typing_env,
                    ty::EarlyBinder::bind(self.checker.tcx, ty),
                );

                self.checker.call_stack.borrow_mut().push(UseSite {
                    instance: self.typing_env.as_query_input(self.instance),
                    kind: UseSiteKind::Drop {
                        drop_span: terminator.source_info.span,
                        place_span: self.body.local_decls[place.local].source_info.span,
                    },
                });
                let result = self
                    .checker
                    .drop_adjustment(self.typing_env.as_query_input(ty));
                self.checker.call_stack.borrow_mut().pop();
                result
            }
            _ => return terminator.edges(),
        };

        let adjustment = match adjustment {
            Ok(v) => v,
            Err(e) => {
                // Too generic, need to bail out and retry after monomorphization.
                *state = MaybeError::Err(e);
                return terminator.edges();
            }
        };

        *bounds = match *bounds {
            FlatSet::Bottom => unreachable!(),
            FlatSet::Elem(v) => FlatSet::Elem(v + adjustment),
            FlatSet::Top => FlatSet::Top,
        };
        terminator.edges()
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: BasicBlock,
        _return_places: rustc_middle::mir::CallReturnPlaces<'_, 'tcx>,
    ) {
    }
}
