// SPDX-License-Identifier: MIT OR Apache-2.0

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit as hir_visit;
use rustc_hir::{Body, Expr, HirId, QPath, StmtKind, UnOp};
use rustc_lint::{LateContext, LateLintPass, LintContext};
use rustc_middle::ty::{TyCtxt, TypeVisitableExt, TypeckResults};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{BytePos, Span, Symbol};

use crate::ctxt::AnalysisCtxt;

declare_tool_lint! {
    pub klint::ASSERT_HIERARCHY,
    Warn,
    "assertion can be written as a stronger compile-time assertion"
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum AssertStrength {
    Build,
    Const,
    Static,
}

impl AssertStrength {
    fn combine<I>(strengths: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        strengths
            .into_iter()
            .min()
            .unwrap_or(AssertStrength::Static)
    }

    fn local_binding(self) -> Self {
        match self {
            AssertStrength::Build => AssertStrength::Build,
            AssertStrength::Const | AssertStrength::Static => AssertStrength::Const,
        }
    }

    fn replacement_macro(self, current: AssertionKind) -> Option<Symbol> {
        match (current, self) {
            (AssertionKind::Build, AssertStrength::Static) => Some(crate::symbol::static_assert),
            (AssertionKind::Build, AssertStrength::Const) => Some(crate::symbol::const_assert),
            (AssertionKind::Const, AssertStrength::Static) => Some(crate::symbol::static_assert),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AssertionKind {
    Build,
    Const,
}

impl AssertionKind {
    fn macro_name(self) -> Symbol {
        match self {
            AssertionKind::Build => crate::symbol::build_assert,
            AssertionKind::Const => crate::symbol::const_assert,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct AssertionCondition {
    kind: AssertionKind,
    call_site: Span,
    condition_span: Span,
}

fn assertion_call_site(
    tcx: TyCtxt<'_>,
    span: Span,
    assertions: &[(AssertionKind, Option<DefId>, Symbol)],
) -> Option<(AssertionKind, Span)> {
    span.macro_backtrace()
        .find(|expn_data| {
            let Some(macro_def_id) = expn_data.macro_def_id else {
                return false;
            };

            assertions.iter().any(|&(_, assertion, name)| {
                Some(macro_def_id) == assertion || tcx.item_name(macro_def_id) == name
            })
        })
        .and_then(|expn_data| {
            let macro_def_id = expn_data.macro_def_id?;
            let kind = assertions.iter().find_map(|&(kind, assertion, name)| {
                (Some(macro_def_id) == assertion || tcx.item_name(macro_def_id) == name)
                    .then_some(kind)
            })?;
            Some((kind, expn_data.call_site.source_callsite()))
        })
}

fn assertion_condition(
    tcx: TyCtxt<'_>,
    expr: &Expr<'_>,
    assertions: &[(AssertionKind, Option<DefId>, Symbol)],
) -> Option<AssertionCondition> {
    let rustc_hir::ExprKind::Unary(UnOp::Not, condition) = expr.kind else {
        return None;
    };
    if !expr.span.from_expansion() {
        return None;
    }

    let (kind, call_site) = assertion_call_site(tcx, expr.span, assertions)?;
    let condition_span = condition.span.source_callsite();
    Some(AssertionCondition {
        kind,
        call_site,
        condition_span,
    })
}

fn emit_assert_hierarchy(
    cx: &LateContext<'_>,
    assertion_span: Span,
    condition_span: Span,
    current: AssertionKind,
    strength: AssertStrength,
) {
    let Some(replacement_macro) = strength.replacement_macro(current) else {
        return;
    };
    let primary = match replacement_macro {
        crate::symbol::static_assert => "this assertion can use the stronger `static_assert!` form",
        crate::symbol::const_assert => "this assertion can use the stronger `const_assert!` form",
        _ => return,
    };
    let note = match (current, strength) {
        (AssertionKind::Build, AssertStrength::Static)
        | (AssertionKind::Const, AssertStrength::Static) => {
            "this asserted condition is closed over compile-time context, so `static_assert!` is the stronger form here"
        }
        (AssertionKind::Build, AssertStrength::Const) => {
            "this asserted condition is valid in a generic-aware const context, so `build_assert!` is unnecessary here"
        }
        _ => return,
    };

    if let Some(macro_name_span) = macro_name_span(cx, assertion_span, current.macro_name()) {
        cx.emit_span_lint(
            ASSERT_HIERARCHY,
            assertion_span,
            AssertHierarchySuggestionDiag {
                assertion_span,
                condition_span,
                macro_name_span,
                primary,
                replacement_macro,
                note,
            },
        );
    } else {
        cx.emit_span_lint(
            ASSERT_HIERARCHY,
            assertion_span,
            AssertHierarchyDiag {
                assertion_span,
                condition_span,
                primary,
                note,
            },
        );
    }
}

fn macro_name_span(cx: &LateContext<'_>, call_site: Span, current_macro: Symbol) -> Option<Span> {
    let source = cx.sess().source_map().span_to_snippet(call_site).ok()?;
    let name = current_macro.as_str();
    let rest = source.strip_prefix(name)?;
    if !rest.starts_with('!') {
        return None;
    }

    Some(call_site.with_hi(call_site.lo() + BytePos(name.len() as u32)))
}

#[derive(Diagnostic)]
#[diag("{$primary}")]
struct AssertHierarchyDiag {
    #[primary_span]
    pub assertion_span: Span,
    #[note("{$note}")]
    pub condition_span: Span,
    pub primary: &'static str,
    pub note: &'static str,
}

#[derive(Diagnostic)]
#[diag("{$primary}")]
struct AssertHierarchySuggestionDiag {
    #[primary_span]
    pub assertion_span: Span,
    #[note("{$note}")]
    pub condition_span: Span,
    #[suggestion(
        "replace the macro name",
        code = "{replacement_macro}",
        applicability = "machine-applicable"
    )]
    pub macro_name_span: Span,
    pub primary: &'static str,
    pub replacement_macro: Symbol,
    pub note: &'static str,
}

pub struct AssertHierarchy<'tcx> {
    pub cx: &'tcx AnalysisCtxt<'tcx>,
}

impl_lint_pass!(AssertHierarchy<'_> => [ASSERT_HIERARCHY]);

struct AssertFnState<'a, 'tcx> {
    cx: &'a AnalysisCtxt<'tcx>,
    late_cx: &'a LateContext<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    assertions: [(AssertionKind, Option<DefId>, Symbol); 2],
    env: LocalEnv,
}

struct LocalEnv {
    bindings: FxHashMap<HirId, AssertStrength>,
}

impl LocalEnv {
    fn new() -> Self {
        Self {
            bindings: FxHashMap::default(),
        }
    }

    fn bind_pattern(&mut self, pat: &rustc_hir::Pat<'_>, strength: AssertStrength) {
        pat.each_binding(|_, hir_id, _, _| {
            self.bindings.insert(hir_id, strength);
        });
    }

    fn get_dependency(&self, hir_id: HirId) -> Option<&AssertStrength> {
        self.bindings.get(&hir_id)
    }
}

impl<'a, 'tcx> AssertFnState<'a, 'tcx> {
    fn path_strength(&self, qpath: &QPath<'tcx>, hir_id: HirId) -> AssertStrength {
        let resolved_strength = match self.typeck.qpath_res(qpath, hir_id) {
            Res::Local(local) => self
                .env
                .get_dependency(local)
                .copied()
                .unwrap_or(AssertStrength::Build),
            Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, _) => {
                AssertStrength::Static
            }
            Res::Def(DefKind::ConstParam, _) => AssertStrength::Const,
            _ => AssertStrength::Build,
        };

        AssertStrength::combine([resolved_strength, self.generic_strength(hir_id)])
    }

    fn generic_strength(&self, hir_id: HirId) -> AssertStrength {
        self.typeck
            .node_args_opt(hir_id)
            .map(|args| {
                if args.has_non_region_param() {
                    AssertStrength::Const
                } else {
                    AssertStrength::Static
                }
            })
            .unwrap_or(AssertStrength::Static)
    }

    fn combine_exprs<I>(&mut self, exprs: I) -> AssertStrength
    where
        I: IntoIterator<Item = &'tcx Expr<'tcx>>,
    {
        AssertStrength::combine(exprs.into_iter().map(|expr| self.expr_strength(expr)))
    }

    fn block_strength(&mut self, block: &'tcx rustc_hir::Block<'tcx>) -> AssertStrength {
        let outer_bindings = std::mem::take(&mut self.env.bindings);

        let strength = (|| {
            for stmt in block.stmts {
                match stmt.kind {
                    StmtKind::Let(local) => {
                        let Some(init) = local.init else {
                            return AssertStrength::Build;
                        };
                        let strength = self.expr_strength(init).local_binding();
                        self.env.bind_pattern(local.pat, strength);
                        if let Some(els) = local.els {
                            return self.block_strength(els);
                        }
                    }
                    StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                        if self.expr_strength(expr) == AssertStrength::Build {
                            return AssertStrength::Build;
                        }
                    }
                    StmtKind::Item(..) => return AssertStrength::Build,
                }
            }

            block
                .expr
                .map(|expr| self.expr_strength(expr))
                .unwrap_or(AssertStrength::Static)
        })();

        self.env.bindings = outer_bindings;
        strength
    }

    fn call_strength(
        &mut self,
        callee: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> AssertStrength {
        let rustc_hir::ExprKind::Path(ref qpath) = callee.kind else {
            return AssertStrength::Build;
        };
        let resolved = self.typeck.qpath_res(qpath, callee.hir_id);
        let arg_strength = AssertStrength::combine([
            self.combine_exprs(args.iter()),
            self.generic_strength(callee.hir_id),
        ]);

        if arg_strength != AssertStrength::Build
            && matches!(resolved, Res::Def(DefKind::Ctor(..), _))
        {
            return arg_strength;
        }

        if arg_strength != AssertStrength::Build
            && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = resolved
            && self.cx.tcx.is_const_fn(def_id)
        {
            return arg_strength;
        }

        AssertStrength::Build
    }

    fn method_call_strength(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        receiver: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> AssertStrength {
        let arg_strength = AssertStrength::combine([
            self.combine_exprs(std::iter::once(receiver).chain(args.iter())),
            self.generic_strength(expr.hir_id),
        ]);

        if arg_strength != AssertStrength::Build
            && let Some(def_id) = self.typeck.type_dependent_def_id(expr.hir_id)
            && self.cx.tcx.is_const_fn(def_id)
        {
            return arg_strength;
        }

        AssertStrength::Build
    }

    fn expr_strength(&mut self, expr: &'tcx Expr<'tcx>) -> AssertStrength {
        match expr.kind {
            rustc_hir::ExprKind::ConstBlock(..) => AssertStrength::Const,
            rustc_hir::ExprKind::Lit(..) => AssertStrength::Static,
            rustc_hir::ExprKind::Path(ref qpath) => self.path_strength(qpath, expr.hir_id),
            rustc_hir::ExprKind::Use(inner, _)
            | rustc_hir::ExprKind::Unary(_, inner)
            | rustc_hir::ExprKind::Cast(inner, _)
            | rustc_hir::ExprKind::Type(inner, _)
            | rustc_hir::ExprKind::DropTemps(inner)
            | rustc_hir::ExprKind::Field(inner, _)
            | rustc_hir::ExprKind::AddrOf(_, _, inner)
            | rustc_hir::ExprKind::UnsafeBinderCast(_, inner, _) => self.expr_strength(inner),
            rustc_hir::ExprKind::Binary(_, lhs, rhs)
            | rustc_hir::ExprKind::AssignOp(_, lhs, rhs)
            | rustc_hir::ExprKind::Index(lhs, rhs, _) => self.combine_exprs([lhs, rhs]),
            rustc_hir::ExprKind::Assign(..) | rustc_hir::ExprKind::Repeat(..) => {
                AssertStrength::Build
            }
            rustc_hir::ExprKind::Array(exprs) | rustc_hir::ExprKind::Tup(exprs) => {
                self.combine_exprs(exprs.iter())
            }
            rustc_hir::ExprKind::Block(block, _) => self.block_strength(block),
            rustc_hir::ExprKind::Struct(_, fields, tail) => {
                let tail_strength = match tail {
                    rustc_hir::StructTailExpr::None => AssertStrength::Static,
                    rustc_hir::StructTailExpr::Base(expr) => self.expr_strength(expr),
                    rustc_hir::StructTailExpr::DefaultFields(_)
                    | rustc_hir::StructTailExpr::NoneWithError(_) => AssertStrength::Build,
                };
                AssertStrength::combine(
                    fields
                        .iter()
                        .map(|field| self.expr_strength(field.expr))
                        .chain(std::iter::once(tail_strength)),
                )
            }
            rustc_hir::ExprKind::If(condition, then_expr, else_expr) => AssertStrength::combine(
                std::iter::once(self.expr_strength(condition))
                    .chain(std::iter::once(self.expr_strength(then_expr)))
                    .chain(else_expr.into_iter().map(|expr| self.expr_strength(expr))),
            ),
            rustc_hir::ExprKind::Match(scrutinee, arms, _) => {
                let mut strengths = Vec::with_capacity(1 + arms.len() * 2);
                strengths.push(self.expr_strength(scrutinee));
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        strengths.push(self.expr_strength(guard));
                    }
                    strengths.push(self.expr_strength(arm.body));
                }
                AssertStrength::combine(strengths)
            }
            rustc_hir::ExprKind::Call(callee, args) => self.call_strength(callee, args),
            rustc_hir::ExprKind::MethodCall(_, receiver, args, _) => {
                self.method_call_strength(expr, receiver, args)
            }
            _ => AssertStrength::Build,
        }
    }
}

impl<'tcx> hir_visit::Visitor<'tcx> for AssertFnState<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let rustc_hir::ExprKind::Unary(UnOp::Not, condition_expr) = expr.kind
            && let Some(condition) = assertion_condition(self.cx.tcx, expr, &self.assertions)
            && let strength @ (AssertStrength::Const | AssertStrength::Static) =
                self.expr_strength(condition_expr)
        {
            emit_assert_hierarchy(
                self.late_cx,
                condition.call_site,
                condition.condition_span,
                condition.kind,
                strength,
            );
        }
        hir_visit::walk_expr(self, expr);
    }
}

impl<'tcx> LateLintPass<'tcx> for AssertHierarchy<'tcx> {
    fn check_fn(
        &mut self,
        cx: &LateContext<'tcx>,
        _: hir_visit::FnKind<'tcx>,
        _: &'tcx rustc_hir::FnDecl<'tcx>,
        body: &'tcx Body<'tcx>,
        _: Span,
        def_id: rustc_hir::def_id::LocalDefId,
    ) {
        let mut state = AssertFnState {
            cx: self.cx,
            late_cx: cx,
            typeck: cx.tcx.typeck(def_id),
            assertions: [
                (
                    AssertionKind::Build,
                    self.cx
                        .get_klint_diagnostic_item(crate::symbol::build_assert),
                    crate::symbol::build_assert,
                ),
                (
                    AssertionKind::Const,
                    self.cx
                        .get_klint_diagnostic_item(crate::symbol::const_assert),
                    crate::symbol::const_assert,
                ),
            ],
            env: LocalEnv::new(),
        };
        hir_visit::Visitor::visit_body(&mut state, body);
    }
}
