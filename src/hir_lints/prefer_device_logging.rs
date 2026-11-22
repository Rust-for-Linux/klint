use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_hir::{BinOpKind, Expr, ExprKind, HirId, Node, Pat, StmtKind};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_lint::{LateContext, LateLintPass, LintContext, declare_tool_lint, impl_lint_pass};
use rustc_middle::middle::resolve::ModChild;
use rustc_middle::ty::{self, Ty};
use rustc_span::{Ident, Span, Symbol, sym};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;
use rustc_trait_selection::traits::{Obligation, ObligationCause};

declare_tool_lint! {
    /// The `prefer_device_logging` lint detects kernel `pr_*` calls made with a device in scope.
    pub klint::PREFER_DEVICE_LOGGING,
    Warn,
    "generic kernel logging used when a device is available"
}

#[derive(Default)]
pub struct PreferDeviceLogging {
    checked: FxHashSet<Span>,
}

impl_lint_pass!(PreferDeviceLogging => [PREFER_DEVICE_LOGGING]);

#[derive(Diagnostic)]
#[diag("`{$print}!` is used while a device reference is in scope")]
#[help("consider using `{$device_print}!` with `{$device}` to include device information")]
struct PreferDeviceLoggingLint {
    print: Symbol,
    device_print: &'static str,
    device: Symbol,
}

fn module_children<'tcx>(cx: &LateContext<'tcx>, module: DefId) -> &'tcx [ModChild] {
    if let Some(local) = module.as_local() {
        cx.tcx.module_children_local(local)
    } else {
        cx.tcx.module_children(module)
    }
}

/// Look up the actual kernel type, so unrelated types named `Device` do not trigger the lint.
fn kernel_device(cx: &LateContext<'_>) -> Option<DefId> {
    let krate = cx
        .tcx
        .crates(())
        .iter()
        .copied()
        .chain(std::iter::once(LOCAL_CRATE))
        .find(|&krate| cx.tcx.crate_name(krate) == crate::symbol::kernel)?;
    let module = module_children(cx, krate.as_def_id())
        .iter()
        .find(|child| child.ident.name.as_str() == "device")?
        .res
        .opt_def_id()?;
    module_children(cx, module)
        .iter()
        .find(|child| child.ident.name.as_str() == "Device")?
        .res
        .opt_def_id()
}

fn is_device_reference(cx: &LateContext<'_>, binding: HirId, device: DefId) -> bool {
    let typeck = cx.tcx.typeck(binding.owner.def_id);
    let ty = typeck.node_type(binding);
    // Shared references remain available even if previously passed by value. Restrict the first
    // version to these rather than suggesting an owned or mutable device that may have been moved.
    let ty::Ref(_, _, rustc_hir::Mutability::Not) = ty.kind() else {
        return false;
    };
    let Some(as_ref) = cx.tcx.get_diagnostic_item(sym::AsRef) else {
        return false;
    };
    let infcx = cx.tcx.infer_ctxt().build(cx.typing_mode());
    let args = infcx.fresh_args_for_item(cx.tcx.hir_span(binding), device);
    let device_ty = Ty::new_adt(cx.tcx, cx.tcx.adt_def(device), args);
    let obligation = Obligation::new(
        cx.tcx,
        ObligationCause::dummy(),
        cx.param_env,
        ty::TraitRef::new(cx.tcx, as_ref, [ty, device_ty]),
    );
    infcx.predicate_must_hold_modulo_regions(&obligation)
}

fn add_bindings(pat: &Pat<'_>, bindings: &mut Vec<(HirId, Ident)>) {
    pat.each_binding(|_, id, _, ident| {
        if !ident.span.from_expansion() {
            bindings.push((id, ident));
        }
    });
}

fn condition_bindings(expr: &Expr<'_>, bindings: &mut Vec<(HirId, Ident)>) {
    match expr.kind {
        ExprKind::Let(let_expr) => add_bindings(let_expr.pat, bindings),
        ExprKind::Binary(op, left, right) if op.node == BinOpKind::And => {
            condition_bindings(right, bindings);
            condition_bindings(left, bindings);
        }
        _ => (),
    }
}

/// Walk outwards, visiting inner declarations first so shadowed device references are ignored.
fn device_in_scope(cx: &LateContext<'_>, expr: &Expr<'_>, device: DefId) -> Option<Symbol> {
    let mut bindings = Vec::new();
    let mut uninitialized = FxHashSet::default();
    let mut child = expr.hir_id;
    for (id, node) in cx.tcx.hir_parent_iter(expr.hir_id) {
        match node {
            Node::Block(block) => {
                let preceding = block
                    .stmts
                    .iter()
                    .take_while(|stmt| stmt.hir_id != child)
                    .collect::<Vec<_>>();
                for stmt in preceding.into_iter().rev() {
                    if let StmtKind::Let(local) = stmt.kind {
                        add_bindings(local.pat, &mut bindings);
                        if local.init.is_none() {
                            local.pat.each_binding(|_, id, _, _| {
                                uninitialized.insert(id);
                            });
                        }
                    }
                }
            }
            Node::Arm(arm) => add_bindings(arm.pat, &mut bindings),
            Node::Expr(parent) => match parent.kind {
                ExprKind::If(cond, then, _) if then.hir_id == child => {
                    condition_bindings(cond, &mut bindings);
                }
                ExprKind::Binary(op, left, right)
                    if op.node == BinOpKind::And && right.hir_id == child =>
                {
                    condition_bindings(left, &mut bindings);
                }
                ExprKind::Closure(closure) => {
                    for param in cx.tcx.hir_body(closure.body).params {
                        add_bindings(param.pat, &mut bindings);
                    }
                }
                _ => (),
            },
            Node::Item(_) | Node::ImplItem(_) | Node::TraitItem(_) => {
                if let Some(body) = cx.tcx.hir_maybe_body_owned_by(id.owner.def_id) {
                    for param in body.params {
                        add_bindings(param.pat, &mut bindings);
                    }
                }
                // Nested functions cannot capture their enclosing function's locals.
                break;
            }
            _ => (),
        }
        child = id;
    }

    let mut seen = FxHashSet::default();
    bindings.into_iter().find_map(|(id, ident)| {
        (seen.insert(ident.name)
            && !uninitialized.contains(&id)
            && is_device_reference(cx, id, device))
        .then_some(ident.name)
    })
}

impl<'tcx> LateLintPass<'tcx> for PreferDeviceLogging {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'tcx>) {
        for expansion in expr.span.macro_backtrace() {
            let Some(def_id) = expansion.macro_def_id else {
                continue;
            };
            if cx.tcx.crate_name(def_id.krate) != crate::symbol::kernel {
                continue;
            }
            let print = cx.tcx.item_name(def_id);
            let device_print = match print.as_str() {
                "pr_emerg" => "dev_emerg",
                "pr_alert" => "dev_alert",
                "pr_crit" => "dev_crit",
                "pr_err" => "dev_err",
                "pr_warn" => "dev_warn",
                "pr_notice" => "dev_notice",
                "pr_info" => "dev_info",
                "pr_debug" => "dev_dbg",
                _ => continue,
            };
            if !module_children(cx, def_id.krate.as_def_id())
                .iter()
                .any(|child| child.ident.name == print && child.res.opt_def_id() == Some(def_id))
            {
                continue;
            }
            // Only diagnose directly written invocations, not logging inside another macro.
            let span = expansion.call_site;
            if span.from_expansion() || !self.checked.insert(span) {
                return;
            }
            if let Some(device_type) = kernel_device(cx)
                && let Some(device) = device_in_scope(cx, expr, device_type)
            {
                cx.emit_span_lint(
                    PREFER_DEVICE_LOGGING,
                    span,
                    PreferDeviceLoggingLint {
                        print,
                        device_print,
                        device,
                    },
                );
            }
            return;
        }
    }
}
