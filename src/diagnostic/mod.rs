pub(crate) mod use_stack;

use rustc_errors::{Diag, DiagCtxtHandle, Diagnostic, Level};
use rustc_middle::ty::PseudoCanonicalInput;

pub struct PolyDisplay<'a, 'tcx, T>(pub &'a PseudoCanonicalInput<'tcx, T>);

impl<T> std::fmt::Display for PolyDisplay<'_, '_, T>
where
    T: std::fmt::Display + Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PseudoCanonicalInput { typing_env, value } = self.0;
        write!(f, "{}", value)?;
        if !typing_env.param_env.caller_bounds().is_empty() {
            write!(f, " where ")?;
            for (i, predicate) in typing_env.param_env.caller_bounds().iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", predicate)?;
            }
        }
        Ok(())
    }
}

pub(crate) struct ClosureDiag<F: FnOnce(&mut Diag<'_, ()>)>(pub F);

impl<'a, F: FnOnce(&mut Diag<'_, ()>)> Diagnostic<'a, ()> for ClosureDiag<F> {
    fn into_diag(self, dcx: DiagCtxtHandle<'a>, level: Level) -> Diag<'a, ()> {
        let mut lint = Diag::new(dcx, level, "");
        (self.0)(&mut lint);
        lint
    }
}
