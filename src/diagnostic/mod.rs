pub(crate) mod use_stack;

use rustc_middle::ty::{CallerBoundsIterator, PseudoCanonicalInput, TyCtxt};

pub struct PolyDisplay<'a, 'tcx, T>(pub TyCtxt<'tcx>, pub &'a PseudoCanonicalInput<'tcx, T>);

impl<T> std::fmt::Display for PolyDisplay<'_, '_, T>
where
    T: std::fmt::Display + Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let PseudoCanonicalInput { typing_env, value } = self.1;
        write!(f, "{}", value)?;
        if !typing_env.param_env.is_empty() {
            write!(f, " where ")?;
            for (i, clause) in typing_env
                .param_env
                .caller_bounds()
                .all_clauses(self.0)
                .iter()
                .enumerate()
            {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", clause)?;
            }
        }
        Ok(())
    }
}
