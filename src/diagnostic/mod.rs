pub(crate) mod use_stack;

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
            for (i, clause) in typing_env.param_env.caller_bounds().iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", clause)?;
            }
        }
        Ok(())
    }
}
