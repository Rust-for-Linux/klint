use rustc_middle::ty::ParamEnvAnd;

mod adjustment;
pub mod dataflow;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub struct TooGeneric;

pub struct PolyDisplay<'a, 'tcx, T>(pub &'a ParamEnvAnd<'tcx, T>);

impl<T> std::fmt::Display for PolyDisplay<'_, '_, T>
where
    T: std::fmt::Display + Copy,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (param_env, instance) = self.0.into_parts();
        write!(f, "{}", instance)?;
        if !param_env.caller_bounds().is_empty() {
            write!(f, " where ")?;
            for (i, predicate) in param_env.caller_bounds().iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", predicate)?;
            }
        }
        Ok(())
    }
}
