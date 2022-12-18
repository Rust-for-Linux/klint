pub mod adjustment;
pub mod annotation;
pub mod dataflow;
pub mod expectation;

use rustc_middle::ty::{Instance, ParamEnvAnd};
use rustc_mir_dataflow::lattice::MeetSemiLattice;
use rustc_span::Span;

use self::dataflow::AdjustmentBounds;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub struct ExpectationRange {
    pub lo: u32,
    pub hi: Option<u32>,
}

impl ExpectationRange {
    pub fn top() -> Self {
        Self { lo: 0, hi: None }
    }

    pub fn single_value(v: u32) -> Self {
        Self {
            lo: v,
            hi: Some(v + 1),
        }
    }

    pub fn is_empty(&self) -> bool {
        if let Some(hi) = self.hi {
            self.lo >= hi
        } else {
            false
        }
    }
}

impl MeetSemiLattice for ExpectationRange {
    fn meet(&mut self, other: &Self) -> bool {
        let mut changed = false;
        if self.lo < other.lo {
            self.lo = other.lo;
            changed = true;
        }

        match (self.hi, other.hi) {
            (_, None) => (),
            (None, Some(_)) => {
                self.hi = other.hi;
                changed = true;
            }
            (Some(a), Some(b)) => {
                if a > b {
                    self.hi = Some(b);
                    changed = true;
                }
            }
        }

        changed
    }
}

impl std::fmt::Display for ExpectationRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.lo, self.hi) {
            (lo, None) => write!(f, "{}..", lo),
            (lo, Some(hi)) if lo >= hi => write!(f, "unsatisfiable"),
            (lo, Some(hi)) if lo + 1 == hi => write!(f, "{lo}"),
            (lo, Some(hi)) => write!(f, "{}..{}", lo, hi),
        }
    }
}

fn saturating_add(x: u32, y: i32) -> u32 {
    let (res, overflow) = x.overflowing_add(y as u32);
    if overflow == (y < 0) {
        res
    } else if overflow {
        u32::MAX
    } else {
        0
    }
}

impl std::ops::Add<AdjustmentBounds> for ExpectationRange {
    type Output = Self;

    fn add(self, rhs: AdjustmentBounds) -> Self::Output {
        Self {
            lo: match rhs.lo {
                None => 0,
                Some(bound) => saturating_add(self.lo, bound),
            },
            hi: self
                .hi
                .zip(rhs.hi)
                .map(|(hi, bound)| saturating_add(hi, bound - 1)),
        }
    }
}

impl std::ops::Sub<AdjustmentBounds> for ExpectationRange {
    type Output = Self;

    fn sub(self, rhs: AdjustmentBounds) -> Self::Output {
        Self {
            lo: match rhs.lo {
                None => 0,
                Some(bound) => saturating_add(self.lo, -bound),
            },
            hi: match (self.hi, rhs.hi) {
                (None, _) => None,
                (_, None) => Some(0),
                (Some(hi), Some(bound)) => Some(saturating_add(hi, 1 - bound)),
            },
        }
    }
}

#[derive(Debug)]
pub enum UseSiteKind {
    Call(Span),
    Drop {
        /// Span that causes the drop.
        drop_span: Span,
        /// Span of the place being dropped.
        place_span: Span,
    },
}

#[derive(Debug)]
pub struct UseSite<'tcx> {
    pub instance: ParamEnvAnd<'tcx, Instance<'tcx>>,
    pub kind: UseSiteKind,
}
