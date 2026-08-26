// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

pub mod adjustment;
pub mod annotation;
pub(crate) mod attribute;
pub mod check;
pub mod dataflow;
pub mod expectation;

use rustc_errors::ErrorGuaranteed;
use rustc_mir_dataflow::lattice::FlatSet;

use crate::lattice::MeetSemiLattice;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub enum Error {
    TooGeneric,
    Error(ErrorGuaranteed),
}

/// Range of preemption count that the function expects.
///
/// Since the preemption count is a non-negative integer, the lower bound is just represented using a `u32`
/// and "no expectation" is represented with 0; the upper bound is represented using an `Option<u32>`, with
/// `None` representing "no expectation". The upper bound is exclusive so `(0, Some(0))` represents an
/// unsatisfiable condition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Encodable, Decodable)]
pub struct ExpectationRange {
    pub lo: u32,
    pub hi: Option<u32>,
}

impl ExpectationRange {
    pub const fn top() -> Self {
        Self { lo: 0, hi: None }
    }

    pub const fn single_value(v: u32) -> Self {
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

    pub fn contains_range(&self, mut other: Self) -> bool {
        !other.meet(self)
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

impl std::ops::Add<i32> for ExpectationRange {
    type Output = Self;

    fn add(self, rhs: i32) -> Self::Output {
        Self {
            lo: saturating_add(self.lo, rhs),
            hi: self.hi.map(|hi| saturating_add(hi, rhs)),
        }
    }
}

impl std::ops::Sub<i32> for ExpectationRange {
    type Output = Self;

    fn sub(self, rhs: i32) -> Self::Output {
        Self {
            lo: saturating_add(self.lo, -rhs),
            hi: self.hi.map(|hi| saturating_add(hi, -rhs)),
        }
    }
}

impl std::ops::Add<FlatSet<i32>> for ExpectationRange {
    type Output = Self;

    fn add(self, rhs: FlatSet<i32>) -> Self::Output {
        match rhs {
            FlatSet::Bottom => self,
            FlatSet::Elem(v) => self + v,
            FlatSet::Top => Self::top(),
        }
    }
}

impl std::ops::Sub<FlatSet<i32>> for ExpectationRange {
    type Output = Self;

    fn sub(self, rhs: FlatSet<i32>) -> Self::Output {
        match rhs {
            FlatSet::Bottom => self,
            FlatSet::Elem(v) => self - v,
            FlatSet::Top => Self { lo: 0, hi: Some(0) },
        }
    }
}
