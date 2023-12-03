#![crate_type = "lib"]

// This is a case that currently klint will return false positive.

pub struct X;

impl Drop for X {
    #[klint::preempt_count(expect = 0)]
    #[inline(never)]
    fn drop(&mut self) {}
}

#[klint::preempt_count(expect = 0..)]
pub fn foo(x: Option<X>) -> Option<X> {
    if let Some(x) = x {
        return Some(x);
    }
    None
}
