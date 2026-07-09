// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

// This is a regression test which is minimize from ICE when compiling libcore.

pub trait Pattern: Sized {
    #[inline]
    fn strip_prefix_of(self, _haystack: &str) -> Option<&str> {
        let _ = &0;
        None
    }
}

#[doc(hidden)]
trait MultiCharEq {}

impl<const N: usize> MultiCharEq for [char; N] {}

struct MultiCharEqPattern<C: MultiCharEq>(C);

impl<C: MultiCharEq> Pattern for MultiCharEqPattern<C> {}

impl<const N: usize> Pattern for [char; N] {
    #[inline]
    fn strip_prefix_of(self, haystack: &str) -> Option<&str> {
        MultiCharEqPattern(self).strip_prefix_of(haystack)
    }
}
