#![allow(klint::build_assert_not_inlined)]
#![deny(klint::build_assert_can_be_const)]

unsafe extern "C" {
    #[klint::diagnostic_item = "build_error"]
    safe fn rust_build_error();
}

#[klint::diagnostic_item = "build_assert"]
macro_rules! build_assert {
    ($expr:expr $(,)?) => {
        if !$expr {
            rust_build_error();
        }
    };
    ($expr:expr, $msg:expr $(,)?) => {
        if !$expr {
            let _ = $msg;
            rust_build_error();
        }
    };
}

macro_rules! forward_build_assert {
    ($expr:expr $(,)?) => {
        build_assert!($expr)
    };
}

const OFFSET: usize = 1;
const LIMIT: usize = 4;

fn literal_const_only() {
    build_assert!(1 < LIMIT);
}

fn const_generic_only<const N: usize>() {
    build_assert!(OFFSET < N, "offset must stay in bounds");
}

fn wrapper_const_only() {
    forward_build_assert!(OFFSET < LIMIT);
}

fn helper<const N: usize>() -> usize {
    N - 1
}

fn helper_const_only<const N: usize>() {
    build_assert!(helper::<N>() < N);
}

fn const_match_only() {
    build_assert!(match LIMIT {
        4 => true,
        _ => false,
    });
}

fn const_comment_comma() {
    build_assert!(1 /* , */ < LIMIT);
}

fn const_comment_comma_msg() {
    build_assert!(1 /* , */ < LIMIT, "still const");
}

#[inline(always)]
fn runtime_dependent(offset: usize, n: usize) {
    build_assert!(offset < n);
}

fn runtime_through_helper(offset: usize) {
    runtime_dependent(offset, LIMIT);
}

fn main() {
    literal_const_only();
    const_generic_only::<LIMIT>();
    wrapper_const_only();
    helper_const_only::<LIMIT>();
    const_match_only();
    const_comment_comma();
    const_comment_comma_msg();
    runtime_dependent(OFFSET, LIMIT);
    runtime_through_helper(OFFSET);
}
