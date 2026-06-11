#![deny(klint::assert_hierarchy)]

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

macro_rules! forward_const_check {
    ($expr:expr $(,)?) => {
        build_assert!($expr);
        let _x = 0usize;
    };
}

macro_rules! const_assert {
    ($expr:expr $(,)?) => {
        const {
            assert!($expr);
        }
    };
}

macro_rules! impl_runtime_check {
    () => {
        fn macro_generated_runtime(n: usize) {
            build_assert!(n < LIMIT);
        }
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

// Macro-generated assertions still lint based on the expanded condition.
fn wrapper_const_generic<const N: usize>() {
    forward_const_check!(N > 0);
}

const fn const_helper<const N: usize>() -> usize {
    N - 1
}

fn const_fn_helper_only<const N: usize>() {
    build_assert!(const_helper::<N>() < N);
}

fn helper<const N: usize>() -> usize {
    N - 1
}

fn non_const_fn_helper<const N: usize>() {
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

fn local_binding_from_outer_scope() {
    let offset = OFFSET;
    build_assert!(offset < LIMIT);
}

fn local_binding_inside_condition() {
    build_assert!({
        let offset = OFFSET;
        offset < LIMIT
    });
}

fn const_assert_static_only() {
    const_assert!(1 < LIMIT);
}

fn const_assert_generic<const N: usize>() {
    const_assert!(OFFSET < N);
}

#[inline(always)]
fn runtime_dependent(offset: usize, n: usize) {
    build_assert!(offset < n);
}

fn runtime_through_helper(offset: usize) {
    runtime_dependent(offset, LIMIT);
}

impl_runtime_check!();

fn main() {
    literal_const_only();
    const_generic_only::<LIMIT>();
    wrapper_const_only();
    wrapper_const_generic::<LIMIT>();
    const_fn_helper_only::<LIMIT>();
    non_const_fn_helper::<LIMIT>();
    const_match_only();
    const_comment_comma();
    const_comment_comma_msg();
    local_binding_from_outer_scope();
    local_binding_inside_condition();
    const_assert_static_only();
    const_assert_generic::<LIMIT>();
    runtime_dependent(OFFSET, LIMIT);
    runtime_through_helper(OFFSET);
    macro_generated_runtime(OFFSET);
}
