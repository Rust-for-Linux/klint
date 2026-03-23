#![allow(klint::build_assert_can_be_const)]
#![deny(klint::build_assert_not_inlined)]

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
static STATIC_LIMIT: usize = 8;

fn literal_const_only() {
    build_assert!(1 < LIMIT);
}

fn const_only_direct<const N: usize>() {
    build_assert!(OFFSET < N);
}

fn const_only_via_local() {
    let offset = LIMIT - 1;
    build_assert!(offset < LIMIT);
}

fn const_only_via_static() {
    let offset = STATIC_LIMIT - 1;
    build_assert!(offset < STATIC_LIMIT);
}

fn const_only_wrapper() {
    forward_build_assert!(OFFSET < LIMIT);
}

fn const_only_message_form() {
    build_assert!(OFFSET < LIMIT, "offset must stay in bounds");
}

fn const_helper<const N: usize>() -> usize {
    N - 1
}

fn const_only_helper_call<const N: usize>() {
    build_assert!(const_helper::<N>() < N);
}

#[unsafe(no_mangle)]
fn const_only_entry() {
    literal_const_only();
    const_only_direct::<4>();
    const_only_via_local();
    const_only_via_static();
    const_only_wrapper();
    const_only_helper_call::<LIMIT>();
}

fn runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}

fn passthrough(value: usize) -> usize {
    value
}

fn runtime_param_const_generic<const N: usize>(offset: usize) {
    build_assert!(offset < N);
}

fn runtime_helper_call<const N: usize>(offset: usize) {
    build_assert!(passthrough(offset) < N);
}

fn runtime_helper_caller(offset: usize) {
    runtime_helper_call::<LIMIT>(offset);
}

fn runtime_local(offset: usize, n: usize) {
    let current = offset;
    build_assert!(current < n);
}

fn runtime_match(offset: usize, n: usize) {
    build_assert!(match offset {
        0 => true,
        _ => offset < n,
    });
}

fn runtime_caller(offset: usize, n: usize) {
    runtime_direct(offset, n);
}

#[unsafe(no_mangle)]
fn runtime_entry() {
    runtime_caller(OFFSET, LIMIT);
    runtime_param_const_generic::<LIMIT>(OFFSET);
    runtime_helper_call::<LIMIT>(OFFSET);
    runtime_helper_caller(OFFSET);
    runtime_local(OFFSET, LIMIT);
    runtime_match(OFFSET, LIMIT);
}

fn runtime_wrapper(offset: usize, n: usize) {
    forward_build_assert!(offset < n);
}

fn runtime_wrapper_caller(offset: usize, n: usize) {
    runtime_wrapper(offset, n);
}

#[unsafe(no_mangle)]
fn wrapper_entry() {
    runtime_wrapper_caller(OFFSET, LIMIT);
}

#[inline(always)]
fn inline_runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}

#[unsafe(no_mangle)]
fn inline_runtime_entry() {
    inline_runtime_direct(OFFSET, LIMIT);
}

fn runtime_fnptr_target(offset: usize) {
    runtime_direct(offset, LIMIT);
}

fn fn_pointer_entry(offset: usize) {
    let f: fn(usize) = runtime_fnptr_target;
    f(offset);
}

fn fn_pointer_const_entry() {
    let f: fn(usize) = runtime_fnptr_target;
    f(OFFSET);
}

fn fn_pointer_mixed_calls(offset: usize) {
    let f: fn(usize) = runtime_fnptr_target;
    f(OFFSET);
    f(offset);
}

trait RuntimeDispatch {
    fn run(&self, offset: usize);
}

trait ConstRuntimeDispatch {
    fn run(&self);
}

struct RuntimeChecker;
struct ConstRuntimeChecker;

impl RuntimeDispatch for RuntimeChecker {
    fn run(&self, offset: usize) {
        runtime_direct(offset, LIMIT);
    }
}

impl ConstRuntimeDispatch for ConstRuntimeChecker {
    fn run(&self) {
        build_assert!(OFFSET < LIMIT);
    }
}

fn dyn_dispatch_entry(offset: usize) {
    let checker: &dyn RuntimeDispatch = &RuntimeChecker;
    checker.run(offset);
}

fn dyn_dispatch_const_entry() {
    let checker: &dyn RuntimeDispatch = &RuntimeChecker;
    checker.run(OFFSET);
}

fn dyn_dispatch_ambiguous_names(offset: usize) {
    let runtime_checker: &dyn RuntimeDispatch = &RuntimeChecker;
    let const_checker: &dyn ConstRuntimeDispatch = &ConstRuntimeChecker;
    const_checker.run();
    runtime_checker.run(offset);
}

fn partially_constant_caller(offset: usize) {
    runtime_direct(offset, LIMIT);
}

#[unsafe(no_mangle)]
#[inline(always)]
fn inline_wrapper(offset: usize) {
    partially_constant_caller(offset);
}
