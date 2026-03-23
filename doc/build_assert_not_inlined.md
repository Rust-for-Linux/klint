<!--
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# `build_assert_not_inlined`

This lint warns when a `build_assert!` condition depends on non-static values, but the function
containing that dependency is not marked `#[inline(always)]`.

`build_assert!` is only valid when the compiler can optimize away its error path. Const-only uses
do not need forced inlining, but once the condition depends on values flowing through a function
boundary, the surrounding call chain must stay inlineable.

## Const-only and const-generic cases

These do not trigger the lint because the condition is already effectively constant:

```rust
fn literal_const_only() {
    build_assert!(1 < 2);
}

fn const_only_direct<const N: usize>() {
    build_assert!(OFFSET < N);
}

fn const_only_wrapper() {
    helper_macro!(OFFSET < LIMIT);
}
```

These cases are covered by the separate
[`build_assert_can_be_const`](build_assert_can_be_const.md) lint, which suggests replacing
`build_assert!` with `const { assert!(...) }`.

## Runtime-dependent parameter flow

This does trigger the lint:

```rust
fn runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}
```

The same applies when only part of the condition is dynamic:

```rust
fn runtime_param_const_generic<const N: usize>(offset: usize) {
    build_assert!(offset < N);
}
```

## Local helper return-value flow

The lint tracks values through local helpers instead of treating every helper call as opaque:

```rust
fn passthrough(x: usize) -> usize {
    x
}

fn runtime_helper_call<const N: usize>(offset: usize) {
    build_assert!(passthrough(offset) < N);
}
```

By contrast, helpers that return only const-derived values do not trigger the lint:

```rust
fn const_helper<const N: usize>() -> usize {
    N - 1
}

fn const_only_helper_call<const N: usize>() {
    build_assert!(const_helper::<N>() < N);
}
```

## Wrapper macros

The lint identifies `build_assert!` through macro ancestry, so simple wrapper macros do not hide
the dependency:

```rust
macro_rules! helper_macro {
    ($cond:expr) => {
        build_assert!($cond);
    };
}

fn runtime_wrapper(offset: usize, n: usize) {
    helper_macro!(offset < n);
}
```

## Function pointers

The analysis also handles function pointers when it can resolve the local target:

```rust
fn runtime_fnptr_target(offset: usize) {
    runtime_direct(offset, LIMIT);
}

fn fn_pointer_entry(offset: usize) {
    let f: fn(usize) = runtime_fnptr_target;
    f(offset);
}
```

Const-only calls through function pointers stay quiet:

```rust
fn fn_pointer_const_entry() {
    let f: fn(usize) = runtime_fnptr_target;
    f(1);
}
```

## Dynamic dispatch

The lint uses monomorphized use edges to recover dyn-dispatch callsites:

```rust
trait RuntimeDispatch {
    fn run(&self, offset: usize);
}

trait ConstRuntimeDispatch {
    fn run(&self);
}

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

fn dyn_dispatch_ambiguous_names(offset: usize) {
    let runtime_checker: &dyn RuntimeDispatch = &RuntimeChecker;
    let const_checker: &dyn ConstRuntimeDispatch = &ConstRuntimeChecker;
    const_checker.run();
    runtime_checker.run(offset);
}
```

This also shows the ambiguous same-name trait-method case: a const-only `run()` method does not
hide the runtime-dependent `run(offset)` call.

## Propagation to callers

The lint is not limited to the function that directly contains `build_assert!`. If a callee's
`build_assert!` still depends on caller-provided values, the requirement propagates upward:

```rust
fn runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}

fn runtime_caller(offset: usize, n: usize) {
    runtime_direct(offset, n);
}
```

Both functions should be `#[inline(always)]`.

If a caller passes only effectively constant values, propagation stops there:

```rust
fn runtime_entry() {
    runtime_direct(1, 4);
}
```

This does not trigger the lint.
