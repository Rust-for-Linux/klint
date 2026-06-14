<!--
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# `build_assert_not_inlined`

This lint warns when a `build_assert!` condition depends on non-static values, but the function
carrying that dependency is not marked `#[inline(always)]`.

`build_assert!` is only valid when the compiler can optimize away its error path. Const-only uses
do not need forced inlining, but once the condition depends on values flowing through a function
boundary, the relevant call chain must stay inlineable.

## Const-only cases

These do not trigger the lint because the condition is effectively constant:

```rust
fn literal_const_only() {
    build_assert!(1 < LIMIT);
}

fn const_only_direct<const N: usize>() {
    build_assert!(OFFSET < N);
}

fn const_only_wrapper() {
    forward_build_assert!(OFFSET < LIMIT);
}
```

The same applies when the value only flows through local constants or statics:

```rust
fn const_only_via_local() {
    let offset = LIMIT - 1;
    build_assert!(offset < LIMIT);
}

fn const_only_via_static() {
    let offset = STATIC_LIMIT - 1;
    build_assert!(offset < STATIC_LIMIT);
}
```

## Direct runtime-dependent conditions

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

And it also applies when the runtime dependency is buried in a larger expression:

```rust
fn runtime_match(offset: usize, n: usize) {
    build_assert!(match offset {
        0 => true,
        _ => offset < n,
    });
}
```

## Local helper flow

The lint tracks values through local helpers instead of treating every helper call as opaque:

```rust
fn passthrough(value: usize) -> usize {
    value
}

fn runtime_helper_call<const N: usize>(offset: usize) {
    build_assert!(passthrough(offset) < N);
}
```

Boolean helper predicates are treated the same way:

```rust
fn runtime_predicate_helper(offset: usize, n: usize) -> bool {
    offset < n
}

fn runtime_predicate_helper_call(offset: usize, n: usize) {
    build_assert!(runtime_predicate_helper(offset, n));
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
macro_rules! forward_build_assert {
    ($cond:expr $(,)?) => {
        build_assert!($cond)
    };
}

fn runtime_wrapper(offset: usize, n: usize) {
    forward_build_assert!(offset < n);
}
```

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

The same applies to partially constant callers:

```rust
fn partially_constant_caller(offset: usize) {
    runtime_direct(offset, LIMIT);
}
```

If a caller passes only effectively constant values, propagation stops there:

```rust
fn runtime_entry() {
    runtime_direct(OFFSET, LIMIT);
}
```

This does not trigger the lint.

## Trait and default methods

The lint applies to trait methods and default methods in the same way as ordinary functions:

```rust
trait RuntimeDispatch {
    fn run(&self, offset: usize);
}

impl RuntimeDispatch for RuntimeChecker {
    fn run(&self, offset: usize) {
        runtime_direct(offset, LIMIT);
    }
}
```

Default methods that directly contain a runtime-dependent `build_assert!` also trigger:

```rust
trait IoKnownSize: Io {
    const MIN_SIZE: usize;

    fn io_addr_assert<U>(&self, offset: usize) -> usize {
        build_assert!(offset_valid::<U>(offset, Self::MIN_SIZE));
        self.addr() + offset
    }
}

fn trait_default_method_entry(offset: usize) {
    let io = FakeIo;
    let _ = io.io_addr_assert::<u32>(offset);
}
```

## Indirect calls

Indirect calls are handled conservatively.

A direct function that itself depends on `build_assert!` still triggers:

```rust
fn runtime_fnptr_target(offset: usize) {
    runtime_direct(offset, LIMIT);
}
```

But an indirect call through a function pointer is not, by itself, treated as a proven
`build_assert!` dependency:

```rust
fn fn_pointer_entry(offset: usize) {
    let f: fn(usize) = runtime_fnptr_target;
    f(offset);
}
```

Likewise, trait-object callsites are kept conservative unless the dependency is proven in the
method body or through ordinary caller propagation.
