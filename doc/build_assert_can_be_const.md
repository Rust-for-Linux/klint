<!--
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# `build_assert_can_be_const`

This lint warns when a `build_assert!` condition is already effectively constant and can therefore
be written as a const assertion instead:

```rust
const {
    assert!(OFFSET < N, "offset must stay in bounds");
}
```

`build_assert!` is meant for conditions that cannot be checked in a plain const context, such as
conditions depending on function arguments that need to be optimized through an inline call chain.
If the condition does not depend on runtime values, using a const assert is clearer and fails
earlier.

## Literal and const-only cases

These trigger the lint because the assertion is already constant:

```rust
fn literal_const_only() {
    build_assert!(1 < LIMIT);
}
```

```rust
fn const_only_direct<const N: usize>() {
    build_assert!(OFFSET < N, "offset must stay in bounds");
}
```

## Wrapper macros

Simple wrapper macros do not hide the const-only case:

```rust
macro_rules! forward_build_assert {
    ($cond:expr) => {
        build_assert!($cond);
    };
}

fn const_only_wrapper() {
    forward_build_assert!(OFFSET < LIMIT);
}
```

## Local const-only helpers

The lint also tracks local helper return values:

```rust
fn helper<const N: usize>() -> usize {
    N - 1
}

fn const_only_helper<const N: usize>() {
    build_assert!(helper::<N>() < N);
}
```

Because the helper result still depends only on compile-time values, this should also use a const
assert instead of `build_assert!`.

## Runtime-dependent cases

These do not trigger `build_assert_can_be_const`:

```rust
fn runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}
```

```rust
fn runtime_param_const_generic<const N: usize>(offset: usize) {
    build_assert!(offset < N);
}
```

Those cases are the domain of [`build_assert_not_inlined`](build_assert_not_inlined.md), which
checks whether the non-constant assertion still has the required `#[inline(always)]` call chain.
