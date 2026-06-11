<!--
SPDX-License-Identifier: MIT OR Apache-2.0
-->

# `assert_hierarchy`

This lint warns when an assertion can use a stronger compile-time assertion form.

The preference order is:

1. `static_assert!`
2. `const_assert!`
3. `build_assert!`

`static_assert!` is preferred when the condition is fully closed over compile-time context.
`const_assert!` is preferred when the condition is valid in a generic-aware const context but still
depends on generics or expression-local bindings. `build_assert!` is only needed once the condition
depends on variables or other non-const context.

## `build_assert!` To `static_assert!`

These trigger the lint with a `static_assert!` suggestion:

```rust
fn literal_const_only() {
    build_assert!(1 < LIMIT);
}
```

```rust
fn wrapper_const_only() {
    forward_build_assert!(OFFSET < LIMIT);
}
```

Macro-generated assertions can also trigger:

```rust
macro_rules! forward_const_check {
    ($expr:expr $(,)?) => {
        build_assert!($expr);
        let _x = 0usize;
    };
}

fn f<const N: usize>() {
    forward_const_check!(N > 0);
}
```

## `build_assert!` To `const_assert!`

These trigger the lint with a `const_assert!` suggestion:

```rust
fn const_generic_only<const N: usize>() {
    build_assert!(OFFSET < N);
}
```

```rust
const fn helper<const N: usize>() -> usize {
    N - 1
}

fn const_fn_helper_only<const N: usize>() {
    build_assert!(helper::<N>() < N);
}
```

## `const_assert!` To `static_assert!`

This also applies to `const_assert!` when it does not actually need generic-aware const context:

```rust
fn const_assert_static_only() {
    const_assert!(1 < LIMIT);
}
```

## Cases That Do Not Trigger

These do not trigger `assert_hierarchy`:

```rust
fn const_assert_generic<const N: usize>() {
    const_assert!(OFFSET < N);
}
```

```rust
fn runtime_direct(offset: usize, n: usize) {
    build_assert!(offset < n);
}
```

```rust
fn non_const_fn_helper<const N: usize>() {
    build_assert!(helper::<N>() < N);
}
```
