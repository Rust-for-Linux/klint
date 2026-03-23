<!--
Copyright Gary Guo.

SPDX-License-Identifier: MIT OR Apache-2.0
-->

klint
=====

Lints for kernel or embedded system development.

## Installation and Usage

Clone the repository and run `cargo install`:
```console
git clone https://github.com/Rust-for-Linux/klint.git
cd klint
cargo install --path .
```

Note that klint currently is pinned to a Rust version so it is likely that running `cargo install --git` will not work as it will not use the `rust-toolchain` file in the repository.

klint is developed against latest nightly rustc; if you would like to use it with a stable Rust version, check the tagged releases.

`klint` will behave like rustc, just with additional lints.

If you use `nix`, you can also build and run `klint` directly:
```console
nix run github:Rust-for-Linux/klint
```

## Run on Linux kernel

```console
cargo install --path .
```

`klint` is a tool and would need to be registered with `rustc`, to do so, apply [this patch](doc/kernel.patch) to the kernel tree.
This patch can be used even if plain rustc or clippy is used for kernel build.

To run this tool for Linux kernel build, use `make RUSTC=<path to klint>` to use klint in place of a Rust compiler.

If you compile kernel with rustdoc tests as kunit tests, you also need a matching version of `rustdoc`.
As it can be tricky to get the versions to match, `klint` provides a `klint-rustdoc` binary will execute the correct rustdoc.
You can add `RUSTDOC="<path to klint>-rustdoc"` to the make command.

`klint`'s atomic context checker is not lint-clean on Linux kernel tree.
If you want to check it out, you can opt into it with `-Dklint::atomic_context`.

## Implemented Lints

* [Infallible allocation](doc/infallible_allocation.md)
* [Atomic context](doc/atomic_context.md)
* [`build_error` checks](doc/build_error.md)
* [Stack frame size check](doc/stack_size.md)
* [Prelude check](doc/not_using_prelude.md)
* [`build_assert` not inlined](doc/build_assert_not_inlined.md)
