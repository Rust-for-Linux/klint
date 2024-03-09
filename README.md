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

To run this tool, use rustup which will prepare the necessary environment variables:
```
rustup run beta klint
```

klint is developed against latest nightly rustc; if you would like to use it with a stable Rust version, check the tagged releases.

`klint` will behave like rustc, just with additional lints.

## Implemented Lints

* [Infallible allocation](doc/infallible_allocation.md)
* [Atomic context](doc/atomic_context.md)
* [`build_error` checks](doc/build_error.md)
