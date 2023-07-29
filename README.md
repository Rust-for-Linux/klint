klint
=====

Lints for kernel or embedded system development.

## Installation and Usage

Clone the repository and run `cargo install`:
```console
git clone https://github.com/nbdd0121/klint.git
cd klint
cargo install --path .
```

Note that klint currently is based on Rust 1.71 so it is likely that running `cargo install --git` will not work as it will not use the `rust-toolchain` file in the repository.

To run this tool, use rustup which will prepare the necessary environment variables:
```
rustup run 1.71.0 klint
```

`klint` will behave like rustc, just with additional lints.

## Implemented Lints

* [Infallible allocation](doc/infallible_allocation.md)
* [Atomic context](doc/atomic_context.md)
