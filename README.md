klint
=====

Lints for kernel or embedded system development.

## Installation and Usage

You'll first need to install `rustc-dev` and `llvm-tools-preview` through rustup:
```console
$ rustup component add rustc-dev llvm-tools-preview
```

Then install via Cargo:
```console
$ cargo install --git https://github.com/nbdd0121/klint.git
```

To run this tool, use rustup which will prepare the necessary environment variables:
```
rustup run nightly klint
```

`klint` will behave like rustc, just with additional lints.

## Implemented Lints

* [Infallible allocation](doc/infallible_allocation.md)
