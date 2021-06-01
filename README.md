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

### Infallible allocation

This lint will warn on any call that could potentially lead to invocation of the OOM handler.

The lint works on monomorphized MIR and therefore can detect all kinds of uses, including indirect calls:

```rust
fn test<'a, F: From<&'a str>>(x: &'a str) -> F {
    x.into()
}

fn test_dyn(x: &mut dyn for<'a> std::ops::AddAssign<&'a str>) {
    x.add_assign("A");
}

// Ok
let _ = String::new();

// Warning
let mut s: String = "str".into();

// Warning
s += "A";

// Warning. Going through generics wouldn't trick the tool.
let _: String = test("str");

// Warning. Using dynamic dispatch wouldn't trick the tool.
test_dyn(&mut String::new());

// Warning. Using function pointers wouldn't trick the tool.
let f: fn(&'static str) -> String = From::from;
f("A");
```

You can opt-out from the warning by letting a function of which name contains `assume_fallible` to call fallible functions instead:
```rust
fn assume_fallible<T, F: FnOnce() -> T>(f: F) -> T {
    f()
}

// Ok. The function `assume_fallible` will exempt the function called by it.
assume_fallible(|| {
    test_dyn(&mut String::new());
});
```
