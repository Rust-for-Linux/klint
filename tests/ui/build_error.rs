#![allow(klint::assert_hierarchy)]
unsafe extern "C" {
    #[klint::diagnostic_item = "build_error"]
    safe fn rust_build_error();
}

macro_rules! build_assert {
    ($expr:expr) => {
        if !$expr {
            rust_build_error();
        }
    }
}

#[inline]
fn inline_call() {
    build_assert!(false);
}

#[unsafe(no_mangle)]
fn gen_build_error() {
    inline_call();
}
