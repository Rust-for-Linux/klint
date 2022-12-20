#![allow(non_upper_case_globals)]

use rustc_span::Symbol;
use std::sync::LazyLock;

macro_rules! def {
    ($($name: ident,)*) => {
        $(pub static $name: LazyLock<Symbol> = LazyLock::new(|| Symbol::intern(stringify!($name)));)*
    };
}

def! {
    klint,
    preempt_count,
    report_preempt_count,
    adjust,
    expect,
    unchecked,
    write,
    Write,
    Waker,
    wake,
    wake_by_ref,
}
