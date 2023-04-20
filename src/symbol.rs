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
    drop_preempt_count,
    report_preempt_count,
    dump_mir,
    adjust,
    expect,
    unchecked,
    error,
    write,
    Write,
    task,
    Waker,
    wake,
    wake_by_ref,
}
