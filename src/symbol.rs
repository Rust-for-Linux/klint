// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

#![allow(non_upper_case_globals)]

use rustc_span::Symbol;
use rustc_span::symbol::PREDEFINED_SYMBOLS_COUNT;

macro_rules! def {
    ($($name: ident,)*) => {
        pub const EXTRA_SYMBOLS: &[&str] = &[$(stringify!($name),)*];

        $(pub const $name: Symbol = Symbol::new(PREDEFINED_SYMBOLS_COUNT + ${index()});)*

        // Use two glob imports to ensure that there're no conflicts between symbols here and predefined symbols;
        const _: () = {
            #[expect(unused)]
            use rustc_span::sym::*;
            use crate::symbol::*;

            $(const _: Symbol = $name;)*
        };
    };
}

def! {
    klint,
    preempt_count,
    drop_preempt_count,
    report_preempt_count,
    dump_mir,
    adjust,
    unchecked,
    Any,
    error,
    Error,
    write,
    Write,
    task,
    wake,
    wake_by_ref,
    Waker,
    sort,
    quicksort,
    partition,
    kernel,
    diagnostic_item,

    any_context,
    atomic_context,
    atomic_context_only,
    process_context,

    // Diagnostic items
    c_str,
    build_error,
    build_assert,
    const_assert,
    static_assert,

    CONFIG_FRAME_WARN,
}
