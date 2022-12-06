#![crate_type = "lib"]

#[klint::preempt_count]
fn a() {}

#[klint::preempt_count()]
fn b() {}

#[klint::preempt_count(adjust = )]
fn c() {}

#[klint::preempt_count(expect = )]
fn d() {}

#[klint::preempt_count(expect = ..)]
fn e() {}

#[klint::preempt_count(unchecked)]
fn f() {}
