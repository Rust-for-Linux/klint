#![crate_type="lib"]

#[klint::preempt_count(adjust = 1, unchecked)]
fn spin_lock() {}

fn okay() {

}

fn not_okay() {
    spin_lock();
}

#[klint::preempt_count(adjust = 0)]
pub fn good() {
    let a: fn() = okay;
    a();
}

#[klint::preempt_count(adjust = 0)]
pub fn bad() {
    let a: fn() = not_okay;
    a();
}
