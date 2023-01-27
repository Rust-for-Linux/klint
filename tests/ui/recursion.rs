#![crate_type = "lib"]

use std::sync::Arc;

#[klint::preempt_count(expect = 0)]
fn might_sleep() {}

#[klint::preempt_count(expect = 0)]
fn recursive_might_sleep() {
    if false {
        recursive_might_sleep();
    }
    might_sleep();
}

fn recursive_might_sleep_unannotated() {
    if false {
        recursive_might_sleep_unannotated();
    }
    might_sleep();
}

#[klint::drop_preempt_count(expect = 0)]
struct Recursive {
    a: Option<Arc<Recursive>>,
}

impl Drop for Recursive {
    fn drop(&mut self) {
        might_sleep();
    }
}

fn drop_recur(recur: Arc<Recursive>) {}
