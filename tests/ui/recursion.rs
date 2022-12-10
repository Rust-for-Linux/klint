#![crate_type = "lib"]

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
