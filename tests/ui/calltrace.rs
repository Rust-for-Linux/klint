#![crate_type = "lib"]

struct LockOnDrop;

impl Drop for LockOnDrop {
    #[klint::preempt_count(adjust = 1, unchecked)]
    fn drop(&mut self) {}
}

#[klint::preempt_count(expect = 0)]
fn might_sleep() {}

fn problematic<T>(x: T) {
    drop(x);
    might_sleep();
}

fn wrapper<T>(x: T) {
    problematic(x);
}

pub fn this_is_fine() {
    wrapper(Vec::<i32>::new());
}

pub fn this_is_not() {
    wrapper(LockOnDrop);
}
