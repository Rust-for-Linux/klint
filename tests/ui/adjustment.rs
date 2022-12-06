#![crate_type = "lib"]

struct Guard;

impl Drop for Guard {
    #[klint::preempt_count(adjust = -1, unchecked)]
    fn drop(&mut self) {}
}

struct Spinlock;

impl Spinlock {
    #[klint::preempt_count(adjust = 1, unchecked)]
    fn lock(&self) -> Guard {
        Guard
    }
}

fn test() {
    let lock = Spinlock;
    if true {
        std::mem::forget(lock.lock());
    }
}
