#![crate_type = "lib"]

struct LockOnDrop;

impl Drop for LockOnDrop {
    #[klint::preempt_count(adjust = 1, unchecked)]
    fn drop(&mut self) {}
}

struct SleepOnDrop;

impl Drop for SleepOnDrop {
    #[klint::preempt_count(expect = 0)]
    fn drop(&mut self) {}
}

fn drop_lock(x: Box<[LockOnDrop]>) {}

#[klint::report_preempt_count]
fn drop_sleep(x: Box<[SleepOnDrop]>) {}
