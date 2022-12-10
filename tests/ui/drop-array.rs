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

struct SleepAndLockOnDrop;

impl Drop for SleepAndLockOnDrop {
    #[klint::preempt_count(adjust = 1, expect = 0, unchecked)]
    fn drop(&mut self) {}
}

#[klint::report_preempt_count]
fn drop_lock(x: Box<[LockOnDrop; 2]>) {}

#[klint::report_preempt_count]
fn drop_sleep(x: Box<[SleepOnDrop; 2]>) {}

fn drop_sleep_and_lock(x: Box<[SleepAndLockOnDrop; 2]>) {}
