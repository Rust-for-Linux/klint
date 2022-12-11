#![crate_type = "lib"]
#![feature(allocator_api)]

use core::alloc::{AllocError, Allocator, Layout};
use core::ptr::NonNull;

struct TestAllocator;

unsafe impl Allocator for TestAllocator {
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        panic!();
    }

    #[inline]
    #[klint::preempt_count(expect = 0)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {}
}

struct SleepAndLockOnDrop;

impl Drop for SleepAndLockOnDrop {
    #[klint::preempt_count(adjust = 1, expect = 0, unchecked)]
    fn drop(&mut self) {}
}

fn drop_box(x: Box<SleepAndLockOnDrop, TestAllocator>) {}
