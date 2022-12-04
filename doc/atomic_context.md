# Atomic context

This lint will error on calls that violate [kernel locking rules](https://docs.kernel.org/locking/locktypes.html).

Conceptually this lint tracks the kernel `preempt_count` statically. All functions have two properties, first is the adjustment to the `preempt_count` that happens after calling the function, and the second is the expectation of `preempt_count` at the entrance to the function. The lint will keep track of the `preempt_count` within the function call, and error if the expectation is not met.

For example, this code is invalid:
```rust
let guard = spinlock.lock();
sleep();
```
because acquiring a spinlock disables preemption, but `sleep` expects preemption to be enabled.

With `Spinlock::lock` being annotated with `#[klint::preempt_count(adjust = 1)]` and `sleep` being annotated with `#[klint::preempt_count(expect = 0)]`, the lint will generate the following error:
```
error: this call expects the preemption count to be 0
 --> example.rs:2:1
  |
2 | sleep();
  | ^^^^^^^
  |
  = note: but the possible preemption count at this point is 1..
```
