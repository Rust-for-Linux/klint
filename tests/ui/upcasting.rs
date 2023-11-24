#![crate_type="lib"]

#[klint::drop_preempt_count(expect = 0)]
trait A {}

#[klint::drop_preempt_count(expect = 1)]
trait B: A {}

fn upcast(x: &dyn B) -> &dyn A {
    x
}
