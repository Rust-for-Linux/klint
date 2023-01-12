#![crate_type="lib"]

#[klint::preempt_count(adjust = 1, unchecked)]
fn spin_lock() {}

trait MyTrait {
    fn foo(&self);
}

struct Good;

impl MyTrait for Good {
    fn foo(&self) {}
}

#[klint::preempt_count(adjust = 0)]
pub fn good() {
    let a: &'static dyn MyTrait = &Good;
    a.foo();
}

struct Bad;

impl MyTrait for Bad {
    fn foo(&self) {
        spin_lock();
    }
}

#[klint::preempt_count(adjust = 0)]
pub fn bad() {
    let a: &'static dyn MyTrait = &Bad;
    a.foo();
}

struct BadDrop;

impl MyTrait for BadDrop {
    fn foo(&self) {}
}

impl Drop for BadDrop {
    fn drop(&mut self) {
        spin_lock();
    }
}

#[klint::preempt_count(adjust = 0)]
pub fn bad_drop() {
    let _a: Box<dyn MyTrait> = Box::new(BadDrop);
}

trait AnnotatedTrait {
    #[klint::preempt_count(adjust = 1)]
    fn foo(&self);
}

struct AnnotatedGood;

impl AnnotatedTrait for AnnotatedGood {
    fn foo(&self) {
        spin_lock();
    }
}

#[klint::preempt_count(adjust = 1)]
pub fn annotated_good() {
    let a: &'static dyn AnnotatedTrait = &AnnotatedGood;
    a.foo();
}

struct AnnotatedBad;

impl AnnotatedTrait for AnnotatedBad {
    fn foo(&self) {}
}

#[klint::preempt_count(adjust = 1)]
pub fn annotated_bad() {
    let a: &'static dyn AnnotatedTrait = &AnnotatedBad;
    a.foo();
}
