// aux-build: kernel.rs
// compile-flags: --extern kernel
#![deny(klint::prefer_device_logging)]
#![allow(unused_variables, dead_code)]
#![deny(unfulfilled_lint_expectations)]

use kernel::device::Device;
use kernel::{pr_debug, pr_err, pr_info};

fn parameter(dev: &Device) {
    pr_info!("probe {}\n", 1);
    pr_err!("failure\n");
    pr_debug!("debug\n");
}

fn wrapper(dev: &kernel::PciDevice) {
    pr_info!("wrapper\n");
}

fn generic_context<C>(dev: &Device<C>) {
    pr_info!("generic context\n");
}

fn generic_wrapper<T: AsRef<Device>>(dev: &T) {
    pr_info!("generic wrapper\n");
}

fn local() {
    let backing = Device(());
    pr_info!("no reference yet\n"); // No warning for the owned value.
    let dev = &backing;
    pr_info!("local\n");
    let dev = 123;
    pr_info!("shadowed\n"); // No warning for the shadowed reference.
}

fn scopes() {
    let backing = Device(());
    {
        let dev = &backing;
        pr_info!("inner\n");
    }
    pr_info!("out of scope\n");
    let dev = &backing;
    fn nested() {
        pr_info!("cannot capture dev\n");
    }
    pr_info!("outer\n");
}

fn patterns(value: Option<&Device>) {
    match value {
        Some(dev) => pr_info!("match\n"),
        None => pr_info!("no device\n"),
    }
    if let Some(dev) = value {
        pr_info!("if let\n");
    } else {
        pr_info!("else\n");
    }
    while let Some(dev) = value {
        pr_info!("while let\n");
        break;
    }
}

#[allow(klint::prefer_device_logging)]
fn suppressed(dev: &Device) {
    pr_info!("allowed\n");
}

#[expect(klint::prefer_device_logging)]
fn expected(dev: &Device) {
    pr_info!("expected\n");
}

fn alias(device: &Device) {
    use kernel::pr_info as info;
    info!("renamed macro\n");
}

macro_rules! wrapper_macro {
    () => { kernel::pr_info!("generated\n") };
}

fn generated(dev: &Device) {
    wrapper_macro!(); // Leave logging inside another macro alone.
    kernel::pr_cont!("continued\n"); // No direct dev_* equivalent.
}

fn unrelated(dev: &u32) {
    pr_info!("not a device\n");
}

fn unrelated_macro(dev: &Device) {
    macro_rules! pr_info {
        ($($arg:tt)*) => { let _ = ::core::format_args!($($arg)*); };
    }
    pr_info!("unrelated macro\n");
}

fn initializer(dev: &Device) {
    let dev = { pr_info!("old binding still visible\n"); 1 };
    pr_info!("new binding is not a device\n");
}

fn closures(dev: &Device) {
    let _ = || pr_info!("outer device can be captured\n");
    let _ = |dev: u32| pr_info!("closure shadows outer device\n");
    let _ = |device: &Device| pr_info!("closure argument\n");
}

fn let_chain(value: Option<&Device>) {
    if let Some(dev) = value && { pr_info!("condition\n"); true } {
        pr_info!("then branch\n");
    } else {
        pr_info!("else branch\n");
    }
}

fn non_reference(mut dev: Device) {
    pr_info!("owned device\n");
    let raw = &raw const dev;
    pr_info!("raw device pointer\n");
    let dev = &mut dev;
    pr_info!("mutable reference may have been moved\n");
}

fn uninitialized() {
    let dev: &Device;
    pr_info!("not initialized\n");
}

fn not_declared_yet(backing: Device) {
    pr_info!("not declared yet\n");
    let dev = &backing;
}
