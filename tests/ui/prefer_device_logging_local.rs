// compile-flags: --crate-name kernel
#![deny(klint::prefer_device_logging)]
#![allow(unused_variables)]

pub mod device {
    pub struct Device;

    impl AsRef<Device> for Device {
        fn as_ref(&self) -> &Self {
            self
        }
    }
}

#[macro_export]
macro_rules! pr_info {
    ($($arg:tt)*) => {{ let _ = ::core::format_args!($($arg)*); }};
}

pub fn probe(dev: &device::Device) {
    pr_info!("local kernel crate\n");
}
