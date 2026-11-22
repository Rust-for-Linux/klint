// no-prefer-dynamic
// compile-flags: --emit=link

pub mod device {
    pub struct Device<C = ()>(pub C);

    impl<C> AsRef<Device<C>> for Device<C> {
        fn as_ref(&self) -> &Self {
            self
        }
    }
}

pub struct PciDevice(pub device::Device);

impl AsRef<device::Device> for PciDevice {
    fn as_ref(&self) -> &device::Device {
        &self.0
    }
}

#[macro_export]
macro_rules! pr_info {
    ($($arg:tt)*) => {{
        let _ = ::core::format_args!($($arg)*);
        let _ = 0;
    }};
}

#[macro_export]
macro_rules! pr_err {
    ($($arg:tt)*) => {{ let _ = ::core::format_args!($($arg)*); }};
}

#[macro_export]
macro_rules! pr_debug {
    ($($arg:tt)*) => {{ let _ = ::core::format_args!($($arg)*); }};
}

#[macro_export]
macro_rules! pr_cont {
    ($($arg:tt)*) => {{ let _ = ::core::format_args!($($arg)*); }};
}
