// check-pass


#[macro_export]
macro_rules! pr_info {
    ($($arg:tt)*) => {};
}

#[macro_export]
macro_rules! pr_cont {
    ($($arg:tt)*) => {};
}

fn main() {
    pr_info!("hello"); //~ WARN pr_* logging calls should end with a trailing "\n"
    pr_info!("hello\n");
    pr_cont!("hello");
    pr_info!("hello {}", "world"); //~ WARN pr_* logging calls should end with a trailing "\n"
    pr_info!("hello {}\n", "world");
}
