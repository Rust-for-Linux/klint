use std::io::Result;
use std::os::unix::process::CommandExt;

fn main() -> Result<()> {
    Err(std::process::Command::new(env!("RUSTDOC"))
        .args(std::env::args().skip(1))
        .exec())
}
