use std::io::Result;
#[cfg(unix)]
use std::os::unix::process::CommandExt;

fn main() -> Result<()> {
    let mut cmd = std::process::Command::new(env!("RUSTDOC"));
    cmd.args(std::env::args().skip(1));

    #[cfg(unix)]
    return Err(cmd.exec());

    #[cfg(not(unix))]
    std::process::exit(cmd.status()?.code().unwrap_or(1));
}
