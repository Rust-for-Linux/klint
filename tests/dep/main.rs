// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::env;
use std::path::PathBuf;
use std::sync::LazyLock;

static PROFILE_PATH: LazyLock<PathBuf> = LazyLock::new(|| {
    let current_exe_path = env::current_exe().unwrap();
    let components: Vec<_> = current_exe_path.components().collect();
    let target_idx = components
        .iter()
        .rposition(|x| x.as_os_str() == "target")
        .unwrap();
    let profile_path = components[..=target_idx + 1].iter().collect();
    profile_path
});

#[test]
fn run() {
    std::process::exit(
        std::process::Command::new("tests/dep/run.sh")
            .env("KLINT", PROFILE_PATH.join("klint"))
            .status()
            .unwrap()
            .code()
            .unwrap(),
    );
}
