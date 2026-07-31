// Copyright Gary Guo.
//
// SPDX-License-Identifier: MIT OR Apache-2.0

extern crate compiletest_rs as compiletest;

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

fn run_ui_tests(bless: bool) {
    let mut config = compiletest::Config {
        bless,
        edition: Some("2024".into()),
        mode: compiletest::common::Mode::Ui,
        ..Default::default()
    };

    config.target_rustcflags = Some(
        [
            "-Zcrate-attr=feature(register_tool)",
            "-Zcrate-attr=register_tool(klint)",
            "--crate-type=lib",
            "-Zcrate-attr=no_std",
            "-Dklint::atomic_context",
            "--extern alloc",
            "--emit=obj",
            "-O",
            "-Cdebuginfo=1",
            "--cfg=CONFIG_FRAME_WARN=\"2048\"",
        ]
        .join(" "),
    );

    config.src_base = "tests/ui".into();
    config.build_base = PROFILE_PATH.join("test/ui");
    config.rustc_path = PROFILE_PATH.join("klint");
    config.link_deps(); // Populate config.target_rustcflags with dependencies on the path

    compiletest::run_tests(&config);
}

#[test]
fn compile_test() {
    let bless = env::var("BLESS").map_or(false, |x| !x.trim().is_empty());
    run_ui_tests(bless);
}
