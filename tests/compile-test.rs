#![feature(once_cell)]

extern crate compiletest_rs as compiletest;

use std::env;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::sync::LazyLock;

static PROFILE_PATH: LazyLock<PathBuf> = LazyLock::new(|| {
    let current_exe_path = env::current_exe().unwrap();
    let deps_path = current_exe_path.parent().unwrap();
    let profile_path = deps_path.parent().unwrap();
    profile_path.into()
});

fn run_ui_tests() -> std::thread::Result<()> {
    let mut config = compiletest::Config {
        edition: Some("2021".into()),
        mode: compiletest::common::Mode::Ui,
        ..Default::default()
    };

    config.target_rustcflags = Some(format!(
        "-Zcrate-attr=feature(register_tool) -Zcrate-attr=register_tool(klint)"
    ));

    config.src_base = "tests/ui".into();
    config.build_base = PROFILE_PATH.join("test/ui");
    config.rustc_path = PROFILE_PATH.join("klint");
    config.link_deps(); // Populate config.target_rustcflags with dependencies on the path

    std::panic::catch_unwind(|| {
        compiletest::run_tests(&config);
    })
}

fn bless_ui_tests() {
    let extensions = ["stdout", "stderr"].map(OsStr::new);
    let build_dir = PROFILE_PATH.join("test/ui");
    for file in std::fs::read_dir(&build_dir).unwrap() {
        let file = file.unwrap();
        if !file
            .path()
            .extension()
            .map_or(false, |ext| extensions.contains(&ext))
        {
            continue;
        }

        let ref_file_name = file.file_name().to_str().unwrap().replace(".stage-id", "");
        let ref_file_path = Path::new("tests/ui")
            .join(file.path().strip_prefix(&build_dir).unwrap())
            .with_file_name(ref_file_name);

        let new_file = std::fs::read(file.path()).unwrap();
        let old_file = std::fs::read(&ref_file_path).unwrap_or_default();

        if new_file != old_file {
            println!(
                "updating {} with {}",
                ref_file_path.display(),
                file.path().display()
            );
            std::fs::copy(file.path(), ref_file_path).expect("cannot update reference file");
        }
    }
}

#[test]
fn compile_test() {
    match run_ui_tests() {
        Ok(_) => (),
        Err(payload) => {
            let bless = env::var("BLESS").map_or(false, |x| !x.trim().is_empty());
            if bless {
                bless_ui_tests();
            }
            std::panic::resume_unwind(payload);
        }
    }
}
