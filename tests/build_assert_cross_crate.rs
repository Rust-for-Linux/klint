use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

fn temp_test_dir(name: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("klint-{name}-{unique}"));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write_file(path: &Path, contents: &str) {
    fs::write(path, contents).unwrap();
}

#[test]
fn build_assert_not_inlined_loads_cross_crate_summary() {
    let root = temp_test_dir("build-assert-cross-crate");
    let upstream = root.join("build_assert_upstream.rs");
    let downstream = root.join("build_assert_downstream.rs");
    let out_dir = root.join("out");
    fs::create_dir_all(&out_dir).unwrap();

    write_file(
        &upstream,
        r#"
#![feature(register_tool)]
#![register_tool(klint)]
#![allow(klint::build_assert_not_inlined)]

unsafe extern "C" {
    #[klint::diagnostic_item = "build_error"]
    safe fn rust_build_error();
}

#[klint::diagnostic_item = "build_assert"]
macro_rules! build_assert {
    ($expr:expr $(,)?) => {
        if !$expr {
            rust_build_error();
        }
    };
}

pub const LIMIT: usize = 8;

pub fn runtime_direct<T>(offset: usize, n: usize, _tag: T) {
    build_assert!(offset < n);
}

pub fn runtime_with_const_limit<T>(offset: usize, _tag: T) {
    build_assert!(offset < LIMIT);
}

pub fn unknown_fn_ptr<T>(offset: usize, f: fn(usize), _tag: T) {
    f(offset);
}
"#,
    );

    write_file(
        &downstream,
        r#"
#![feature(register_tool)]
#![register_tool(klint)]
#![allow(dead_code)]
#![deny(klint::build_assert_not_inlined)]

extern crate build_assert_upstream;

fn cross_crate_runtime_caller(offset: usize, n: usize) {
    build_assert_upstream::runtime_direct(offset, n, ());
}

fn cross_crate_partially_constant_caller(offset: usize) {
    build_assert_upstream::runtime_direct(offset, build_assert_upstream::LIMIT, ());
}

fn cross_crate_const_entry() {
    build_assert_upstream::runtime_direct(1, build_assert_upstream::LIMIT, ());
    build_assert_upstream::runtime_with_const_limit(1, ());
}

fn local_runtime_target(offset: usize) {
    build_assert_upstream::runtime_direct(offset, build_assert_upstream::LIMIT, ());
}

fn cross_crate_unknown_fn_ptr(offset: usize) {
    build_assert_upstream::unknown_fn_ptr(offset, local_runtime_target, ());
}
"#,
    );

    let klint = env!("CARGO_BIN_EXE_klint");

    let upstream_status = Command::new(klint)
        .env("RUSTC_BOOTSTRAP", "1")
        .arg(&upstream)
        .arg("--crate-name")
        .arg("build_assert_upstream")
        .arg("--crate-type")
        .arg("lib")
        .arg("--emit=metadata,obj")
        .arg("--out-dir")
        .arg(&out_dir)
        .status()
        .unwrap();
    assert!(upstream_status.success());

    let upstream_rmeta = out_dir.join("libbuild_assert_upstream.rmeta");
    assert!(upstream_rmeta.exists());
    assert!(
        out_dir
            .join("libbuild_assert_upstream.klint.rmeta")
            .exists()
    );

    let downstream_output = Command::new(klint)
        .env("RUSTC_BOOTSTRAP", "1")
        .arg(&downstream)
        .arg("--crate-name")
        .arg("build_assert_downstream")
        .arg("--crate-type")
        .arg("lib")
        .arg("--emit=metadata")
        .arg("--out-dir")
        .arg(&out_dir)
        .arg("--extern")
        .arg(format!(
            "build_assert_upstream={}",
            upstream_rmeta.display()
        ))
        .output()
        .unwrap();

    assert!(!downstream_output.status.success());

    let stderr = String::from_utf8_lossy(&downstream_output.stderr);
    assert!(stderr.contains("cross_crate_runtime_caller"), "{stderr}");
    assert!(
        stderr.contains("cross_crate_partially_constant_caller"),
        "{stderr}"
    );
    assert!(!stderr.contains("cross_crate_const_entry"), "{stderr}");
    assert!(!stderr.contains("cross_crate_unknown_fn_ptr"), "{stderr}");
}
