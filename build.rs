fn main() {
    println!("cargo:rerun-if-changed=deps/libLLVM-18-rust-1.78.0-nightly.so");
    println!("cargo:rustc-link-search=deps");
}
