use std::env::{var, var_os};
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=src/codegen.rs.in");
    println!("cargo:rerun-if-changed=src/codegen.rs.tiny.in");
    println!("cargo:rerun-if-env-changed=GITHUB_ACTIONS");

    let actions = var("GITHUB_ACTIONS").unwrap_or_else(|_| "false".into());

    let mut src = PathBuf::from(var_os("CARGO_MANIFEST_DIR").unwrap());
    src.push("src");

    if actions == "true" {
        src.push("codegen.rs.tiny.in");
    } else {
        src.push("codegen.rs.in");
    }

    let mut dest = PathBuf::from(var_os("OUT_DIR").unwrap());
    dest.push("codegen.rs.in");

    std::fs::copy(src, dest).unwrap();
}
