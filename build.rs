use std::env;
use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

#[must_use]
fn command_output(program: &Path, args: &[&str]) -> String {
    let output = Command::new(program)
        .args(args)
        .output()
        .unwrap_or_else(|e| panic!("could not run {}: {e}", program.display()));
    assert!(
        output.status.success(),
        "{} {} failed",
        program.display(),
        args.join(" ")
    );
    String::from_utf8(output.stdout)
        .expect("tool output was not UTF-8")
        .trim()
        .to_owned()
}

fn main() {
    let rustc = PathBuf::from(env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc")));
    let cargo = PathBuf::from(env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")));

    println!("cargo:rustc-env=RUST_ROCQ_CARGO={}", cargo.display());
    println!(
        "cargo:rustc-env=RUST_ROCQ_SYSROOT={}",
        command_output(&rustc, &["--print", "sysroot"])
    );
}
