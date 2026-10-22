#![feature(rustc_private)]

extern crate polonius_engine;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_type_ir;

mod arguments;
mod body;
mod emit;
mod frontend;
mod items;
mod polonius;
mod rocq;
mod store;
mod ty;

use std::path::PathBuf;
use std::process::ExitCode;

use frontend::Frontend;

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().collect();
    let cargo_mode = std::env::var_os("RUST_ROCQ_CARGO_MODE").is_some();
    let include_deps = std::env::var_os("RUST_ROCQ_INCLUDE_DEPS").is_some();
    let is_primary_package = std::env::var_os("CARGO_PRIMARY_PACKAGE").is_some();
    let translate = !cargo_mode || include_deps || is_primary_package;

    let mut out_dir =
        std::env::var_os("RUST_ROCQ_OUT").map_or_else(|| PathBuf::from("out"), PathBuf::from);
    if let Some(i) = args.iter().position(|a| a == "--rocq-out") {
        if i + 1 < args.len() {
            out_dir = PathBuf::from(args.remove(i + 1));
        }
        args.remove(i);
    }

    if cargo_mode {
        args = arguments::without_incremental(args);
        if translate {
            out_dir = arguments::cargo_output_dir(out_dir, &args);
        }
    }

    if translate {
        if !args.iter().any(|a| a.starts_with("-Zverbose-internals")) {
            args.push("-Zverbose-internals".to_owned());
        }
    }

    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        if let Some(path) = arguments::sysroot() {
            args.push("--sysroot".to_owned());
            args.push(path);
        }
    }

    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(
            &args,
            &mut Frontend {
                out_dir,
                translate,
                continue_compilation: cargo_mode,
            },
        );
    })
}
