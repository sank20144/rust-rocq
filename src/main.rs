#![feature(rustc_private)]

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

mod rocq;
mod store;
mod ty;

use std::process::ExitCode;

use rustc_driver::Compilation;
use rustc_middle::ty::TyCtxt;

struct Frontend;

impl rustc_driver::Callbacks for Frontend {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_sess, providers| {
            providers.queries.mir_borrowck = store::mir_borrowck;
        });
    }

    fn after_analysis(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        for def_id in store::collected() {
            let Some(facts) = store::retrieve(tcx, def_id) else {
                continue;
            };
            let body = &facts.body;
            println!(
                "{} :: phase {:?}, {} blocks, {} locals, polonius facts {}",
                tcx.def_path_str(def_id),
                body.phase,
                body.basic_blocks.len(),
                body.local_decls.len(),
                if facts.input_facts.is_some() { "yes" } else { "no" },
            );
        }
        Compilation::Stop
    }
}

fn sysroot() -> Option<String> {
    if let Ok(path) = std::env::var("SYSROOT") {
        return Some(path);
    }
    let out = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()?;
    Some(String::from_utf8(out.stdout).ok()?.trim().to_owned())
}

fn main() -> ExitCode {
    let mut args: Vec<String> = std::env::args().collect();

    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        if let Some(path) = sysroot() {
            args.push("--sysroot".to_owned());
            args.push(path);
        }
    }

    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut Frontend);
    })
}
