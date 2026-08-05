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

mod body;
mod emit;
mod items;
mod polonius;
mod rocq;
mod store;
mod ty;

use std::path::PathBuf;
use std::process::ExitCode;

use rustc_driver::Compilation;
use rustc_middle::ty::TyCtxt;

struct Frontend {
    out_dir: PathBuf,
}

impl rustc_driver::Callbacks for Frontend {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.override_queries = Some(|_sess, providers| {
            providers.queries.mir_borrowck = store::mir_borrowck;
        });
    }

    fn after_analysis(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        let cx = ty::Cx::new(tcx);
        let mut out = emit::Output::new(&self.out_dir);

        let (traits, impls) = items::collect(&cx);
        out.set_items(traits, impls);

        for def_id in store::collected() {
            let Some(facts) = store::retrieve(tcx, def_id) else {
                continue;
            };
            let name = tcx.def_path_str(def_id);
            out.push(name.clone(), cx.body(def_id.to_def_id(), &name, &facts.body, polonius::facts(facts)));

            for (idx, promoted) in facts.promoted.iter_enumerated() {
                let pname = format!("{name}::promoted[{}]", idx.as_u32());
                out.push(pname.clone(), cx.body(def_id.to_def_id(), &pname, promoted, polonius::empty_facts()));
            }
        }

        if out.is_empty() {
            return Compilation::Stop;
        }

        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
        let source = compiler
            .sess
            .local_crate_source_file()
            .map(|f| emit::source_name(f.path(rustc_span::RemapPathScopeComponents::DIAGNOSTICS)))
            .unwrap_or_else(|| "input".to_owned());

        match out.write(&crate_name, &source) {
            Ok(path) => eprintln!("rust-rocq: wrote {}", path.display()),
            Err(e) => {
                compiler.sess.dcx().fatal(format!("could not write output: {e}"));
            }
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

    let mut out_dir = PathBuf::from("out");
    if let Some(i) = args.iter().position(|a| a == "--rocq-out") {
        if i + 1 < args.len() {
            out_dir = PathBuf::from(args.remove(i + 1));
        }
        args.remove(i);
    }

    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        if let Some(path) = sysroot() {
            args.push("--sysroot".to_owned());
            args.push(path);
        }
    }

    rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut Frontend { out_dir });
    })
}
