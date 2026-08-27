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
    translate: bool,
    continue_compilation: bool,
}

impl rustc_driver::Callbacks for Frontend {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        if self.translate {
            config.override_queries = Some(|_sess, providers| {
                providers.queries.mir_borrowck = store::mir_borrowck;
            });
        }
    }

    fn after_analysis(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'_>,
    ) -> Compilation {
        if !self.translate {
            return Compilation::Continue;
        }

        let cx = ty::Cx::new(tcx);
        let mut out = emit::Output::new(&self.out_dir);

        let items = items::collect(&cx);
        out.set_items(items.adts, items.traits, items.impls);
        out.set_build_flags(vec![
            ("overflow-checks", tcx.sess.overflow_checks().to_string()),
            ("debug-assertions", tcx.sess.opts.debug_assertions.to_string()),
            ("opt-level", format!("{:?}", tcx.sess.opts.optimize)),
        ]);

        for def_id in store::collected() {
            let Some(facts) = store::retrieve(tcx, def_id) else {
                continue;
            };
            let name = tcx.def_path_str(def_id);
            out.push_mir(&name, render_mir(tcx, &facts.body));
            out.push(
                name.clone(),
                cx.body(
                    def_id.to_def_id(),
                    &name,
                    &facts.body,
                    polonius::annotations(facts),
                ),
            );

            for (idx, promoted) in facts.promoted.iter_enumerated() {
                let pname = format!("{name}::promoted[{}]", idx.as_u32());
                out.push_mir(&pname, render_mir(tcx, promoted));
                out.push(
                    pname.clone(),
                    cx.body(
                        def_id.to_def_id(),
                        &pname,
                        promoted,
                        polonius::empty_annotations(),
                    ),
                );
            }
        }

        if out.is_empty() {
            return self.finished();
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

        self.finished()
    }
}

impl Frontend {
    fn finished(&self) -> Compilation {
        if self.continue_compilation {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn render_mir<'tcx>(tcx: TyCtxt<'tcx>, body: &rustc_middle::mir::Body<'tcx>) -> String {
    let mut buf = Vec::new();
    let writer = rustc_middle::mir::pretty::MirWriter::new(tcx);
    match writer.write_mir_fn(body, &mut buf) {
        Ok(()) => String::from_utf8_lossy(&buf).into_owned(),
        Err(e) => format!("// could not render: {e}\n"),
    }
}

fn sysroot() -> Option<String> {
    if let Ok(path) = std::env::var("SYSROOT") {
        return Some(path);
    }
    Some(env!("RUST_ROCQ_SYSROOT").to_owned())
}

fn without_incremental(args: Vec<String>) -> Vec<String> {
    let mut filtered = Vec::with_capacity(args.len());
    let mut args = args.into_iter();
    while let Some(arg) = args.next() {
        if arg == "-C" || arg == "--codegen" {
            let Some(value) = args.next() else {
                filtered.push(arg);
                break;
            };
            if !value.starts_with("incremental=") {
                filtered.push(arg);
                filtered.push(value);
            }
        } else if arg.starts_with("-Cincremental=")
            || arg.starts_with("--codegen=incremental=")
        {
            continue;
        } else {
            filtered.push(arg);
        }
    }
    filtered
}

fn option_value(args: &[String], name: &str) -> Option<String> {
    for (i, arg) in args.iter().enumerate() {
        if arg == name {
            return args.get(i + 1).cloned();
        }
        if let Some(value) = arg.strip_prefix(&format!("{name}=")) {
            return Some(value.to_owned());
        }
    }
    None
}

fn codegen_value(args: &[String], name: &str) -> Option<String> {
    let prefix = format!("{name}=");
    for (i, arg) in args.iter().enumerate() {
        if arg == "-C" || arg == "--codegen" {
            if let Some(value) = args.get(i + 1).and_then(|v| v.strip_prefix(&prefix)) {
                return Some(value.to_owned());
            }
        }
        if let Some(value) = arg.strip_prefix(&format!("-C{prefix}")) {
            return Some(value.to_owned());
        }
        if let Some(value) = arg.strip_prefix(&format!("--codegen={prefix}")) {
            return Some(value.to_owned());
        }
    }
    None
}

fn path_component(value: &str) -> String {
    let component: String = value
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();
    if component.is_empty() {
        "unknown".to_owned()
    } else {
        component
    }
}

fn cargo_output_dir(base: PathBuf, args: &[String]) -> PathBuf {
    let crate_name = option_value(args, "--crate-name").unwrap_or_else(|| "crate".to_owned());
    let metadata = codegen_value(args, "metadata").unwrap_or_else(|| "default".to_owned());
    base.join(path_component(&crate_name))
        .join(path_component(&metadata))
}

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
        args = without_incremental(args);
        if translate {
            out_dir = cargo_output_dir(out_dir, &args);
        }
    }

    if translate {
        if !args.iter().any(|a| a.starts_with("-Zverbose-internals")) {
            args.push("-Zverbose-internals".to_owned());
        }
    }

    if !args.iter().any(|a| a.starts_with("--sysroot")) {
        if let Some(path) = sysroot() {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn removes_split_and_joined_incremental_options() {
        assert_eq!(
            without_incremental(strings(&[
                "rustc",
                "-C",
                "incremental=target/incremental",
                "-Copt-level=2",
                "--codegen=incremental=other",
                "input.rs",
            ])),
            strings(&["rustc", "-Copt-level=2", "input.rs"])
        );
    }

    #[test]
    fn cargo_output_uses_crate_name_and_metadata() {
        let output = cargo_output_dir(
            PathBuf::from("out"),
            &strings(&["--crate-name", "my_crate", "-C", "metadata=abc123"]),
        );
        assert_eq!(output, PathBuf::from("out/my_crate/abc123"));
    }
}
