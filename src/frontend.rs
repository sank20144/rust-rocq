use std::path::PathBuf;

use rustc_driver::Compilation;
use rustc_middle::ty::TyCtxt;

use crate::{emit, items, polonius, store, ty};

pub struct Frontend {
    pub out_dir: PathBuf,
    pub translate: bool,
    pub continue_compilation: bool,
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
            (
                "debug-assertions",
                tcx.sess.opts.debug_assertions.to_string(),
            ),
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

        out.add_adts(items::external_adts(&cx));

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
                compiler
                    .sess
                    .dcx()
                    .fatal(format!("could not write output: {e}"));
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
