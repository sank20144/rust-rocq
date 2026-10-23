use std::path::PathBuf;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::mir::pretty::MirWriter;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use rustc_span::RemapPathScopeComponents;

use crate::output::Output;
use crate::translator::Translator;
use crate::{items, output, polonius, store};

pub struct Frontend {
    pub out_dir: PathBuf,
    pub translate: bool,
    pub continue_compilation: bool,
}

impl Callbacks for Frontend {
    fn config(&mut self, config: &mut Config) {
        if self.translate {
            config.override_queries = Some(|_sess, providers| {
                providers.queries.mir_borrowck = store::mir_borrowck;
            });
        }
    }

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        if !self.translate {
            return Compilation::Continue;
        }

        let translator = Translator::new(tcx);
        let mut out = Output::new(&self.out_dir);

        let items = items::collect(&translator);
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
                translator.body(
                    def_id.to_def_id(),
                    &name,
                    &facts.body,
                    polonius::annotations(facts),
                ),
            );

            for (index, promoted) in facts.promoted.iter_enumerated() {
                let promoted_name = format!("{name}::promoted[{}]", index.as_u32());
                out.push_mir(&promoted_name, render_mir(tcx, promoted));
                out.push(
                    promoted_name.clone(),
                    translator.body(
                        def_id.to_def_id(),
                        &promoted_name,
                        promoted,
                        polonius::empty_annotations(),
                    ),
                );
            }
        }

        out.add_adts(items::external_adts(&translator));

        if out.is_empty() {
            return self.finished();
        }

        let crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        let source = compiler
            .sess
            .local_crate_source_file()
            .map(|f| output::source_name(f.path(RemapPathScopeComponents::DIAGNOSTICS)))
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

fn render_mir<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> String {
    let mut buffer = Vec::new();
    let writer = MirWriter::new(tcx);
    match writer.write_mir_fn(body, &mut buffer) {
        Ok(()) => String::from_utf8_lossy(&buffer).into_owned(),
        Err(e) => format!("// could not render: {e}\n"),
    }
}
