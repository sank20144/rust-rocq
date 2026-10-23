use std::cell::RefCell;
use std::collections::BTreeSet;
use std::mem;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::term::{self, Term};

pub struct Translator<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    regions: RefCell<BTreeSet<u32>>,
    file: RefCell<String>,
    adts_seen: RefCell<Vec<DefId>>,
}

impl<'tcx> Translator<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Translator {
            tcx,
            regions: RefCell::new(BTreeSet::new()),
            file: RefCell::new(String::new()),
            adts_seen: RefCell::new(Vec::new()),
        }
    }

    pub fn take_regions(&self) -> Vec<u64> {
        let taken = mem::take(&mut *self.regions.borrow_mut());
        taken.into_iter().map(u64::from).collect()
    }

    pub fn adts_seen(&self) -> Vec<DefId> {
        self.adts_seen.borrow().clone()
    }

    pub fn record_adt(&self, def_id: DefId) {
        if !self.adts_seen.borrow().contains(&def_id) {
            self.adts_seen.borrow_mut().push(def_id);
        }
    }

    pub fn record_region(&self, region: u32) {
        self.regions.borrow_mut().insert(region);
    }

    pub fn path(&self, def_id: DefId) -> Term {
        term::string(self.tcx.def_path_str(def_id))
    }

    pub fn set_file(&self, file: String) {
        *self.file.borrow_mut() = file;
    }

    pub fn file(&self) -> String {
        self.file.borrow().clone()
    }

    pub fn span_file(&self, span: Span) -> String {
        let source_map = self.tcx.sess.source_map();
        match source_map.lookup_line(span.lo()) {
            Ok(start) => source_map
                .filename_for_diagnostics(&start.sf.name)
                .to_string(),
            Err(_) => String::new(),
        }
    }

    pub fn span(&self, span: Span) -> Term {
        if span.is_dummy() {
            return term::atom("NoSpan");
        }
        let source_map = self.tcx.sess.source_map();
        let Ok(start) = source_map.lookup_line(span.lo()) else {
            return term::atom("NoSpan");
        };
        let Ok(end) = source_map.lookup_line(span.hi()) else {
            return term::atom("NoSpan");
        };
        let file = source_map
            .filename_for_diagnostics(&start.sf.name)
            .to_string();
        let mut args = vec![
            term::nat(start.line as u64 + 1),
            term::nat(source_map.lookup_char_pos(span.lo()).col_display as u64),
            term::nat(end.line as u64 + 1),
            term::nat(source_map.lookup_char_pos(span.hi()).col_display as u64),
        ];
        if file == *self.file.borrow() {
            term::app("Span", args)
        } else {
            args.insert(0, term::string(file));
            term::app("SpanIn", args)
        }
    }
}
