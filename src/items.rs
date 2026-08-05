use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

use crate::rocq::{self, Term};
use crate::ty::Cx;

pub fn collect(cx: &Cx<'_>) -> (Vec<Term>, Vec<Term>) {
    let mut traits = Vec::new();
    let mut impls = Vec::new();

    let mut ids: Vec<_> = cx.tcx.hir_crate_items(()).definitions().collect();
    ids.sort_by_key(|id| id.local_def_index.as_u32());

    for local in ids {
        let def_id = local.to_def_id();
        match cx.tcx.def_kind(local) {
            DefKind::Trait => traits.push(cx.trait_def(def_id)),
            DefKind::Impl { of_trait: true } => impls.push(cx.impl_def(def_id)),
            _ => {}
        }
    }

    let _ = cx.take_regions();
    (traits, impls)
}

impl<'tcx> Cx<'tcx> {
    fn trait_def(&self, def_id: DefId) -> Term {
        rocq::note(
            self.tcx.def_path_str(def_id),
            rocq::app(
                "TraitDef",
                vec![
                    rocq::note("path", self.path(def_id)),
                    rocq::note("generics", self.generics(def_id)),
                    rocq::note("bounds", self.bounds(def_id)),
                    rocq::note("items", rocq::list(self.assoc_items(def_id))),
                ],
            ),
        )
    }

    fn impl_def(&self, def_id: DefId) -> Term {
        let trait_ref = self.tcx.impl_trait_ref(def_id).skip_binder();
        let negative = matches!(self.tcx.impl_polarity(def_id), ty::ImplPolarity::Negative);

        let mapped: Vec<Term> = self
            .tcx
            .associated_items(def_id)
            .in_definition_order()
            .filter_map(|item| {
                let of = item.trait_item_def_id()?;
                Some(rocq::pair(self.path(of), self.path(item.def_id)))
            })
            .collect();

        rocq::note(
            self.tcx.def_path_str(def_id),
            rocq::app(
                "ImplDef",
                vec![
                    rocq::note("path", self.path(def_id)),
                    rocq::note("trait", self.path(trait_ref.def_id)),
                    rocq::note("args", self.generic_args(trait_ref.args)),
                    rocq::note("generics", self.generics(def_id)),
                    rocq::note("bounds", self.bounds(def_id)),
                    rocq::note("items", rocq::list(mapped)),
                    rocq::note("negative", rocq::boolean(negative)),
                ],
            ),
        )
    }

    fn assoc_items(&self, def_id: DefId) -> Vec<Term> {
        self.tcx
            .associated_items(def_id)
            .in_definition_order()
            .map(|item| {
                let kind = match item.kind {
                    ty::AssocKind::Fn { has_self, .. } => {
                        rocq::app("AiFn", vec![rocq::boolean(has_self)])
                    }
                    ty::AssocKind::Const { .. } => rocq::atom("AiConst"),
                    ty::AssocKind::Type { .. } => rocq::atom("AiType"),
                };
                rocq::app(
                    "AssocItem",
                    vec![
                        rocq::string(
                            item.opt_name().map_or_else(String::new, |n| n.to_string()),
                        ),
                        self.path(item.def_id),
                        kind,
                        rocq::boolean(item.defaultness(self.tcx).has_value()),
                    ],
                )
            })
            .collect()
    }
}
