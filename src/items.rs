use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

use crate::rocq::{self, Term};
use crate::ty::Cx;

pub struct Items {
    pub adts: Vec<Term>,
    pub traits: Vec<Term>,
    pub impls: Vec<Term>,
}

pub fn collect(cx: &Cx<'_>) -> Items {
    let mut items = Items {
        adts: Vec::new(),
        traits: Vec::new(),
        impls: Vec::new(),
    };

    let mut ids: Vec<_> = cx.tcx.hir_crate_items(()).definitions().collect();
    ids.sort_by_key(|id| id.local_def_index.as_u32());

    for local in ids {
        let def_id = local.to_def_id();
        match cx.tcx.def_kind(local) {
            DefKind::Struct | DefKind::Enum | DefKind::Union => items.adts.push(cx.adt_def(def_id)),
            DefKind::Trait => items.traits.push(cx.trait_def(def_id)),
            DefKind::Impl { of_trait: true } => items.impls.push(cx.impl_def(def_id)),
            _ => {}
        }
    }

    let _ = cx.take_regions();
    items
}

pub fn external_adts(cx: &Cx<'_>) -> Vec<Term> {
    let mut done: Vec<DefId> = Vec::new();
    let mut adts = Vec::new();
    loop {
        let pending: Vec<DefId> = cx
            .adts_seen()
            .into_iter()
            .filter(|id| !id.is_local() && !done.contains(id))
            .collect();
        if pending.is_empty() {
            break;
        }
        for def_id in pending {
            done.push(def_id);
            adts.push(cx.adt_def(def_id));
        }
    }
    let _ = cx.take_regions();
    adts
}

impl<'tcx> Cx<'tcx> {
    fn adt_def(&self, def_id: DefId) -> Term {
        let adt = self.tcx.adt_def(def_id);
        let kind = if adt.is_enum() {
            "AkEnum"
        } else if adt.is_union() {
            "AkUnion"
        } else {
            "AkStruct"
        };

        let variants: Vec<Term> = adt
            .variants()
            .iter_enumerated()
            .map(|(idx, v)| {
                let discr = if adt.is_enum() {
                    adt.discriminant_for_variant(self.tcx, idx).val
                } else {
                    0
                };
                let fields: Vec<Term> = v
                    .fields
                    .iter()
                    .map(|f| {
                        let t = self.tcx.type_of(f.did).skip_binder();
                        rocq::pair(rocq::string(f.name.to_string()), self.ty(t))
                    })
                    .collect();
                rocq::app(
                    "VariantDef",
                    vec![
                        rocq::string(v.name.to_string()),
                        rocq::nat(idx.as_u32()),
                        rocq::bits(discr),
                        rocq::list(fields),
                    ],
                )
            })
            .collect();

        let repr = adt.repr();
        let mut reprs = Vec::new();
        if repr.c() {
            reprs.push(rocq::string("C"));
        }
        if repr.transparent() {
            reprs.push(rocq::string("transparent"));
        }
        if repr.packed() {
            reprs.push(rocq::string("packed"));
        }
        if let Some(int) = repr.int {
            reprs.push(rocq::string(format!("{int:?}")));
        }

        rocq::note(
            self.tcx.def_path_str(def_id),
            rocq::app(
                "AdtDef",
                vec![
                    rocq::note("path", self.path(def_id)),
                    rocq::note("kind", rocq::atom(kind)),
                    rocq::note("generics", self.generics(def_id)),
                    rocq::note("variants", rocq::list(variants)),
                    rocq::note("repr", rocq::list(reprs)),
                ],
            ),
        )
    }

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
                        rocq::string(item.opt_name().map_or_else(String::new, |n| n.to_string())),
                        self.path(item.def_id),
                        kind,
                        rocq::boolean(item.defaultness(self.tcx).has_value()),
                    ],
                )
            })
            .collect()
    }
}
