use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;

use crate::term::{self, Term};
use crate::translator::Translator;

pub struct Items {
    pub adts: Vec<Term>,
    pub traits: Vec<Term>,
    pub impls: Vec<Term>,
}

#[must_use]
pub fn collect(translator: &Translator<'_>) -> Items {
    let mut items = Items {
        adts: Vec::new(),
        traits: Vec::new(),
        impls: Vec::new(),
    };

    let mut ids: Vec<LocalDefId> = translator.tcx.hir_crate_items(()).definitions().collect();
    ids.sort_by_key(|id| id.local_def_index.as_u32());

    for local in ids {
        let def_id = local.to_def_id();
        match translator.tcx.def_kind(local) {
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                items.adts.push(translator.adt_def(def_id))
            }
            DefKind::Trait => items.traits.push(translator.trait_def(def_id)),
            DefKind::Impl { of_trait: true } => items.impls.push(translator.impl_def(def_id)),
            _ => {}
        }
    }

    let _ = translator.take_regions();
    items
}

#[must_use]
pub fn external_adts(translator: &Translator<'_>) -> Vec<Term> {
    let mut done: Vec<DefId> = Vec::new();
    let mut adts = Vec::new();
    loop {
        let pending: Vec<DefId> = translator.with_adts_seen(|seen| {
            seen.iter()
                .copied()
                .filter(|id| !id.is_local() && !done.contains(id))
                .collect()
        });
        if pending.is_empty() {
            break;
        }
        for def_id in pending {
            done.push(def_id);
            adts.push(translator.adt_def(def_id));
        }
    }
    let _ = translator.take_regions();
    adts
}

impl<'tcx> Translator<'tcx> {
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
            .map(|(index, v)| {
                let discriminant = if adt.is_enum() {
                    adt.discriminant_for_variant(self.tcx, index).val
                } else {
                    0
                };
                let fields: Vec<Term> = v
                    .fields
                    .iter()
                    .map(|f| {
                        let t = self.tcx.type_of(f.did).skip_binder();
                        term::pair(term::string(f.name.as_str()), self.ty(t))
                    })
                    .collect();
                term::app(
                    "VariantDef",
                    vec![
                        term::string(v.name.as_str()),
                        term::nat(u64::from(index.as_u32())),
                        term::bits(discriminant),
                        term::list(fields),
                    ],
                )
            })
            .collect();

        let repr = adt.repr();
        let mut reprs = Vec::new();
        if repr.c() {
            reprs.push(term::string("C"));
        }
        if repr.transparent() {
            reprs.push(term::string("transparent"));
        }
        if repr.packed() {
            reprs.push(term::string("packed"));
        }
        if let Some(int) = repr.int {
            reprs.push(term::string(&format!("{int:?}")));
        }

        term::note(
            &self.tcx.def_path_str(def_id),
            term::app(
                "AdtDef",
                vec![
                    term::note("path", self.path(def_id)),
                    term::note("kind", term::atom(kind)),
                    term::note("generics", self.generics(def_id)),
                    term::note("variants", term::list(variants)),
                    term::note("repr", term::list(reprs)),
                ],
            ),
        )
    }

    fn trait_def(&self, def_id: DefId) -> Term {
        term::note(
            &self.tcx.def_path_str(def_id),
            term::app(
                "TraitDef",
                vec![
                    term::note("path", self.path(def_id)),
                    term::note("generics", self.generics(def_id)),
                    term::note("bounds", self.bounds(def_id)),
                    term::note("items", term::list(self.associated_items(def_id))),
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
                let trait_item = item.trait_item_def_id()?;
                Some(term::pair(self.path(trait_item), self.path(item.def_id)))
            })
            .collect();

        term::note(
            &self.tcx.def_path_str(def_id),
            term::app(
                "ImplDef",
                vec![
                    term::note("path", self.path(def_id)),
                    term::note("trait", self.path(trait_ref.def_id)),
                    term::note("args", self.generic_args(trait_ref.args)),
                    term::note("generics", self.generics(def_id)),
                    term::note("bounds", self.bounds(def_id)),
                    term::note("items", term::list(mapped)),
                    term::note("negative", term::boolean(negative)),
                ],
            ),
        )
    }

    fn associated_items(&self, def_id: DefId) -> Vec<Term> {
        self.tcx
            .associated_items(def_id)
            .in_definition_order()
            .map(|item| {
                let kind = match item.kind {
                    ty::AssocKind::Fn { has_self, .. } => {
                        term::app("AiFn", vec![term::boolean(has_self)])
                    }
                    ty::AssocKind::Const { .. } => term::atom("AiConst"),
                    ty::AssocKind::Type { .. } => term::atom("AiType"),
                };
                term::app(
                    "AssocItem",
                    vec![
                        term::string(&item.opt_name().map_or_else(String::new, |n| n.to_string())),
                        self.path(item.def_id),
                        kind,
                        term::boolean(item.defaultness(self.tcx).has_value()),
                    ],
                )
            })
            .collect()
    }
}
