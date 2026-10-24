use std::collections::HashMap;
use std::mem;
use std::sync::{LazyLock, Mutex};

use rustc_borrowck::consumers::{
    self, BodyWithBorrowckFacts, ConsumerOptions, PoloniusInput, PoloniusLocationTable,
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::queries::mir_borrowck::ProvidedValue;
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;

pub struct Facts<'tcx> {
    pub body: Body<'tcx>,
    pub promoted: IndexVec<Promoted, Body<'tcx>>,
    pub input_facts: Option<Box<PoloniusInput>>,
    pub location_table: Option<PoloniusLocationTable>,
}

static BODIES: LazyLock<Mutex<HashMap<LocalDefId, Facts<'static>>>> =
    LazyLock::new(|| Mutex::new(HashMap::new()));

pub fn mir_borrowck(tcx: TyCtxt<'_>, def_id: LocalDefId) -> ProvidedValue<'_> {
    let bodies =
        consumers::get_bodies_with_borrowck_facts(tcx, def_id, ConsumerOptions::PoloniusInputFacts);

    let bodies: FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>> =
        unsafe { mem::transmute(bodies) };

    let mut map = BODIES
        .lock()
        .expect("no code panics while holding the body store lock");
    for (def_id, facts) in bodies {
        map.insert(
            def_id,
            Facts {
                body: facts.body,
                promoted: facts.promoted,
                input_facts: facts.input_facts,
                location_table: facts.location_table,
            },
        );
    }
    drop(map);

    let mut providers = Providers::default();
    rustc_borrowck::provide(&mut providers.queries);
    (providers.queries.mir_borrowck)(tcx, def_id)
}

#[must_use]
pub fn collected() -> Vec<LocalDefId> {
    let map = BODIES
        .lock()
        .expect("no code panics while holding the body store lock");
    let mut ids: Vec<LocalDefId> = map.keys().copied().collect();
    ids.sort_by_key(|id| id.local_def_index.as_u32());
    ids
}

#[must_use]
pub fn retrieve<'tcx>(_tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Option<&'tcx Facts<'tcx>> {
    let map = BODIES
        .lock()
        .expect("no code panics while holding the body store lock");
    unsafe { mem::transmute(map.get(&def_id)) }
}
