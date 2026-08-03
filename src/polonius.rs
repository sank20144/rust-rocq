use rustc_borrowck::consumers::RichLocation;

use crate::rocq::{self, Term};
use crate::store::Facts;

const RELATIONS: [&str; 17] = [
    "universal_region",
    "placeholder",
    "known_placeholder_subset",
    "loan_issued_at",
    "loan_killed_at",
    "loan_invalidated_at",
    "subset_base",
    "var_used_at",
    "var_defined_at",
    "var_dropped_at",
    "use_of_var_derefs_origin",
    "drop_of_var_derefs_origin",
    "child_path",
    "path_is_var",
    "path_assigned_at_base",
    "path_moved_at_base",
    "path_accessed_at_base",
];

pub fn facts(f: &Facts<'_>) -> Term {
    let (Some(input), Some(table)) = (f.input_facts.as_deref(), f.location_table.as_ref()) else {
        return empty_facts();
    };

    let pt = |p| point(table.to_rich_location(p));

    rocq::app(
        "Facts",
        vec![
            rocq::note("universal_region", rocq::list(input.universal_region.iter().map(|o| idx(*o)).collect())),
            rocq::note("placeholder", pairs(&input.placeholder, |(o, l)| (idx(*o), idx(*l)))),
            rocq::note("known_placeholder_subset", pairs(&input.known_placeholder_subset, |(a, b)| (idx(*a), idx(*b)))),
            rocq::note("loan_issued_at", triples(&input.loan_issued_at, |(o, l, p)| (idx(*o), idx(*l), pt(*p)))),
            rocq::note("loan_killed_at", pairs(&input.loan_killed_at, |(l, p)| (idx(*l), pt(*p)))),
            rocq::note("loan_invalidated_at", pairs(&input.loan_invalidated_at, |(p, l)| (pt(*p), idx(*l)))),
            rocq::note("subset_base", triples(&input.subset_base, |(a, b, p)| (idx(*a), idx(*b), pt(*p)))),
            rocq::note("var_used_at", pairs(&input.var_used_at, |(v, p)| (idx(*v), pt(*p)))),
            rocq::note("var_defined_at", pairs(&input.var_defined_at, |(v, p)| (idx(*v), pt(*p)))),
            rocq::note("var_dropped_at", pairs(&input.var_dropped_at, |(v, p)| (idx(*v), pt(*p)))),
            rocq::note("use_of_var_derefs_origin", pairs(&input.use_of_var_derefs_origin, |(v, o)| (idx(*v), idx(*o)))),
            rocq::note("drop_of_var_derefs_origin", pairs(&input.drop_of_var_derefs_origin, |(v, o)| (idx(*v), idx(*o)))),
            rocq::note("child_path", pairs(&input.child_path, |(c, p)| (idx(*c), idx(*p)))),
            rocq::note("path_is_var", pairs(&input.path_is_var, |(p, v)| (idx(*p), idx(*v)))),
            rocq::note("path_assigned_at_base", pairs(&input.path_assigned_at_base, |(p, q)| (idx(*p), pt(*q)))),
            rocq::note("path_moved_at_base", pairs(&input.path_moved_at_base, |(p, q)| (idx(*p), pt(*q)))),
            rocq::note("path_accessed_at_base", pairs(&input.path_accessed_at_base, |(p, q)| (idx(*p), pt(*q)))),
        ],
    )
}

pub fn empty_facts() -> Term {
    rocq::app(
        "Facts",
        RELATIONS.iter().map(|r| rocq::note(*r, rocq::list(vec![]))).collect(),
    )
}

fn point(rich: RichLocation) -> Term {
    let (ctor, loc) = match rich {
        RichLocation::Start(l) => ("PtStart", l),
        RichLocation::Mid(l) => ("PtMid", l),
    };
    rocq::app(
        ctor,
        vec![
            rocq::nat(loc.block.as_u32() as u64),
            rocq::nat(loc.statement_index as u64),
        ],
    )
}

fn idx(i: impl Into<u32>) -> Term {
    rocq::nat(i.into() as u64)
}

fn pairs<T>(items: &[T], f: impl Fn(&T) -> (Term, Term)) -> Term {
    rocq::list(
        items
            .iter()
            .map(|t| {
                let (a, b) = f(t);
                rocq::pair(a, b)
            })
            .collect(),
    )
}

fn triples<T>(items: &[T], f: impl Fn(&T) -> (Term, Term, Term)) -> Term {
    rocq::list(
        items
            .iter()
            .map(|t| {
                let (a, b, c) = f(t);
                rocq::triple(a, b, c)
            })
            .collect(),
    )
}
