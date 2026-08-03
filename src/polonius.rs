use rustc_borrowck::consumers::RichLocation;

use crate::rocq::{self, Term};
use crate::store::Facts;

pub fn facts(f: &Facts<'_>) -> Term {
    let (Some(input), Some(table)) = (f.input_facts.as_deref(), f.location_table.as_ref()) else {
        return empty_facts();
    };

    let pt = |p| point(table.to_rich_location(p));

    rocq::app(
        "Facts",
        vec![
            rocq::list(input.universal_region.iter().map(|o| idx(*o)).collect()),
            pairs(&input.placeholder, |(o, l)| (idx(*o), idx(*l))),
            pairs(&input.known_placeholder_subset, |(a, b)| (idx(*a), idx(*b))),
            triples(&input.loan_issued_at, |(o, l, p)| (idx(*o), idx(*l), pt(*p))),
            pairs(&input.loan_killed_at, |(l, p)| (idx(*l), pt(*p))),
            pairs(&input.loan_invalidated_at, |(p, l)| (pt(*p), idx(*l))),
            triples(&input.subset_base, |(a, b, p)| (idx(*a), idx(*b), pt(*p))),
            pairs(&input.var_used_at, |(v, p)| (idx(*v), pt(*p))),
            pairs(&input.var_defined_at, |(v, p)| (idx(*v), pt(*p))),
            pairs(&input.var_dropped_at, |(v, p)| (idx(*v), pt(*p))),
            pairs(&input.use_of_var_derefs_origin, |(v, o)| (idx(*v), idx(*o))),
            pairs(&input.drop_of_var_derefs_origin, |(v, o)| (idx(*v), idx(*o))),
            pairs(&input.child_path, |(c, p)| (idx(*c), idx(*p))),
            pairs(&input.path_is_var, |(p, v)| (idx(*p), idx(*v))),
            pairs(&input.path_assigned_at_base, |(p, q)| (idx(*p), pt(*q))),
            pairs(&input.path_moved_at_base, |(p, q)| (idx(*p), pt(*q))),
            pairs(&input.path_accessed_at_base, |(p, q)| (idx(*p), pt(*q))),
        ],
    )
}

pub fn empty_facts() -> Term {
    rocq::app("Facts", (0..17).map(|_| rocq::list(vec![])).collect())
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
