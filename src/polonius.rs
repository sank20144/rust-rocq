use std::collections::{BTreeMap, BTreeSet};

use polonius_engine::{Algorithm, Output};
use rustc_borrowck::consumers::RichLocation;

use crate::rocq::{self, Term};
use crate::store::Facts;

type Id = u32;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Point {
    Start(Id, usize),
    Mid(Id, usize),
}

impl Point {
    fn from_rich(value: RichLocation) -> Self {
        match value {
            RichLocation::Start(location) => {
                Self::Start(location.block.as_u32(), location.statement_index)
            }
            RichLocation::Mid(location) => {
                Self::Mid(location.block.as_u32(), location.statement_index)
            }
        }
    }

    fn term(self) -> Term {
        match self {
            Self::Start(block, statement) => rocq::app(
                "PtStart",
                vec![rocq::nat(block as u64), rocq::nat(statement as u64)],
            ),
            Self::Mid(block, statement) => rocq::app(
                "PtMid",
                vec![rocq::nat(block as u64), rocq::nat(statement as u64)],
            ),
        }
    }
}

type PointSet = BTreeSet<Point>;
type IdSet = BTreeSet<Id>;
type LiveAt = BTreeMap<Point, IdSet>;
type RegionLoans = BTreeMap<Point, BTreeMap<Id, IdSet>>;
type RegionSubsets = BTreeMap<Point, BTreeMap<Id, IdSet>>;

fn zombie_loans(
    requires: &RegionLoans,
    killed: &BTreeSet<(Id, Point)>,
    edges: &BTreeSet<(Point, Point)>,
    origin_live: &BTreeMap<Point, IdSet>,
    subsets: &RegionSubsets,
) -> LiveAt {
    let mut zombie_requires = BTreeSet::<(Id, Id, Point)>::new();

    for &(loan, point) in killed {
        let Some(regions) = requires.get(&point) else {
            continue;
        };
        for (&region, loans) in regions {
            if !loans.contains(&loan) {
                continue;
            }
            for &(_, target) in edges.iter().filter(|(source, _)| *source == point) {
                if origin_live
                    .get(&target)
                    .is_some_and(|live| live.contains(&region))
                {
                    zombie_requires.insert((region, loan, target));
                }
            }
        }
    }

    loop {
        let mut changed = false;
        let current: Vec<_> = zombie_requires.iter().copied().collect();
        for (region, loan, point) in current {
            if let Some(targets) = subsets.get(&point).and_then(|at| at.get(&region)) {
                for &target_region in targets {
                    changed |= zombie_requires.insert((target_region, loan, point));
                }
            }
            for &(_, target) in edges.iter().filter(|(source, _)| *source == point) {
                if origin_live
                    .get(&target)
                    .is_some_and(|live| live.contains(&region))
                {
                    changed |= zombie_requires.insert((region, loan, target));
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut result = LiveAt::new();
    for (region, loan, point) in zombie_requires {
        if origin_live
            .get(&point)
            .is_some_and(|live| live.contains(&region))
        {
            result.entry(point).or_default().insert(loan);
        }
    }
    result
}

fn add_live(into: &mut LiveAt, from: &LiveAt) {
    for (&point, loans) in from {
        into.entry(point).or_default().extend(loans);
    }
}

fn loan_ends(
    live: &LiveAt,
    edges: &BTreeSet<(Point, Point)>,
) -> BTreeSet<(Id, Point, Option<Point>)> {
    let mut ends = BTreeSet::new();
    for &(from, to) in edges {
        let from_live = live.get(&from).cloned().unwrap_or_default();
        let to_live = live.get(&to).cloned().unwrap_or_default();
        for loan in from_live.difference(&to_live) {
            ends.insert((*loan, from, Some(to)));
        }
    }

    let outgoing: PointSet = edges.iter().map(|(from, _)| *from).collect();
    for (&at, loans) in live {
        if !outgoing.contains(&at) {
            for &loan in loans {
                ends.insert((loan, at, None));
            }
        }
    }
    ends
}

fn id(value: impl Into<u32>) -> Id {
    value.into()
}

pub fn annotations(f: &Facts<'_>) -> Term {
    let (Some(input), Some(table)) = (f.input_facts.as_deref(), f.location_table.as_ref()) else {
        return empty_annotations();
    };

    let output = Output::compute(input, Algorithm::Naive, true);
    let point = |p| Point::from_rich(table.to_rich_location(p));

    let mut starts = BTreeSet::new();
    let mut issued = LiveAt::new();
    for &(origin, loan, at) in &input.loan_issued_at {
        let at = point(at);
        let loan = id(loan);
        starts.insert((id(origin), loan, at));
        issued.entry(at).or_default().insert(loan);
    }

    let edges: BTreeSet<_> = input
        .cfg_edge
        .iter()
        .map(|&(from, to)| (point(from), point(to)))
        .collect();
    let killed: BTreeSet<_> = input
        .loan_killed_at
        .iter()
        .map(|&(loan, at)| (id(loan), point(at)))
        .collect();

    let mut ordinary = LiveAt::new();
    for (at, loans) in &output.loan_live_at {
        ordinary
            .entry(point(*at))
            .or_default()
            .extend(loans.iter().copied().map(id));
    }

    let mut origin_live = BTreeMap::<Point, IdSet>::new();
    for (at, origins) in &output.origin_live_on_entry {
        origin_live
            .entry(point(*at))
            .or_default()
            .extend(origins.iter().copied().map(id));
    }

    let mut requires = RegionLoans::new();
    for (at, regions) in &output.origin_contains_loan_at {
        let at = point(*at);
        for (origin, loans) in regions {
            requires
                .entry(at)
                .or_default()
                .entry(id(*origin))
                .or_default()
                .extend(loans.iter().copied().map(id));
        }
    }

    let mut subsets = RegionSubsets::new();
    for (at, regions) in &output.subset {
        let at = point(*at);
        for (origin, targets) in regions {
            subsets
                .entry(at)
                .or_default()
                .entry(id(*origin))
                .or_default()
                .extend(targets.iter().copied().map(id));
        }
    }

    let zombies = zombie_loans(&requires, &killed, &edges, &origin_live, &subsets);
    let mut live = ordinary;
    add_live(&mut live, &zombies);
    add_live(&mut live, &issued);

    let ends = loan_ends(&live, &edges);

    let mut universal: Vec<_> = input.universal_region.iter().copied().map(id).collect();
    universal.sort_unstable();
    universal.dedup();
    let mut placeholders: Vec<_> = input
        .placeholder
        .iter()
        .map(|&(origin, loan)| (id(origin), id(loan)))
        .collect();
    placeholders.sort_unstable();
    placeholders.dedup();
    let mut known_subsets: Vec<_> = input
        .known_placeholder_subset
        .iter()
        .map(|&(from, to)| (id(from), id(to)))
        .collect();
    known_subsets.sort_unstable();
    known_subsets.dedup();

    rocq::app(
        "BorrowckAnnotations",
        vec![
            rocq::note(
                "universal regions",
                rocq::list(universal.into_iter().map(|n| rocq::nat(n as u64)).collect()),
            ),
            rocq::note(
                "placeholders",
                rocq::list(
                    placeholders
                        .into_iter()
                        .map(|(o, l)| rocq::pair(rocq::nat(o as u64), rocq::nat(l as u64)))
                        .collect(),
                ),
            ),
            rocq::note(
                "known placeholder subsets",
                rocq::list(
                    known_subsets
                        .into_iter()
                        .map(|(a, b)| rocq::pair(rocq::nat(a as u64), rocq::nat(b as u64)))
                        .collect(),
                ),
            ),
            rocq::note(
                "loan starts",
                rocq::list(
                    starts
                        .into_iter()
                        .map(|(origin, loan, at)| {
                            rocq::app(
                                "LoanStart",
                                vec![rocq::nat(origin as u64), rocq::nat(loan as u64), at.term()],
                            )
                        })
                        .collect(),
                ),
            ),
            rocq::note(
                "loan ends",
                rocq::list(
                    ends.into_iter()
                        .map(|(loan, from, to)| {
                            rocq::app(
                                "LoanEnd",
                                vec![
                                    rocq::nat(loan as u64),
                                    from.term(),
                                    rocq::option(to.map(Point::term)),
                                ],
                            )
                        })
                        .collect(),
                ),
            ),
        ],
    )
}

pub fn empty_annotations() -> Term {
    rocq::app(
        "BorrowckAnnotations",
        vec![
            rocq::list(vec![]),
            rocq::list(vec![]),
            rocq::list(vec![]),
            rocq::list(vec![]),
            rocq::list(vec![]),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(n: Id) -> Point {
        Point::Start(0, n as usize)
    }

    #[test]
    fn killed_loan_stays_live_while_containing_origin_is_live() {
        let mut requires = RegionLoans::new();
        requires
            .entry(p(0))
            .or_default()
            .entry(1)
            .or_default()
            .insert(7);
        let killed = BTreeSet::from([(7, p(0))]);
        let edges = BTreeSet::from([(p(0), p(1)), (p(1), p(2))]);
        let origin_live =
            BTreeMap::from([(p(1), BTreeSet::from([1])), (p(2), BTreeSet::from([1]))]);

        let live = zombie_loans(
            &requires,
            &killed,
            &edges,
            &origin_live,
            &RegionSubsets::new(),
        );
        assert_eq!(live.get(&p(1)), Some(&BTreeSet::from([7])));
        assert_eq!(live.get(&p(2)), Some(&BTreeSet::from([7])));
    }

    #[test]
    fn zombie_loan_propagates_through_region_subset() {
        let mut requires = RegionLoans::new();
        requires
            .entry(p(0))
            .or_default()
            .entry(1)
            .or_default()
            .insert(7);
        let killed = BTreeSet::from([(7, p(0))]);
        let edges = BTreeSet::from([(p(0), p(1)), (p(1), p(2))]);
        let origin_live =
            BTreeMap::from([(p(1), BTreeSet::from([1, 2])), (p(2), BTreeSet::from([2]))]);
        let subsets = BTreeMap::from([(p(1), BTreeMap::from([(1, BTreeSet::from([2]))]))]);

        let live = zombie_loans(&requires, &killed, &edges, &origin_live, &subsets);
        assert_eq!(live.get(&p(2)), Some(&BTreeSet::from([7])));
    }

    #[test]
    fn loan_ending_is_specific_to_the_edge_where_it_dies() {
        let live = BTreeMap::from([(p(0), BTreeSet::from([7])), (p(1), BTreeSet::from([7]))]);
        let edges = BTreeSet::from([(p(0), p(1)), (p(0), p(2))]);

        let ends = loan_ends(&live, &edges);
        assert!(ends.contains(&(7, p(0), Some(p(2)))));
        assert!(!ends.contains(&(7, p(0), Some(p(1)))));
        assert!(ends.contains(&(7, p(1), None)));
    }
}
