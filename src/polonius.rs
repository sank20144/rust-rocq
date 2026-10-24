use std::collections::{BTreeMap, BTreeSet};

use polonius_engine::{Algorithm, Output};
use rustc_borrowck::consumers::RichLocation;

use crate::store::Facts;
use crate::term::{self, Term};

type Id = u32;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Point {
    Start { block: Id, statement: usize },
    Mid { block: Id, statement: usize },
}

impl Point {
    fn from_rich(value: RichLocation) -> Self {
        match value {
            RichLocation::Start(location) => Self::Start {
                block: location.block.as_u32(),
                statement: location.statement_index,
            },
            RichLocation::Mid(location) => Self::Mid {
                block: location.block.as_u32(),
                statement: location.statement_index,
            },
        }
    }

    fn term(self) -> Term {
        match self {
            Self::Start { block, statement } => term::app(
                "PtStart",
                vec![term::nat(block as u64), term::nat(statement as u64)],
            ),
            Self::Mid { block, statement } => term::app(
                "PtMid",
                vec![term::nat(block as u64), term::nat(statement as u64)],
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

pub fn annotations(facts: &Facts<'_>) -> Term {
    let (Some(input), Some(table)) = (facts.input_facts.as_deref(), facts.location_table.as_ref())
    else {
        return empty_annotations();
    };

    let output = Output::compute(input, Algorithm::Naive, true);
    let point = |p| Point::from_rich(table.to_rich_location(p));

    let mut starts = BTreeSet::new();
    let mut issued = LiveAt::new();
    for &(origin, loan, at) in &input.loan_issued_at {
        let at = point(at);
        let loan = u32::from(loan);
        starts.insert((u32::from(origin), loan, at));
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
        .map(|&(loan, at)| (u32::from(loan), point(at)))
        .collect();

    let mut ordinary = LiveAt::new();
    for (at, loans) in &output.loan_live_at {
        ordinary
            .entry(point(*at))
            .or_default()
            .extend(loans.iter().copied().map(u32::from));
    }

    let mut origin_live = BTreeMap::<Point, IdSet>::new();
    for (at, origins) in &output.origin_live_on_entry {
        origin_live
            .entry(point(*at))
            .or_default()
            .extend(origins.iter().copied().map(u32::from));
    }

    let mut requires = RegionLoans::new();
    for (at, regions) in &output.origin_contains_loan_at {
        let at = point(*at);
        for (origin, loans) in regions {
            requires
                .entry(at)
                .or_default()
                .entry(u32::from(*origin))
                .or_default()
                .extend(loans.iter().copied().map(u32::from));
        }
    }

    let mut subsets = RegionSubsets::new();
    for (at, regions) in &output.subset {
        let at = point(*at);
        for (origin, targets) in regions {
            subsets
                .entry(at)
                .or_default()
                .entry(u32::from(*origin))
                .or_default()
                .extend(targets.iter().copied().map(u32::from));
        }
    }

    let zombies = zombie_loans(&requires, &killed, &edges, &origin_live, &subsets);
    let mut live = ordinary;
    add_live(&mut live, &zombies);
    add_live(&mut live, &issued);

    let ends = loan_ends(&live, &edges);

    let mut universal: Vec<_> = input
        .universal_region
        .iter()
        .copied()
        .map(u32::from)
        .collect();
    universal.sort_unstable();
    universal.dedup();
    let mut placeholders: Vec<_> = input
        .placeholder
        .iter()
        .map(|&(origin, loan)| (u32::from(origin), u32::from(loan)))
        .collect();
    placeholders.sort_unstable();
    placeholders.dedup();
    let mut known_subsets: Vec<_> = input
        .known_placeholder_subset
        .iter()
        .map(|&(from, to)| (u32::from(from), u32::from(to)))
        .collect();
    known_subsets.sort_unstable();
    known_subsets.dedup();

    term::app(
        "BorrowckAnnotations",
        vec![
            term::note(
                "universal regions",
                term::list(universal.into_iter().map(|n| term::nat(n as u64)).collect()),
            ),
            term::note(
                "placeholders",
                term::list(
                    placeholders
                        .into_iter()
                        .map(|(o, l)| term::pair(term::nat(o as u64), term::nat(l as u64)))
                        .collect(),
                ),
            ),
            term::note(
                "known placeholder subsets",
                term::list(
                    known_subsets
                        .into_iter()
                        .map(|(a, b)| term::pair(term::nat(a as u64), term::nat(b as u64)))
                        .collect(),
                ),
            ),
            term::note(
                "loan starts",
                term::list(
                    starts
                        .into_iter()
                        .map(|(origin, loan, at)| {
                            term::app(
                                "LoanStart",
                                vec![term::nat(origin as u64), term::nat(loan as u64), at.term()],
                            )
                        })
                        .collect(),
                ),
            ),
            term::note(
                "loan ends",
                term::list(
                    ends.into_iter()
                        .map(|(loan, from, to)| {
                            term::app(
                                "LoanEnd",
                                vec![
                                    term::nat(loan as u64),
                                    from.term(),
                                    term::option(to.map(Point::term)),
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
    term::app(
        "BorrowckAnnotations",
        vec![
            term::list(vec![]),
            term::list(vec![]),
            term::list(vec![]),
            term::list(vec![]),
            term::list(vec![]),
        ],
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(n: Id) -> Point {
        Point::Start {
            block: 0,
            statement: n as usize,
        }
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
