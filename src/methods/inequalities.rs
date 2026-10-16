//! Whether an `inequalities` step holds (`METHODS.md`, inequalities): its
//! claim follows by linear arithmetic over an ordered field from what the
//! lines it cites say, each part of them, and the bounds a membership among
//! them implies. The arithmetic is `linear`'s; the proof the build writes of
//! what is decided here is `crate::elab::calculators`.

use std::collections::BTreeSet;

use crate::mm::kernel::{FloatLabels, Term};

use super::algebra::parts;
use super::linear::{self, How};

/// Whether a plain `inequalities` step's claim follows from `cited`, the
/// lines the step cites, each read with its parts (`algebra::parts`), and
/// `implied`, what a membership among them implies, of which a disequality
/// says nothing to an order (`METHODS.md`, inequalities, What a step does):
/// by a combination that adds the facts as they stand, each once, and the
/// claim's sides the sums of theirs. A disequality taken both ways adds no
/// side. None where the claim is no relation `linear` reads.
pub fn decide(
    claimed: &Term,
    cited: &[Term],
    implied: &[Term],
    labels: &FloatLabels,
) -> Option<bool> {
    // A claim of two facts or more, `0 ≤ e and e ≤ 9`, holds where each
    // does, as the build proves each and joins them.
    let claims: Vec<(Term, linear::Fact)> = parts(claimed)
        .into_iter()
        .filter(|part| !conjoined(part))
        .map(|part| linear::fact(&part, labels).map(|f| (part, f)))
        .collect::<Option<_>>()?;
    // Each fact with the term it was read from.
    let mut given = Vec::new();
    let mut said_as = Vec::new();
    for held in cited {
        for said in parts(held) {
            if let Some(fact) = linear::fact(&said, labels) {
                given.push(fact);
                said_as.push(said);
            }
        }
    }
    let cited_count = given.len();
    // A membership's bounds are offered as facts, but a disequality among
    // them, `k ≠ 0` from `k ∈ ℕ`, only as a disequality the step may claim.
    let mut apart = Vec::new();
    for said in implied {
        match linear::fact(said, labels) {
            Some(fact) if fact.how == How::Ne => apart.push(fact),
            Some(fact) => {
                given.push(fact);
                said_as.push(said.clone());
            }
            None => {}
        }
    }
    let read = Given {
        facts: &given,
        said_as: &said_as,
        cited: cited_count,
        apart: &apart,
    };
    Some(
        claims
            .iter()
            .all(|(part, claim)| added(part, claim, &read, labels)),
    )
}

/// What a plain step adds: the facts, the term each is read from, how many
/// of them, first, the lines the step cites give, and the disequalities a
/// membership among them implies.
struct Given<'a> {
    facts: &'a [linear::Fact],
    said_as: &'a [Term],
    cited: usize,
    apart: &'a [linear::Fact],
}

/// Whether one claim follows from what is given by adding it as it stands
/// (`decide`). Where it adds no cited line, the claim rests on the facts a
/// step takes unwritten alone, `m < m + 1` or `a ≤ a`, and is one step.
fn added(
    part: &Term,
    claim: &linear::Fact,
    given: &Given,
    labels: &FloatLabels,
) -> bool {
    // A disequality is reached by adding nothing: from an order it is a
    // `weakening` row, so a step claims one only as a cited line or a
    // membership's bound says it.
    if claim.how == How::Ne {
        let restates = |f: &linear::Fact| {
            f.how == How::Ne
                && (f.side.minus(&claim.side).is_zero()
                    || f.side.plus(&claim.side).is_zero())
        };
        return given.facts.iter().chain(given.apart).any(restates);
    }
    let facts = given.facts;
    let mut all = facts.to_vec();
    all.push(linear::opposite(claim));
    let lines = vec![None; all.len()];
    let Some(used) = linear::used_facts(&all, &lines, true) else {
        return false;
    };
    if !used.iter().any(|&i| i < given.cited) {
        return true;
    }
    // Lines added as they stand make a sum as strict as the strictest of
    // them: `a < b` gives `a < b`, and `a ≤ b` from it is a `weakening` row.
    let strict = used
        .iter()
        .any(|&i| i < given.cited && facts[i].how == How::Lt);
    if claim.how == How::Le && strict {
        return false;
    }
    // An equation is added from equations: from two orders it is
    // `antisymmetry`.
    let ordered = used
        .iter()
        .any(|&i| i < given.cited && matches!(facts[i].how, How::Le | How::Lt));
    if claim.how == How::Eq && ordered {
        return false;
    }
    let Some(claim_sides) = linear::sides(part, labels) else {
        return false;
    };
    let added: Vec<linear::Sides> = used
        .iter()
        .filter(|&&i| i < facts.len() && facts[i].how != How::Ne)
        .filter_map(|&i| linear::sides(&given.said_as[i], labels))
        .collect();
    linear::sums_sides(&claim_sides, &added)
}

/// The cited facts a claim that follows combines (`METHODS.md`,
/// inequalities: an atom is one of the claim or of the facts the step
/// combines). Each of `cited` is a fact of a line the step cites, and
/// `line_of` the line it is of; for each part of the claim the combination
/// is `linear::certificate`'s, which rests on the most lines, as the build
/// takes it. Each cited fact it uses (`linear::used_facts`) is given by its
/// index in `cited`. None where the claim does not follow, or is no relation
/// `linear` reads.
pub fn combined(
    claimed: &Term,
    cited: &[Term],
    line_of: &[usize],
    implied: &[Term],
    labels: &FloatLabels,
) -> Option<BTreeSet<usize>> {
    let claims: Vec<_> = parts(claimed)
        .iter()
        .filter(|part| !conjoined(part))
        .map(|part| linear::fact(part, labels))
        .collect::<Option<_>>()?;
    let mut given = Vec::new();
    // For each fact, the cited fact it is of and the page's line.
    let mut of_cited: Vec<Option<usize>> = Vec::new();
    let mut lines: Vec<Option<usize>> = Vec::new();
    for (i, held) in cited.iter().enumerate() {
        for said in parts(held) {
            if let Some(fact) = linear::fact(&said, labels) {
                given.push(fact);
                of_cited.push(Some(i));
                lines.push(line_of.get(i).copied());
            }
        }
    }
    for said in implied {
        if let Some(fact) = linear::fact(said, labels).filter(|f| f.how != How::Ne) {
            given.push(fact);
            of_cited.push(None);
            lines.push(None);
        }
    }
    let mut out = BTreeSet::new();
    for claim in &claims {
        let mut all = given.clone();
        all.push(linear::opposite(claim));
        let mut all_lines = lines.clone();
        all_lines.push(None);
        let used = linear::used_facts(&all, &all_lines, true)?;
        out.extend(
            used.iter()
                .filter_map(|j| of_cited.get(*j).copied().flatten()),
        );
    }
    Some(out)
}

/// Whether a term is a conjunction, which `algebra::parts` takes apart
/// (`rules::SPLIT`).
fn conjoined(term: &Term) -> bool {
    term.label()
        .is_some_and(|l| crate::rules::lookup(crate::rules::SPLIT, l).is_some())
}

/// What a step whose claim `shown` does not follow is told, the step by its
/// number.
pub fn refusal(shown: &str, number: &str) -> String {
    format!("{shown} does not follow from what step {number} cites")
}
