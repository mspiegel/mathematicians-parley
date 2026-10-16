//! Whether an `inequalities` step holds (`METHODS.md`, inequalities): its
//! claim follows by linear arithmetic over an ordered field from what the
//! lines it cites say, each part of them, and the bounds a membership among
//! them implies. The arithmetic is `linear`'s; the proof the build writes of
//! what is decided here is `crate::elab::calculators`.

use std::collections::BTreeSet;

use crate::mm::kernel::{FloatLabels, Term};

use super::algebra::parts;
use super::linear::{self, How};

/// Whether the claim follows from `cited`, the lines the step cites, each
/// read with its parts (`algebra::parts`), and `implied`, what a membership
/// among them implies, of which a disequality says nothing to an order.
/// None where the claim is no relation `linear` reads.
pub fn decide(
    claimed: &Term,
    cited: &[Term],
    implied: &[Term],
    labels: &FloatLabels,
) -> Option<bool> {
    // A claim of two facts or more, `0 ≤ e and e ≤ 9`, holds where each
    // does, as the build proves each and joins them.
    let claims: Vec<_> = parts(claimed)
        .iter()
        .filter(|part| !conjoined(part))
        .map(|part| linear::fact(part, labels))
        .collect::<Option<_>>()?;
    let mut given = Vec::new();
    for held in cited {
        given.extend(
            parts(held)
                .iter()
                .filter_map(|said| linear::fact(said, labels)),
        );
    }
    given.extend(
        implied
            .iter()
            .filter_map(|said| linear::fact(said, labels))
            .filter(|one| one.how != How::Ne),
    );
    Some(claims.iter().all(|claim| linear::follows(&given, claim)))
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
        let used = linear::used_facts(&all, &all_lines)?;
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
