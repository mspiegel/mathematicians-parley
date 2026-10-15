//! Whether an `inequalities` step holds (`METHODS.md`, inequalities): its
//! claim follows by linear arithmetic over an ordered field from what the
//! lines it cites say, each part of them, and the bounds a membership among
//! them implies. The arithmetic is `linear`'s; the proof the build writes of
//! what is decided here is `crate::elab::calculators`.

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
