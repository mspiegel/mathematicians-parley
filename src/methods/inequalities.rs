//! Whether an `inequalities` step holds (`METHODS.md`, inequalities): its
//! claim follows by linear arithmetic over an ordered field from what the
//! lines it cites say, each part of them, and the bounds a membership among
//! them implies. The arithmetic is `linear`'s; the proof the build writes of
//! what is decided here is `crate::elab::calculators`.

use std::collections::BTreeSet;

use crate::mm::kernel::{FloatLabels, Term};

use super::algebra::parts;
use super::field::q;
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
    let claims = claim_parts(claimed, labels)?;
    let read = Given::of(cited, implied, labels);
    Some(
        claims
            .iter()
            .all(|part| added(&part.term, &part.fact, &read, labels)),
    )
}

/// One fact a claim says.
struct ClaimPart {
    /// The term it is read from.
    term: Term,
    fact: linear::Fact,
}

/// Each fact a claim says; None where one is no relation `linear` reads.
fn claim_parts(claimed: &Term, labels: &FloatLabels) -> Option<Vec<ClaimPart>> {
    parts(claimed)
        .into_iter()
        .filter(|part| !conjoined(part))
        .map(|term| linear::fact(&term, labels).map(|fact| ClaimPart { term, fact }))
        .collect()
}

/// What a plain step adds: the facts, the term each is read from, how many
/// of them, first, the lines the step cites give, and the disequalities a
/// membership among them implies.
struct Given {
    facts: Vec<linear::Fact>,
    said_as: Vec<Term>,
    /// The cited line each fact is of, by its place among them; None for
    /// one a membership implies.
    term_of: Vec<Option<usize>>,
    cited: usize,
    apart: Vec<linear::Fact>,
}

impl Given {
    /// The facts of the lines `cited`, each part of them, and of `implied`,
    /// what a membership among them implies. A membership's bounds are
    /// offered as facts, but a disequality among them, `k ≠ 0` from
    /// `k ∈ ℕ`, only as a disequality the step may claim.
    fn of(cited: &[Term], implied: &[Term], labels: &FloatLabels) -> Given {
        let mut facts = Vec::new();
        let mut said_as = Vec::new();
        let mut term_of = Vec::new();
        for (i, held) in cited.iter().enumerate() {
            for said in parts(held) {
                if let Some(fact) = linear::fact(&said, labels) {
                    facts.push(fact);
                    said_as.push(said);
                    term_of.push(Some(i));
                }
            }
        }
        let cited = facts.len();
        let mut apart = Vec::new();
        for said in implied {
            match linear::fact(said, labels) {
                Some(fact) if fact.how == How::Ne => apart.push(fact),
                Some(fact) => {
                    facts.push(fact);
                    said_as.push(said.clone());
                    term_of.push(None);
                }
                None => {}
            }
        }
        Given {
            facts,
            said_as,
            term_of,
            cited,
            apart,
        }
    }
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
        return given.facts.iter().chain(&given.apart).any(restates);
    }
    accepted(part, claim, given, &given.term_of, labels).is_some()
}

/// The facts of `given` a claim that is no disequality adds, by their
/// place: the first combination of them that adds as they stand
/// (`linear::alike_combinations`, resting on the most of the lines
/// `lines` says each is of) whose sum is the claim (`sums_to`). Where
/// a disequality is among the facts, the one combination `linear::
/// used_facts` takes, which takes it both ways. None where no combination
/// is the claim.
fn accepted(
    part: &Term,
    claim: &linear::Fact,
    given: &Given,
    lines: &[Option<usize>],
    labels: &FloatLabels,
) -> Option<BTreeSet<usize>> {
    let mut all = given.facts.to_vec();
    all.push(linear::opposite(claim));
    let mut all_lines = lines.to_vec();
    all_lines.resize(all.len(), None);
    let combinations: Vec<BTreeSet<usize>> = if all.iter().any(|f| f.how == How::Ne) {
        linear::used_facts(&all, &all_lines, true)
            .into_iter()
            .collect()
    } else {
        linear::alike_combinations(&all, &all_lines)
            .found
            .into_iter()
            .map(|weights| weights.keys().copied().collect())
            .collect()
    };
    combinations
        .into_iter()
        .find(|used| sums_to(part, claim, given, used, labels))
}

/// Whether the facts of `given` at `used` add to the claim as they stand
/// (`accepted`): as strict as the claim says, equations from equations
/// alone, and the claim's sides the sums of theirs. Facts that add no cited
/// line are what a step takes unwritten, and the claim rests on them alone.
fn sums_to(
    part: &Term,
    claim: &linear::Fact,
    given: &Given,
    used: &BTreeSet<usize>,
    labels: &FloatLabels,
) -> bool {
    let facts = &given.facts;
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
    let claims = claim_parts(claimed, labels)?;
    let read = Given::of(cited, implied, labels);
    // The page's line each fact is of, which a combination rests on.
    let lines: Vec<Option<usize>> = read
        .term_of
        .iter()
        .map(|t| t.and_then(|i| line_of.get(i).copied()))
        .collect();
    let mut out = BTreeSet::new();
    for part in &claims {
        if part.fact.how == How::Ne {
            out.extend(restated_apart(&part.fact, cited, line_of, implied, labels)?);
            continue;
        }
        let used = accepted(&part.term, &part.fact, &read, &lines, labels)?;
        out.extend(
            used.iter()
                .filter_map(|&j| read.term_of.get(j).copied().flatten()),
        );
    }
    Some(out)
}

/// The cited facts a disequality claim combines, as `combined` gives them:
/// the combination `linear::used_facts` takes against its denial.
fn restated_apart(
    claim: &linear::Fact,
    cited: &[Term],
    line_of: &[usize],
    implied: &[Term],
    labels: &FloatLabels,
) -> Option<BTreeSet<usize>> {
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
    given.push(linear::opposite(claim));
    lines.push(None);
    let used = linear::used_facts(&given, &lines, true)?;
    Some(
        used.iter()
            .filter_map(|j| of_cited.get(*j).copied().flatten())
            .collect(),
    )
}

/// Whether a term is a conjunction, which `algebra::parts` takes apart
/// (`rules::SPLIT`).
fn conjoined(term: &Term) -> bool {
    term.label()
        .is_some_and(|l| crate::rules::lookup(crate::rules::SPLIT, l).is_some())
}

/// What a plain step `decide` refuses is told, its claim `shown` and the
/// step by its number. A claim that follows from the facts by linear
/// arithmetic, but not by adding them as they stand, is told the move it
/// takes is written as a row (`METHODS.md`, inequalities, Refusals): a
/// disequality from an order is a `weakening` row, and any other move a
/// row naming it, or a chain `transitivity`. Only one that does not follow
/// at all is told so.
pub fn refusal(
    shown: &str,
    number: &str,
    claimed: &Term,
    cited: &[Term],
    implied: &[Term],
    labels: &FloatLabels,
) -> String {
    let given = Given::of(cited, implied, labels);
    let claims = claim_parts(claimed, labels).unwrap_or_default();
    let follows = claims
        .iter()
        .all(|part| follows_linearly(&part.fact, &given));
    if claims.is_empty() || !follows {
        return format!("{shown} does not follow from what step {number} cites");
    }
    if claims.iter().any(|part| part.fact.how == How::Ne) {
        return format!(
            "{shown} follows from an order step {number} cites by a `weakening` row, and a plain inequalities step only adds its lines as they stand; write the line, then the claim with `weakening` as its reason"
        );
    }
    if claims
        .iter()
        .any(|part| !searched_whole(&part.fact, &given))
    {
        return format!(
            "{shown} may follow from what step {number} cites by adding its lines as they stand, but they give more facts than a plain inequalities step tries every way of adding; cite fewer lines, or add them in steps of their own"
        );
    }
    format!(
        "{shown} follows from what step {number} cites by a move other than adding its lines as they stand, which is all a plain inequalities step does; write the move as a row that names it, or a chain of lines as `transitivity`"
    )
}

/// Whether the search for the facts of `given` that add to `claim` as they
/// stand (`accepted`) reached its end, which one over too many facts does
/// not (`linear::Alike`).
fn searched_whole(claim: &linear::Fact, given: &Given) -> bool {
    let mut all = given.facts.clone();
    all.push(linear::opposite(claim));
    let mut lines = given.term_of.clone();
    lines.resize(all.len(), None);
    linear::alike_combinations(&all, &lines).whole
}

/// Whether `claim` follows from what is given by any combination linear
/// arithmetic finds, whatever multiplies each fact. A disequality follows
/// where either order between its sides does.
fn follows_linearly(claim: &linear::Fact, given: &Given) -> bool {
    if claim.how == How::Ne {
        let below = linear::Fact::new(claim.side.clone(), How::Lt);
        let above = linear::Fact::new(claim.side.scaled(&q(-1)), How::Lt);
        return follows_linearly(&below, given) || follows_linearly(&above, given);
    }
    let mut all = given.facts.clone();
    all.push(linear::opposite(claim));
    let lines = vec![None; all.len()];
    linear::used_facts(&all, &lines, false).is_some()
}
