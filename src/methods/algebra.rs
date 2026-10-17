//! Whether an `algebra` step holds (`METHODS.md`, algebra): its claim is an
//! identity of the field, or follows from the equations it cites added and
//! subtracted with at most one multiplied by a term; a disequality is one it
//! cites rescaled. The polynomials are `field`'s; the proof the build writes
//! of what is decided here is `crate::elab::calculators`.

use num_traits::Zero;

use crate::mm::kernel::{FloatLabels, Term};
use crate::rules::{self, lookup};

use super::field::{self, Op, Poly, DIV, Q};

/// What `decide` finds of an `algebra` step.
pub enum Verdict {
    /// The claim holds, combining the cited lines named here by their place
    /// among `cited`: what the step's hypotheses are asked of
    /// (`METHODS.md`, an atom is one of the facts the step combines).
    Holds { combined: Vec<usize> },
    /// The claim is neither an equation nor a disequality, which algebra
    /// decides.
    Undecided,
    /// A power the step reads is one algebra does not multiply out.
    PastExpanding(Term),
    /// The claim, an equation, is no identity and no combination of the
    /// equations cited.
    NoCombination,
    /// The claim, a disequality, rescales none the step cites.
    NoRescaling,
}

/// What a step whose claim `shown` the verdict refuses is told, the step
/// by its number, a term put in the page's words by `render`; None where
/// the claim holds.
pub fn refusal(
    verdict: &Verdict,
    shown: &str,
    number: &str,
    render: &dyn Fn(&Term) -> String,
) -> Option<String> {
    match verdict {
        Verdict::Holds { .. } | Verdict::Undecided => None,
        Verdict::PastExpanding(power) => Some(format!(
            "{} is a power algebra does not multiply out: writing it out costs more \
             than {}, each step the cube of its terms times the base's",
            render(power),
            field::WORK
        )),
        Verdict::NoCombination => Some(format!(
            "{shown} is not an identity, nor does it follow from what step {number} \
             cites, added and subtracted with at most one equation multiplied by a term"
        )),
        Verdict::NoRescaling => Some(format!(
            "{shown} is not a rescaling of any disequality step {number} cites"
        )),
    }
}

/// Whether the claim follows by `algebra` from the lines the step cites,
/// each as one term, its parts read as `parts` reads them.
pub fn decide(claimed: &Term, cited: &[Term], labels: &FloatLabels) -> Verdict {
    let mut read = vec![claimed.clone()];
    for held in cited {
        read.extend(parts(held));
    }
    for said in &read {
        if let Some(power) = field::past_expanding(said, labels) {
            return Verdict::PastExpanding(power);
        }
    }
    let Some(want) = field::equation(claimed, labels) else {
        return decide_apart(claimed, cited, labels);
    };
    let claims = readings(claimed, want, labels);
    let claim_under = denominators(claimed, labels);
    let mut given = Vec::new();
    let mut unders = Vec::new();
    // The cited line each equation given is a part of.
    let mut from = Vec::new();
    for (i, held) in cited.iter().enumerate() {
        for node in parts(held) {
            if let Some(one) = field::equation(&node, labels) {
                let read = claim_says(&node, one, labels);
                let under = field::exactly(&denominators(&node, labels), &read.taken);
                given.push(read.says);
                unders.push(under);
                from.push(i);
            }
        }
    }
    let found = claims
        .iter()
        .find_map(|c| combination(&given, &unders, c, &claim_under));
    match found {
        Some(taken) => {
            let mut combined: Vec<usize> =
                taken.iter().map(|t| from[t.which]).collect();
            combined.sort();
            combined.dedup();
            Verdict::Holds { combined }
        }
        None => Verdict::NoCombination,
    }
}

/// A disequality claim, which holds where it is one the step cites rescaled:
/// the method is allowed one disequality and no more. A claim that is no
/// disequality either is not decided here.
fn decide_apart(claimed: &Term, cited: &[Term], labels: &FloatLabels) -> Verdict {
    let Some(claim) = field::denied(claimed, labels) else {
        return Verdict::Undecided;
    };
    for (i, held) in cited.iter().enumerate() {
        for said in parts(held) {
            let one = field::denied(&said, labels);
            if one.is_some() && rescales(one.as_ref(), Some(&claim)).is_some() {
                return Verdict::Holds { combined: vec![i] };
            }
        }
    }
    Verdict::NoRescaling
}

/// A term and, where it is a conjunction, each of its parts in turn
/// (`rules::SPLIT`).
pub fn parts(term: &Term) -> Vec<Term> {
    let mut out = vec![term.clone()];
    if let Some(picks) = term.label().and_then(|l| lookup(rules::SPLIT, l)) {
        if picks.len() == term.children().len() {
            for child in term.children() {
                out.extend(parts(child));
            }
        }
    }
    out
}

/// What the cited polynomial is multiplied by to become the claim's: two
/// disequalities say one thing when one polynomial is the other scaled.
pub fn rescales(cited: Option<&Poly>, claim: Option<&Poly>) -> Option<Q> {
    let (cited, claim) = (cited?, claim?);
    if cited.terms.is_empty() || claim.terms.is_empty() {
        return None;
    }
    let lead = claim.lead()?;
    let theirs = cited.terms.get(lead)?;
    let times = &claim.terms[lead] / theirs;
    if times.is_zero() || *claim != cited.scaled(&times) {
        return None;
    }
    Some(times)
}

/// Each divisor a term writes, leftmost first and once for each time it
/// divides: what `field::read` reads the term's denominator as the product
/// of. It goes through what `read` multiplies out, sums, differences,
/// negations, products, quotients and powers it expands, and a divisor under
/// a power divides once for each the power multiplies; inside an atom is
/// not a denominator.
fn divisors_of(term: &Term, labels: &FloatLabels) -> Vec<Term> {
    let mut out = Vec::new();
    divisors_into(term, labels, &mut out);
    out
}

/// `divisors_of`, onto `out`.
fn divisors_into(term: &Term, labels: &FloatLabels, out: &mut Vec<Term>) {
    if term.variable().is_some() {
        return;
    }
    let kids = term.children();
    if term.label() == Some(field::NEG) && kids.len() == 1 {
        divisors_into(&kids[0], labels, out);
        return;
    }
    let Some(how) = Op::applied(term) else {
        return;
    };
    if matches!(how, Op::Add | Op::Sub | Op::Mul) {
        divisors_into(&kids[0], labels, out);
        divisors_into(&kids[1], labels, out);
    } else if how == Op::Div {
        divisors_into(&kids[0], labels, out);
        out.push(kids[1].clone());
    } else if how == Op::Exp {
        if let field::Power::Expanded { by, .. } =
            field::power_of(&kids[0], &kids[1], labels)
        {
            let mut under = Vec::new();
            divisors_into(&kids[0], labels, &mut under);
            for _ in 0..by {
                out.extend(under.iter().cloned());
            }
        }
    }
}

/// What a claim's sides are multiplied by for one divisor it writes, which
/// is what `field::read` takes the divisor as: the divisor itself; where it
/// is a quotient c/e, its numerator c; and where it is −(c/e), read as
/// (−c)/e, the negated numerator −c.
#[derive(Clone)]
pub enum Factor {
    Divisor(Term),
    Numerator {
        /// The divisor as written, c/e, which the page says is not 0.
        divisor: Term,
        top: Term,
        below: Term,
    },
    NegatedNumerator {
        /// The divisor as written, −(c/e), which the page says is not 0.
        divisor: Term,
        /// c/e.
        quotient: Term,
        top: Term,
        below: Term,
        /// −c, what the sides are multiplied by.
        negated: Term,
    },
}

impl Factor {
    pub fn term(&self) -> &Term {
        match self {
            Factor::Divisor(t) => t,
            Factor::Numerator { top, .. } => top,
            Factor::NegatedNumerator { negated, .. } => negated,
        }
    }
}

/// A quotient c/e with nothing dividing in either part.
struct QuotientParts {
    top: Term,
    below: Term,
}

/// `d`'s parts where it is a quotient c/e with nothing dividing in either;
/// None otherwise.
fn quotient_parts(d: &Term, labels: &FloatLabels) -> Option<QuotientParts> {
    let whole = |t: &Term| field::read(t, labels).under == field::one();
    let kids = d.children();
    let quotient = d.variable().is_none()
        && d.label() == Some("co")
        && kids.len() == 3
        && &*kids[2].rpn(labels) == DIV;
    (quotient && whole(&kids[0]) && whole(&kids[1])).then(|| QuotientParts {
        top: kids[0].clone(),
        below: kids[1].clone(),
    })
}

/// What a divisor of a claim's is read as: itself, where nothing in it
/// divides, its numerator c where it is c/e, or −c where it is −(c/e);
/// None for a divisor that divides deeper than that.
fn factor_of(d: Term, labels: &FloatLabels) -> Option<Factor> {
    if field::read(&d, labels).under == field::one() {
        return Some(Factor::Divisor(d));
    }
    if let Some(QuotientParts { top, below }) = quotient_parts(&d, labels) {
        return Some(Factor::Numerator {
            divisor: d,
            top,
            below,
        });
    }
    if d.variable().is_some() || d.label() != Some("cneg") {
        return None;
    }
    let quotient = d.children()[0].clone();
    let QuotientParts { top, below } = quotient_parts(&quotient, labels)?;
    let negated = Term::apply("cneg", vec![top.clone()]);
    Some(Factor::NegatedNumerator {
        divisor: d,
        quotient,
        top,
        below,
        negated,
    })
}

/// One reading of an equation for `algebra`, as the decision and the proof
/// both read it.
pub struct ClaimSays {
    /// The polynomial that must vanish: the equation's sides with their
    /// denominators multiplied across, some of the divisors it writes
    /// divided out of it.
    pub says: Poly,
    /// The divisors not divided out, which the proof multiplies a claim's
    /// sides by; None for one that divides deeper than a quotient
    /// (`factor_of`).
    pub kept: Vec<Option<Factor>>,
    /// What was divided out, the product of the divisors taken.
    pub taken: Poly,
}

/// Each reading of `want`, the equation as `field::equation` reads it,
/// with a product of the divisors it writes divided out where that divides
/// it exactly: the most divided out first, and the reading with none last.
/// Dividing both sides by a term is not a thing a step does besides what
/// it combines, so a claim follows when one reading of it is a combination
/// (`METHODS.md`, algebra); which one is read off the claim, and a cited
/// equation is read the first way, which says the least.
pub fn readings(claimed: &Term, want: Poly, labels: &FloatLabels) -> Vec<ClaimSays> {
    // The divisors, those alike in one group, each with how often it is
    // written.
    let mut groups: Vec<(Poly, Vec<Option<Factor>>)> = Vec::new();
    for d in claimed
        .children()
        .iter()
        .flat_map(|side| divisors_of(side, labels))
    {
        let factor = factor_of(d.clone(), labels);
        let by = match &factor {
            Some(f) => field::read(f.term(), labels).over,
            None => field::read(&d, labels).over,
        };
        match groups.iter_mut().find(|(p, _)| *p == by) {
            Some((_, all)) => all.push(factor),
            None => groups.push((by, vec![factor])),
        }
    }
    // Every choice of how many of each group to divide out, the most first.
    let mut choices: Vec<Vec<usize>> = vec![Vec::new()];
    for (_, all) in &groups {
        choices = choices
            .into_iter()
            .flat_map(|c| {
                (0..=all.len()).rev().map(move |n| {
                    let mut more = c.clone();
                    more.push(n);
                    more
                })
            })
            .collect();
    }
    choices.sort_by_key(|c| std::cmp::Reverse(c.iter().sum::<usize>()));
    let mut out = Vec::new();
    for choice in choices {
        let mut taken = field::one();
        let mut kept = Vec::new();
        for ((by, all), n) in groups.iter().zip(&choice) {
            for _ in 0..*n {
                taken = taken.times(by);
            }
            kept.extend(all[*n..].iter().cloned());
        }
        if taken.zero() {
            continue;
        }
        if let Some(says) = field::exactly(&want, &taken) {
            out.push(ClaimSays { says, kept, taken });
        }
    }
    out
}

/// The product of an equation's denominators, both sides': what its sides
/// are multiplied by to read it as a polynomial (`field::equation`).
pub fn denominators(node: &Term, labels: &FloatLabels) -> Poly {
    let sides: Vec<field::Quotient> = node
        .children()
        .iter()
        .map(|side| field::read(side, labels))
        .collect();
    sides[0].under.times(&sides[1].under)
}

/// How one reading of the claim is a combination of the cited equations
/// (`field::follows`), each cited equation read as `claim_says` reads it and
/// holding the denominators `unders` it was not divided by, None where what
/// was divided out does not divide them; `claim_under` is the claim's own
/// denominators. Dividing both sides by a term is not a
/// second thing a step does (`METHODS.md`, algebra), so the combination is
/// also asked with each equation read with its own divisors divided out
/// against the claim with its own: each is multiplied by the claim's
/// divisors left over its own, and the multipliers found are carried back.
/// A − (p/q − r/s) is (A + B − p/q) − (B − r/s), which as polynomials is s
/// times one and q times the other.
pub fn combination(
    given: &[Poly],
    unders: &[Option<Poly>],
    says: &ClaimSays,
    claim_under: &Poly,
) -> Option<Vec<field::Taken>> {
    if let Some(how) = field::follows(given, &says.says) {
        return Some(how);
    }
    let left = field::exactly(claim_under, &says.taken)?;
    let scales: Vec<Poly> = unders
        .iter()
        .map(|own| own.as_ref().and_then(|own| field::exactly(&left, own)))
        .collect::<Option<_>>()?;
    let scaled: Vec<Poly> =
        given.iter().zip(&scales).map(|(g, s)| g.times(s)).collect();
    let how = field::follows(&scaled, &says.says)?;
    Some(
        how.into_iter()
            .map(|t| field::Taken::of(t.which, t.multiplier().times(&scales[t.which])))
            .collect(),
    )
}

/// The reading of a cited equation: the most divided out (`readings`).
pub fn claim_says(claimed: &Term, want: Poly, labels: &FloatLabels) -> ClaimSays {
    readings(claimed, want, labels)
        .into_iter()
        .next()
        .expect("the reading with nothing divided out")
}
