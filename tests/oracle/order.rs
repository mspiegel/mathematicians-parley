//! Claims for `inequalities`, drawn around a point (`METHODS.md`,
//! inequalities: the claim follows when its denial and the cited facts have
//! no solution over an ordered field).
//!
//! The letters are given whole values, a point p, and each cited fact is a
//! linear fact true at p. A claim made true is a sum of the cited facts,
//! each by a positive number (an equation by a number of either sign), less
//! a number 0 or more: Farkas's combination, which is the method's own
//! certificate, so it follows. A claim made false fails at p, where every
//! cited fact holds, so nothing it cites gives it. No solver is needed for
//! either.
//!
//! Each cited fact has a letter of its own, which no other cited fact
//! holds and which the claim holds, so a claim made true uses every line it
//! cites: none could be left out and the claim still follow.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};

use parley::formula::grammar::Grammar;

use crate::algebra::{at, constant, small, sum, times, written_out, Poly, LETTERS};
use crate::gen::{made, term, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

/// A relation of a linear form to 0: `form how 0`.
#[derive(Clone, Copy, Debug, PartialEq)]
enum How {
    Le,
    Lt,
    Eq,
    Ne,
}

/// What a cited group of lines says: a fact, or for `Split` the same form
/// said at most 0 and not 0, which together are below 0 by the split the
/// method makes of a disequality.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    Le,
    Lt,
    Eq,
    Split,
}

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// A small positive number: 1, 2, 3, or a half.
fn positive(r: &mut Random) -> BigRational {
    match r.below(4) {
        0 => ratio(1, 2),
        k => BigRational::from_integer(BigInt::from(k)),
    }
}

fn letter(x: &'static str, c: BigRational) -> Poly {
    BTreeMap::from([(vec![(x, 1)], c)])
}

/// A linear form with a nonzero coefficient of `own` and any of `shared`,
/// and a constant.
fn form(r: &mut Random, own: &'static str, shared: &[&'static str]) -> Poly {
    let mut out = letter(own, BigRational::from_integer(small(r, true)));
    for x in shared {
        if r.below(2) == 0 {
            out = sum(
                &out,
                &letter(x, BigRational::from_integer(small(r, true))),
                1,
            );
        }
    }
    sum(
        &out,
        &constant(BigRational::from_integer(small(r, true))),
        1,
    )
}

/// A linear form in one of the letters and any of the others. A claim
/// written with it holds a letter, as `inequalities`' claims do: one of
/// numerals alone is `arithmetic`'s.
fn any_form(r: &mut Random) -> Poly {
    let first = LETTERS[r.below(3) as usize];
    let mut out = sum(
        &constant(BigRational::from_integer(small(r, true))),
        &letter(first, BigRational::from_integer(small(r, true))),
        1,
    );
    for x in LETTERS {
        if x != first && r.below(2) == 0 {
            out = sum(
                &out,
                &letter(x, BigRational::from_integer(small(r, true))),
                1,
            );
        }
    }
    out
}

/// `form how 0` written as the page writes a relation: its terms split
/// between two sides, each side holding `common` as well, so that letters
/// stand on both; the relation turned round or denied at random.
fn written(
    r: &mut Random,
    g: &Grammar,
    form: &Poly,
    how: How,
    common: &Poly,
) -> String {
    let (mut left, mut right) = (common.clone(), common.clone());
    for (m, c) in form {
        let one = BTreeMap::from([(m.clone(), c.clone())]);
        if r.below(2) == 0 {
            left = sum(&left, &one, 1);
        } else {
            right = sum(&right, &one, -1);
        }
    }
    let (l, rt) = (term(g, &written_out(&left)), term(g, &written_out(&right)));
    let node = match (how, r.below(3)) {
        (How::Le, 0) => made(g, "_ ≤ _", vec![l, rt]),
        (How::Le, 1) => made(g, "_ ≥ _", vec![rt, l]),
        (How::Le, _) => made(g, "not _", vec![made(g, "_ < _", vec![rt, l])]),
        (How::Lt, 0) => made(g, "_ < _", vec![l, rt]),
        (How::Lt, 1) => made(g, "_ > _", vec![rt, l]),
        (How::Lt, _) => made(g, "not _", vec![made(g, "_ ≤ _", vec![rt, l])]),
        (How::Eq, 0) => made(g, "_ = _", vec![rt, l]),
        (How::Eq, _) => made(g, "_ = _", vec![l, rt]),
        (How::Ne, 0) => made(g, "_ ≠ _", vec![rt, l]),
        (How::Ne, _) => made(g, "_ ≠ _", vec![l, rt]),
    };
    g.print(&node)
}

/// Whether `how` holds of a value.
fn holds(how: How, v: &BigRational) -> bool {
    match how {
        How::Le => !v.is_positive(),
        How::Lt => v.is_negative(),
        How::Eq => v.is_zero(),
        How::Ne => !v.is_zero(),
    }
}

/// A claim for `inequalities`, drawn around a point and judged there.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let point: BTreeMap<&'static str, BigInt> = LETTERS
        .iter()
        .map(|x| (*x, BigInt::from(r.below(7)) - 3))
        .collect();
    let groups = r.below(4) as usize;
    let shared = &LETTERS[groups..];
    let mut kinds: Vec<Kind> = (0..groups)
        .map(|_| [Kind::Le, Kind::Lt, Kind::Eq, Kind::Split][r.below(4) as usize])
        .collect();
    // A disequality cited is what makes the claim strict, and nothing else
    // does: one that was not needed would be a line the step cites and
    // uses nothing of.
    let split = kinds.iter().position(|k| *k == Kind::Split);
    if let Some(at_split) = split {
        for (i, kind) in kinds.iter_mut().enumerate() {
            if i != at_split && (*kind == Kind::Split || *kind == Kind::Lt) {
                *kind = Kind::Le;
            }
        }
    }
    let mut drawn: Vec<(Kind, Poly)> = Vec::new();
    for (own, kind) in LETTERS[..groups].iter().zip(kinds) {
        let e = form(r, own, shared);
        let value = at(&e, &point);
        // The bound each fact sets on e, so that p meets it: at or above its
        // value, strictly above it where the fact is strict or denies.
        let bound = match kind {
            Kind::Eq => value,
            Kind::Le if r.below(2) == 0 => value,
            Kind::Le => value + positive(r),
            Kind::Lt | Kind::Split => value + positive(r),
        };
        drawn.push((kind, sum(&e, &constant(bound), -1)));
    }
    // The combination: each fact by a positive weight, an equation by one of
    // either sign, less a slack of 0 or more.
    let mut combined = Poly::new();
    for (kind, f) in &drawn {
        let mut weight = positive(r);
        if *kind == Kind::Eq && r.below(2) == 0 {
            weight = -weight;
        }
        combined = sum(&combined, &times(&constant(weight), f), 1);
    }
    let slack = if split.is_some() || r.below(2) == 0 {
        BigRational::zero()
    } else {
        positive(r)
    };
    combined = sum(&combined, &constant(slack.clone()), -1);
    let strict_by = |kind: Kind| kind == Kind::Lt || kind == Kind::Split;
    let strict = slack.is_positive() || drawn.iter().any(|(k, _)| strict_by(*k));
    let all_equations = drawn.iter().all(|(k, _)| *k == Kind::Eq);
    // What the combination gives: below 0 where something in it is strict,
    // 0 where it is all equations, at most 0 otherwise. Where a disequality
    // makes it strict, the claim is strict too.
    let wanted = if split.is_some() {
        [How::Lt, How::Ne][r.below(2) as usize]
    } else if strict {
        [How::Lt, How::Le, How::Ne][r.below(3) as usize]
    } else if all_equations {
        [How::Eq, How::Le][r.below(2) as usize]
    } else {
        How::Le
    };
    let true_claim = r.below(2) == 0;
    let (claim, how) = if true_claim {
        (combined, wanted)
    } else {
        // Moved by a constant to fail at p.
        let value = at(&combined, &point);
        let shift = match wanted {
            How::Le => -value + positive(r),
            How::Lt if r.below(2) == 0 => -value,
            How::Lt => -value + positive(r),
            How::Eq => -value + positive(r),
            How::Ne => -value,
        };
        (sum(&combined, &constant(shift), 1), wanted)
    };
    debug_assert_eq!(holds(how, &at(&claim, &point)), true_claim);

    let others_equations = drawn
        .iter()
        .all(|(k, _)| *k == Kind::Eq || *k == Kind::Split);
    let mut header: Vec<String> =
        LETTERS.iter().map(|x| format!("let {x} ∈ ℝ")).collect();
    let mut labels = Vec::new();
    let mut cite = |line: String, header: &mut Vec<String>| {
        header.push(format!("assume {line}"));
        labels.push(format!("H{}", header.len()));
    };
    for (kind, f) in &drawn {
        let common = any_form(r);
        match kind {
            Kind::Le => cite(written(r, g, f, How::Le, &common), &mut header),
            Kind::Lt => cite(written(r, g, f, How::Lt, &common), &mut header),
            Kind::Eq => cite(written(r, g, f, How::Eq, &common), &mut header),
            // Where the claim is a `≠` and all else it combines is
            // equations, the claim denied makes the form 0, which the `≠`
            // denies alone, and the bound beside it is not needed.
            Kind::Split => {
                if !(wanted == How::Ne && others_equations) {
                    cite(written(r, g, f, How::Le, &common), &mut header);
                }
                cite(written(r, g, f, How::Ne, &common), &mut header);
            }
        }
    }
    let common = any_form(r);
    let said = written(r, g, &claim, how, &common);
    let justification = if labels.is_empty() {
        "inequalities".to_string()
    } else {
        format!("inequalities, from {}", labels.join(", "))
    };
    let shown = format!(
        "{claim:?} {how:?} 0 from {:?} at {point:?}",
        drawn
            .iter()
            .map(|(k, f)| format!("{f:?} {k:?}"))
            .collect::<Vec<_>>()
    );
    Drawn {
        header,
        written: said,
        justification,
        verdict: Verdict::Holds(true_claim),
        shown,
    }
}
