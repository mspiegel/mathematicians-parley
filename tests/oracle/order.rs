//! Claims for a plain `inequalities` step, drawn around a point
//! (`METHODS.md`, inequalities, What a step does: a plain step adds the
//! lines it cites as they stand, each once, and claims their sums, the
//! smaller sides' sum against the larger sides').
//!
//! The letters are given whole values, a point p, and each cited line is a
//! linear relation true at p: all orders, or all equations, since an
//! equation adds to an equation and an order to an order. Each holds a
//! letter of its own, which no other line holds and the claim does, so a
//! claim uses every line it cites. From them one claim is drawn of four
//! kinds:
//!
//! - their sums, `<` where a line is strict and `≤` where none is, or `=`
//!   of equations, which the step takes;
//! - one line taken twice, or `≤` where a line is strict, or `≠` from
//!   orders, which follow and are not their sums: the step is told the move
//!   is a row (`refusal`);
//! - their sums moved by a constant so that the claim fails at p, which
//!   does not follow.
//!
//! No solver is needed: the claim is made true or false by construction.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

use parley::formula::grammar::Grammar;

use crate::algebra::{at, constant, small, sum, times, written_out, Poly, LETTERS};
use crate::gen::{made, term, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

/// What the tools say of a claim that follows only by a move a row names,
/// and of a disequality from an order.
const A_MOVE: &str = "by a move other than adding its lines as they stand";
const A_WEAKENING: &str = "by a `weakening` row";

/// The relation a line or the claim states, of its smaller side to its
/// larger.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Rel {
    Le,
    Lt,
    Eq,
    Ne,
}

/// One relation: its two sides, the smaller first.
#[derive(Clone, Debug)]
struct Relation {
    low: Poly,
    high: Poly,
    rel: Rel,
}

fn ratio(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn letter(x: &'static str, c: BigRational) -> Poly {
    BTreeMap::from([(vec![(x, 1)], c)])
}

/// A linear form with a nonzero coefficient of `own`, any of `shared`,
/// and a constant.
fn form(r: &mut Random, own: &'static str, shared: &[&'static str]) -> Poly {
    let start = letter(own, BigRational::from_integer(small(r, true)));
    let out = with_shared(r, start, shared);
    let c = constant(BigRational::from_integer(small(r, true)));
    sum(&out, &c, 1)
}

/// `start` with any of `shared`, each by a small coefficient.
fn with_shared(r: &mut Random, start: Poly, shared: &[&'static str]) -> Poly {
    let mut out = start;
    for x in shared {
        if r.below(2) == 0 {
            let term = letter(x, BigRational::from_integer(small(r, true)));
            out = sum(&out, &term, 1);
        }
    }
    out
}

/// A line true at p: a form of its own letter against one of the shared
/// letters alone, so that its own letter does not cancel and the line says
/// more than a fact of numerals; the other side moved by a constant so that
/// p meets the relation, strictly or not.
fn line(
    r: &mut Random,
    own: &'static str,
    shared: &[&'static str],
    rel: Rel,
    point: &BTreeMap<&'static str, BigInt>,
) -> Relation {
    let low = form(r, own, shared);
    let start = constant(BigRational::from_integer(small(r, true)));
    let high = with_shared(r, start, shared);
    let gap = match rel {
        Rel::Eq | Rel::Ne => ratio(0),
        Rel::Le => ratio(r.below(2) as i64),
        Rel::Lt => ratio(1 + r.below(3) as i64),
    };
    let moved = at(&low, point) + gap - at(&high, point);
    Relation {
        high: sum(&high, &constant(moved), 1),
        low,
        rel,
    }
}

/// The relation as the page writes it, turned round at random.
fn written(r: &mut Random, g: &Grammar, f: &Relation) -> String {
    let l = term(g, &written_out(&f.low));
    let h = term(g, &written_out(&f.high));
    let turned = r.below(2) == 0;
    let node = match (f.rel, turned) {
        (Rel::Le, false) => made(g, "_ ≤ _", vec![l, h]),
        (Rel::Le, true) => made(g, "_ ≥ _", vec![h, l]),
        (Rel::Lt, false) => made(g, "_ < _", vec![l, h]),
        (Rel::Lt, true) => made(g, "_ > _", vec![h, l]),
        (Rel::Eq, false) => made(g, "_ = _", vec![l, h]),
        (Rel::Eq, true) => made(g, "_ = _", vec![h, l]),
        (Rel::Ne, false) => made(g, "_ ≠ _", vec![l, h]),
        (Rel::Ne, true) => made(g, "_ ≠ _", vec![h, l]),
    };
    g.print(&node)
}

/// The lines added as they stand, each `by` times: the smaller sides'
/// sum against the larger sides'.
fn summed(lines: &[Relation], by: &[i64], rel: Rel) -> Relation {
    let (mut low, mut high) = (Poly::new(), Poly::new());
    for (f, k) in lines.iter().zip(by) {
        low = sum(&low, &times(&constant(ratio(*k)), &f.low), 1);
        high = sum(&high, &times(&constant(ratio(*k)), &f.high), 1);
    }
    Relation { low, high, rel }
}

/// A claim for a plain `inequalities` step, drawn around a point and
/// judged by how it was made.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let point: BTreeMap<&'static str, BigInt> = LETTERS
        .iter()
        .map(|x| (*x, BigInt::from(r.below(7)) - 3))
        .collect();
    let count = 1 + r.below(3) as usize;
    let shared = &LETTERS[count..];
    let equations = r.below(4) == 0;
    let lines: Vec<Relation> = LETTERS[..count]
        .iter()
        .map(|own| {
            let rel = if equations {
                Rel::Eq
            } else if r.below(2) == 0 {
                Rel::Lt
            } else {
                Rel::Le
            };
            line(r, own, shared, rel, &point)
        })
        .collect();
    let strict = lines.iter().any(|f| f.rel == Rel::Lt);
    let sums = if equations {
        Rel::Eq
    } else if strict {
        Rel::Lt
    } else {
        Rel::Le
    };
    let once = vec![1; count];
    let (claim, verdict) = match r.below(4) {
        // Their sums, as the step adds them.
        0 | 1 => (summed(&lines, &once, sums), Verdict::Holds(true)),
        // A move: a line taken twice, or a strict sum weakened.
        2 => {
            let mut twice = once.clone();
            twice[0] = 2;
            let weakened = strict && r.below(2) == 0;
            let made = if weakened {
                summed(&lines, &once, Rel::Le)
            } else {
                summed(&lines, &twice, sums)
            };
            let ne = strict && r.below(3) == 0;
            if ne {
                (
                    summed(&lines, &once, Rel::Ne),
                    Verdict::Refused(vec![A_WEAKENING]),
                )
            } else {
                (made, Verdict::Refused(vec![A_MOVE]))
            }
        }
        // Their sums, moved to fail at p.
        _ => {
            let mut made = summed(&lines, &once, sums);
            let value = at(&made.low, &point) - at(&made.high, &point);
            // The larger side moved below the smaller by one, or to meet it
            // where the claim is strict.
            let shift = match sums {
                Rel::Lt => value,
                _ => value - BigRational::one(),
            };
            made.high = sum(&made.high, &constant(shift), 1);
            (made, Verdict::Holds(false))
        }
    };
    let mut header: Vec<String> =
        LETTERS.iter().map(|x| format!("let {x} ∈ ℝ")).collect();
    let mut labels = Vec::new();
    for f in &lines {
        header.push(format!("assume {}", written(r, g, f)));
        labels.push(format!("H{}", header.len()));
    }
    let shown = format!(
        "{:?} {:?} {:?} from {:?} at {point:?}",
        claim.low,
        claim.rel,
        claim.high,
        lines
            .iter()
            .map(|f| format!("{:?} {:?} {:?}", f.low, f.rel, f.high))
            .collect::<Vec<_>>()
    );
    Drawn {
        header,
        written: written(r, g, &claim),
        justification: format!("inequalities, from {}", labels.join(", ")),
        verdict,
        shown,
    }
}
