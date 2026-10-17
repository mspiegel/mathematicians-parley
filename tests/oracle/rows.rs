//! Claims for what a step of inequalities does besides adding lines:
//! rows that name their manipulation, `transitivity` and `antisymmetry`
//! (`METHODS.md`, inequalities, Rows; transitivity; antisymmetry).
//!
//! The oracle is the table of manipulations the document gives, applied to
//! linear relations drawn around a point:
//!
//! - rows: a cited line, then one to three rows, each the row above with
//!   t added to both sides, both sides multiplied by a numeral other than
//!   0 and the relation turned round where it is negative, an equation's
//!   sides swapped, or the relation weakened. Such rows are taken; one row
//!   made otherwise, multiplied by a negative number and not turned round,
//!   added to on one side only, or weakened the wrong way, is refused;
//! - transitivity: lines whose terms meet, chained in the order cited, and
//!   the claim relating the first term to the last by the chain's
//!   relation, `=` where every link is, `<` where one is, and `≤`
//!   otherwise. A claim by another relation is refused;
//! - antisymmetry: a ≤ b and b ≤ a, and a = b. A strict order among them
//!   is refused.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed};

use parley::formula::grammar::Grammar;

use crate::algebra::{at, constant, small, sum, times, written_out, Poly, LETTERS};
use crate::gen::{made, term, Drawn};
use crate::judge::Verdict;
use crate::order::{line, Rel, Relation};
use crate::shared::Random;

/// What the tools say of a row that is not the row above so manipulated, of
/// a chain's claim by another relation, and of two lines antisymmetry does
/// not take.
const NOT_THE_ROW: &str = "is not the row above";
const NOT_THE_CHAIN: &str = "and the chain it cites gives";
const NOT_ANTISYMMETRIC: &str = "by antisymmetry what is not two lines";

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn point(r: &mut Random) -> BTreeMap<&'static str, BigInt> {
    LETTERS
        .iter()
        .map(|x| (*x, BigInt::from(r.below(7)) - 3))
        .collect()
}

fn header() -> Vec<String> {
    LETTERS.iter().map(|x| format!("let {x} ∈ ℝ")).collect()
}

fn side(g: &Grammar, p: &Poly) -> parley::formula::node::Node {
    term(g, &written_out(p))
}

/// A relation written smaller side first, as a row writes it.
fn plain(g: &Grammar, f: &Relation) -> String {
    let (l, h) = (side(g, &f.low), side(g, &f.high));
    let pattern = match f.rel {
        Rel::Le => "_ ≤ _",
        Rel::Lt => "_ < _",
        Rel::Eq => "_ = _",
        Rel::Ne => "_ ≠ _",
    };
    g.print(&made(g, pattern, vec![l, h]))
}

/// A numeral as a reason writes it: `2`, `−1`, `1/2`.
fn numeral_said(c: &BigRational) -> String {
    let sign = if c.is_negative() { "−" } else { "" };
    let c = c.abs();
    if c.is_integer() {
        format!("{sign}{}", c.numer())
    } else {
        format!("{sign}{}/{}", c.numer(), c.denom())
    }
}

/// One row: what it says, and the reason it names.
struct Row {
    says: Relation,
    reason: String,
}

/// The rows written under `inequalities`, each with its reason beside it.
fn rows_written(g: &Grammar, rows: &[Row]) -> String {
    let mut out = "inequalities".to_string();
    for row in rows {
        out.push_str(&format!(
            "\n      {}        {}",
            plain(g, &row.says),
            row.reason
        ));
    }
    out
}

/// The row above with a manipulation, made as the table says, or, where
/// `wrong`, otherwise: multiplied by a negative number and not turned
/// round, added to on one side only, or weakened the wrong way. None where
/// the manipulation drawn does not apply to the row.
fn manipulated(
    r: &mut Random,
    g: &Grammar,
    above: &Relation,
    wrong: bool,
) -> Option<Row> {
    match r.below(4) {
        0 => {
            let t = if r.below(2) == 0 {
                constant(BigRational::from_integer(small(r, true)))
            } else {
                BTreeMap::from([(
                    vec![("y", 1)],
                    BigRational::from_integer(small(r, true)),
                )])
            };
            let reason = format!("adding {}", g.print(&side(g, &t)));
            let high = if wrong {
                above.high.clone()
            } else {
                sum(&above.high, &t, 1)
            };
            Some(Row {
                says: Relation {
                    low: sum(&above.low, &t, 1),
                    high,
                    rel: above.rel,
                },
                reason,
            })
        }
        1 => {
            let negative = wrong || r.below(2) == 0;
            let c = match (negative, r.below(3)) {
                (true, 0) => ratio(-1, 1),
                (true, _) => ratio(-2, 1),
                (false, 0) => ratio(1, 2),
                (false, _) => ratio(2 + r.below(2) as i64, 1),
            };
            let by = |p: &Poly| times(&constant(c.clone()), p);
            // A negative multiplier turns an order round, which a wrong row
            // does not; an equation is not turned, and a wrong row of one
            // multiplies one side only, which is no wrong row where the other
            // side is 0.
            let order = above.rel != Rel::Eq;
            if !order && wrong && above.high.is_empty() {
                return None;
            }
            let (low, high) = match (order, negative && !wrong, wrong) {
                (true, true, _) => (by(&above.high), by(&above.low)),
                (false, _, true) => (by(&above.low), above.high.clone()),
                _ => (by(&above.low), by(&above.high)),
            };
            Some(Row {
                says: Relation {
                    low,
                    high,
                    rel: above.rel,
                },
                reason: format!("multiplying by {}", numeral_said(&c)),
            })
        }
        2 if above.rel == Rel::Eq && !wrong => Some(Row {
            says: Relation {
                low: above.high.clone(),
                high: above.low.clone(),
                rel: Rel::Eq,
            },
            reason: "symmetry".to_string(),
        }),
        _ => {
            let rel = match (above.rel, wrong) {
                (Rel::Lt, false) => [Rel::Le, Rel::Ne][r.below(2) as usize],
                (Rel::Eq, false) => Rel::Le,
                (Rel::Le, true) => Rel::Lt,
                (Rel::Eq, true) => Rel::Lt,
                _ => return None,
            };
            Some(Row {
                says: Relation {
                    low: above.low.clone(),
                    high: above.high.clone(),
                    rel,
                },
                reason: "weakening".to_string(),
            })
        }
    }
}

/// A step of rows, drawn from a cited line and judged by how its rows were
/// made.
pub fn rows(r: &mut Random, g: &Grammar) -> Drawn {
    let p = point(r);
    let rel = [Rel::Le, Rel::Lt, Rel::Eq][r.below(3) as usize];
    let cited = line(r, "x", &["y"], rel, &p);
    let mut header = header();
    header.push(format!("assume {}", plain(g, &cited)));
    let label = format!("H{}", header.len());
    let count = 1 + r.below(3) as usize;
    let wrong_at = (r.below(3) == 0).then(|| r.below(count as u64) as usize);
    let mut rows = vec![Row {
        says: cited.clone(),
        reason: label,
    }];
    let mut made_wrong = false;
    while rows.len() <= count {
        let above = &rows.last().expect("the cited row").says;
        // Once a row says ≠ nothing more is made of it.
        if above.rel == Rel::Ne {
            break;
        }
        let wrong = wrong_at == Some(rows.len() - 1);
        if let Some(row) = manipulated(r, g, above, wrong) {
            made_wrong |= wrong;
            rows.push(row);
        }
    }
    let claim = plain(g, &rows.last().expect("a last row").says);
    let verdict = if made_wrong {
        Verdict::Refused(vec![NOT_THE_ROW])
    } else {
        Verdict::Holds(true)
    };
    Drawn {
        header,
        written: claim,
        justification: rows_written(g, &rows),
        verdict,
        shown: rows
            .iter()
            .map(|row| format!("{} ({})", plain(g, &row.says), row.reason))
            .collect::<Vec<_>>()
            .join(" / "),
    }
}

/// A form in x and y with a constant, moved so that its value at p is
/// `value`.
fn valued(
    r: &mut Random,
    p: &BTreeMap<&'static str, BigInt>,
    value: &BigRational,
) -> Poly {
    let mut out = constant(BigRational::from_integer(small(r, true)));
    for x in ["x", "y"] {
        if r.below(3) != 0 {
            let term = BTreeMap::from([(
                vec![(x, 1)],
                BigRational::from_integer(small(r, true)),
            )]);
            out = sum(&out, &term, 1);
        }
    }
    let moved = value.clone() - at(&out, p);
    sum(&out, &constant(moved), 1)
}

/// A chain cited by `transitivity`, drawn going up around a point, and a
/// claim by its relation or another.
pub fn transitivity(r: &mut Random, g: &Grammar) -> Drawn {
    let p = point(r);
    let links = 2 + r.below(2) as usize;
    let mut value = BigRational::from_integer(BigInt::from(r.below(5)) - 2);
    let mut terms = vec![valued(r, &p, &value)];
    let mut rels = Vec::new();
    for _ in 0..links {
        let rel = [Rel::Eq, Rel::Le, Rel::Lt][r.below(3) as usize];
        if rel != Rel::Eq {
            value += BigRational::from_integer(BigInt::from(r.below(3)));
            if rel == Rel::Lt {
                value += BigRational::one();
            }
        }
        terms.push(valued(r, &p, &value));
        rels.push(rel);
    }
    let mut header = header();
    let mut labels = Vec::new();
    for (i, rel) in rels.iter().enumerate() {
        let link = Relation {
            low: terms[i].clone(),
            high: terms[i + 1].clone(),
            rel: *rel,
        };
        header.push(format!("assume {}", plain(g, &link)));
        labels.push(format!("H{}", header.len()));
    }
    let chain = if rels.iter().all(|rel| *rel == Rel::Eq) {
        Rel::Eq
    } else if rels.contains(&Rel::Lt) {
        Rel::Lt
    } else {
        Rel::Le
    };
    let (claimed, verdict) = if r.below(3) == 0 {
        let other = match chain {
            Rel::Eq => Rel::Le,
            Rel::Le => Rel::Lt,
            _ => Rel::Le,
        };
        (other, Verdict::Refused(vec![NOT_THE_CHAIN]))
    } else {
        (chain, Verdict::Holds(true))
    };
    let claim = Relation {
        low: terms[0].clone(),
        high: terms[links].clone(),
        rel: claimed,
    };
    Drawn {
        header,
        written: plain(g, &claim),
        justification: format!("transitivity, from {}", labels.join(", ")),
        verdict,
        shown: format!("{rels:?} claimed {claimed:?}"),
    }
}

/// `a ≤ b` and `b ≤ a` cited by `antisymmetry`, written either way round,
/// and a = b; or one of them strict, which is refused.
pub fn antisymmetry(r: &mut Random, g: &Grammar) -> Drawn {
    let p = point(r);
    let value = BigRational::from_integer(BigInt::from(r.below(5)) - 2);
    // Two terms written differently, so that the claim is no a = a.
    let a = valued(r, &p, &value);
    let b = loop {
        let b = valued(r, &p, &value);
        if b != a {
            break b;
        }
    };
    let strict = r.below(3) == 0;
    let first = Relation {
        low: a.clone(),
        high: b.clone(),
        rel: if strict { Rel::Lt } else { Rel::Le },
    };
    let second = Relation {
        low: b.clone(),
        high: a.clone(),
        rel: Rel::Le,
    };
    let mut header = header();
    header.push(format!("assume {}", plain(g, &first)));
    header.push(format!("assume {}", plain(g, &second)));
    let (n, m) = (header.len() - 1, header.len());
    let claim = Relation {
        low: a,
        high: b,
        rel: Rel::Eq,
    };
    let verdict = if strict {
        Verdict::Refused(vec![NOT_ANTISYMMETRIC])
    } else {
        Verdict::Holds(true)
    };
    Drawn {
        header,
        written: plain(g, &claim),
        justification: format!("antisymmetry, from H{n}, H{m}"),
        verdict,
        shown: format!("strict {strict}"),
    }
}
