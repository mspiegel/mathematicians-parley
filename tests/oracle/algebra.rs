//! Claims for `algebra`: an expression in letters set equal to what it
//! expands to, or to that with one coefficient moved. The oracle is the
//! test's own expansion to a polynomial, which shares no code with the
//! normaliser; two sides are one claim exactly when they expand alike
//! (`METHODS.md`, algebra: with no cited equation, `L − R` normalises to 0).

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use parley::formula::grammar::Grammar;

use crate::gen::{made, term, Drawn, Expr};
use crate::judge::Verdict;
use crate::shared::Random;

/// The letters a claim is written in, each said real by a `let` line.
const LETTERS: [&str; 3] = ["x", "y", "z"];

/// A product of letters, each with its power, in the order of `LETTERS`.
type Monomial = Vec<(&'static str, u32)>;

/// A polynomial: each monomial with its coefficient, none of them 0.
type Poly = BTreeMap<Monomial, BigRational>;

fn constant(c: BigRational) -> Poly {
    let mut p = Poly::new();
    if !c.is_zero() {
        p.insert(Vec::new(), c);
    }
    p
}

fn sum(a: &Poly, b: &Poly, sign: i32) -> Poly {
    let mut out = a.clone();
    for (m, c) in b {
        let c = if sign < 0 { -c.clone() } else { c.clone() };
        let total = out.get(m).cloned().unwrap_or_else(BigRational::zero) + c;
        if total.is_zero() {
            out.remove(m);
        } else {
            out.insert(m.clone(), total);
        }
    }
    out
}

fn times(a: &Poly, b: &Poly) -> Poly {
    let mut out = Poly::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let mut powers: BTreeMap<&'static str, u32> = BTreeMap::new();
            for (x, k) in ma.iter().chain(mb) {
                *powers.entry(x).or_default() += k;
            }
            let m: Monomial = LETTERS
                .iter()
                .filter_map(|x| powers.get(x).map(|k| (*x, *k)))
                .collect();
            out = sum(&out, &BTreeMap::from([(m, ca * cb)]), 1);
        }
    }
    out
}

/// What an expression expands to: letters, numerals, sums, products,
/// whole powers, and division by a numeral other than 0, which is all a
/// drawn expression holds.
fn expanded(e: &Expr) -> Poly {
    match e {
        Expr::Num(n) => constant(BigRational::from_integer(n.clone())),
        Expr::Letter(x) => BTreeMap::from([(vec![(*x, 1)], BigRational::one())]),
        Expr::Neg(a) => sum(&Poly::new(), &expanded(a), -1),
        Expr::Add(a, b) => sum(&expanded(a), &expanded(b), 1),
        Expr::Sub(a, b) => sum(&expanded(a), &expanded(b), -1),
        Expr::Mul(a, b) => times(&expanded(a), &expanded(b)),
        Expr::Div(a, b) => {
            let Expr::Num(d) = &**b else {
                unreachable!("an algebra claim divides only by a numeral")
            };
            let scale = constant(BigRational::new(BigInt::one(), d.clone()));
            times(&expanded(a), &scale)
        }
        Expr::Pow(a, k) => {
            let base = expanded(a);
            (0..*k).fold(constant(BigRational::one()), |acc, _| times(&acc, &base))
        }
        Expr::Mod(..) => unreachable!("an algebra claim holds no remainder"),
    }
}

/// A small numeral, 1 to 5, or of either sign where `signed`.
fn small(r: &mut Random, signed: bool) -> BigInt {
    let n = BigInt::from(1 + r.below(5));
    if signed && r.below(3) == 0 {
        -n
    } else {
        n
    }
}

/// An expression in the letters, at most `depth` deep.
fn drawn(r: &mut Random, depth: u32) -> Expr {
    if depth == 0 || r.below(4) == 0 {
        return match r.below(3) {
            0 => Expr::Num(small(r, true)),
            _ => Expr::Letter(LETTERS[r.below(3) as usize]),
        };
    }
    let sub = |r: &mut Random| Box::new(drawn(r, depth - 1));
    match r.below(7) {
        0 => Expr::Neg(sub(r)),
        1 | 2 => Expr::Add(sub(r), sub(r)),
        3 => Expr::Sub(sub(r), sub(r)),
        4 => Expr::Mul(sub(r), sub(r)),
        5 => Expr::Pow(sub(r), 2 + r.below(2) as u32),
        _ => Expr::Div(sub(r), Box::new(Expr::Num(small(r, false) + 1))),
    }
}

fn letters_in(e: &Expr, out: &mut Vec<&'static str>) {
    match e {
        Expr::Letter(x) => {
            if !out.contains(x) {
                out.push(x);
            }
        }
        Expr::Num(_) => {}
        Expr::Neg(a) | Expr::Pow(a, _) => letters_in(a, out),
        Expr::Add(a, b)
        | Expr::Sub(a, b)
        | Expr::Mul(a, b)
        | Expr::Div(a, b)
        | Expr::Mod(a, b) => {
            letters_in(a, out);
            letters_in(b, out);
        }
    }
}

/// A polynomial written out: its terms by degree, highest first, each a
/// coefficient and its letters; a coefficient of 1 is not written, nor a
/// power of 1.
fn written_out(p: &Poly) -> Expr {
    let mut terms: Vec<(&Monomial, &BigRational)> = p.iter().collect();
    terms
        .sort_by_key(|(m, _)| std::cmp::Reverse(m.iter().map(|(_, k)| k).sum::<u32>()));
    let mut out: Option<Expr> = None;
    for (m, c) in terms {
        let size = c.abs();
        let mut product: Option<Expr> = None;
        for (x, k) in m {
            let factor = if *k == 1 {
                Expr::Letter(x)
            } else {
                Expr::Pow(Box::new(Expr::Letter(x)), *k)
            };
            product = Some(match product {
                None => factor,
                Some(p) => Expr::Mul(Box::new(p), Box::new(factor)),
            });
        }
        let coefficient = if size.is_integer() {
            Expr::Num(size.to_integer())
        } else {
            Expr::Div(
                Box::new(Expr::Num(size.numer().clone())),
                Box::new(Expr::Num(size.denom().clone())),
            )
        };
        let term = match product {
            None => coefficient,
            Some(p) if size.is_one() => p,
            Some(p) => Expr::Mul(Box::new(coefficient), Box::new(p)),
        };
        out = Some(match (out, c.is_negative()) {
            (None, false) => term,
            (None, true) => Expr::Neg(Box::new(term)),
            (Some(o), false) => Expr::Add(Box::new(o), Box::new(term)),
            (Some(o), true) => Expr::Sub(Box::new(o), Box::new(term)),
        });
    }
    out.unwrap_or(Expr::Num(BigInt::zero()))
}

/// The value of a polynomial at a point, each letter a whole number.
fn at(p: &Poly, point: &BTreeMap<&'static str, BigInt>) -> BigRational {
    p.iter()
        .map(|(m, c)| {
            m.iter().fold(c.clone(), |acc, (x, k)| {
                acc * BigRational::from_integer(point[x].pow(*k))
            })
        })
        .sum()
}

/// An expression that is not a constant once expanded, in `letters` alone
/// where they are given.
fn not_constant(
    r: &mut Random,
    depth: u32,
    letters: Option<&[&'static str]>,
) -> (Expr, Poly) {
    loop {
        let e = drawn(r, depth);
        let p = expanded(&e);
        let mut seen = Vec::new();
        letters_in(&e, &mut seen);
        let within = letters.is_none_or(|l| seen.iter().all(|x| l.contains(x)));
        if within && p.keys().any(|m| !m.is_empty()) {
            return (e, p);
        }
    }
}

/// How `algebra` refuses a claim that does not follow from what it cites,
/// and one that multiplies two cited equations by a term.
pub const NOT_ONE_STEP: &str =
    "added and subtracted with at most one equation multiplied by a term";

/// A claim `algebra` derives from cited equations (`METHODS.md`, algebra:
/// `L − R` is a sum of the cited `lᵢ − rᵢ`, each times a polynomial, at
/// most one of which has a letter in it), or one that cannot follow.
///
/// Each cited equation says what a polynomial is at a point p of whole
/// numbers, so all of them hold at p. A claim made true is a polynomial
/// with the cited polynomials added on one side, one times a polynomial and
/// the other times a numeral, and their values on the other; a claim made
/// false is that one more, which fails at p while every cited line holds
/// there, so nothing it cites gives it.
///
/// Where both are multiplied by a term, the first by one in x and y and the
/// second by one in z, the claim is not one step: the two polynomials share
/// no letter, so neither multiplier is a number plus a multiple of the
/// other equation, and no sum with one multiplier a number makes the claim.
pub fn derived(r: &mut Random, g: &Grammar) -> Drawn {
    let point: BTreeMap<&'static str, BigInt> = LETTERS
        .iter()
        .map(|x| (*x, BigInt::from(r.below(7)) - 3))
        .collect();
    // The first equation in x and y, the second in z alone, so that neither
    // follows from the other and a step citing both uses both.
    let cited = 1 + r.below(2) as usize;
    let mut equations: Vec<(Expr, Poly, BigRational)> = Vec::new();
    for i in 0..cited {
        let letters: &[&'static str] = if i == 0 { &["x", "y"] } else { &["z"] };
        let (e, p) = not_constant(r, 2, Some(letters));
        let value = at(&p, &point);
        equations.push((e, p, value));
    }
    // Which equation a term multiplies, or both.
    let multiplied = r.below(cited as u64 + 1) as usize;
    let both = cited == 2 && multiplied == 2;
    let base = expanded(&drawn(r, 2));
    let mut left = base.clone();
    let mut right = base;
    for (i, (_, p, value)) in equations.iter().enumerate() {
        // With two cited, a multiplier is in its own equation's letters: one
        // the other equation divides would make that one the first's
        // multiple, and the claim would follow from the first alone.
        let own: &[&'static str] = if i == 0 { &["x", "y"] } else { &["z"] };
        let factor = if i == multiplied.min(cited - 1) || both {
            not_constant(r, 1, (cited == 2).then_some(own)).1
        } else {
            constant(BigRational::from_integer(small(r, true)))
        };
        left = sum(&left, &times(&factor, p), 1);
        right = sum(&right, &times(&factor, &constant(value.clone())), 1);
    }
    let holds = both || r.below(2) == 0;
    if !holds {
        right = sum(&right, &constant(BigRational::one()), 1);
    }
    let (left, right) = (written_out(&left), written_out(&right));
    let mut letters = Vec::new();
    letters_in(&left, &mut letters);
    letters_in(&right, &mut letters);
    for (e, _, _) in &equations {
        letters_in(e, &mut letters);
    }
    letters.sort_by_key(|x| LETTERS.iter().position(|l| l == x));
    let mut header: Vec<String> =
        letters.iter().map(|x| format!("let {x} ∈ ℝ")).collect();
    let mut labels = Vec::new();
    for (e, _, value) in &equations {
        let value = written_out(&constant(value.clone()));
        let node = made(g, "_ = _", vec![term(g, e), term(g, &value)]);
        header.push(format!("assume {}", g.print(&node)));
        labels.push(format!("H{}", header.len()));
    }
    let node = made(g, "_ = _", vec![term(g, &left), term(g, &right)]);
    Drawn {
        header,
        written: g.print(&node),
        justification: format!("algebra, from {}", labels.join(", ")),
        verdict: if both {
            Verdict::Refused(vec![NOT_ONE_STEP])
        } else {
            Verdict::Holds(holds)
        },
        shown: format!(
            "{left:?} = {right:?}, from {:?} at {point:?}",
            equations
                .iter()
                .map(|(e, _, v)| format!("{e:?} = {v}"))
                .collect::<Vec<_>>()
        ),
    }
}

/// An identity of `algebra`'s, or one coefficient away from one.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let left = loop {
        let e = drawn(r, 3);
        let mut seen = Vec::new();
        letters_in(&e, &mut seen);
        if !seen.is_empty() {
            break e;
        }
    };
    let mut right_poly = expanded(&left);
    if r.below(2) == 0 {
        // One term's coefficient moved by one, or a term added.
        let keys: Vec<Monomial> = right_poly.keys().cloned().collect();
        let moved = if keys.is_empty() || r.below(3) == 0 {
            vec![(LETTERS[r.below(3) as usize], 1)]
        } else {
            keys[r.below(keys.len() as u64) as usize].clone()
        };
        right_poly = sum(
            &right_poly,
            &BTreeMap::from([(moved, BigRational::one())]),
            1,
        );
    }
    let right = written_out(&right_poly);
    let (left, right) = if r.below(4) == 0 {
        (right, left)
    } else {
        (left, right)
    };
    let mut letters = Vec::new();
    letters_in(&left, &mut letters);
    letters_in(&right, &mut letters);
    letters.sort_by_key(|x| LETTERS.iter().position(|l| l == x));
    let verdict = Verdict::Holds(expanded(&left) == expanded(&right));
    let node = made(g, "_ = _", vec![term(g, &left), term(g, &right)]);
    Drawn {
        header: letters.iter().map(|x| format!("let {x} ∈ ℝ")).collect(),
        written: g.print(&node),
        justification: "algebra".to_string(),
        verdict,
        shown: format!("{left:?} = {right:?}"),
    }
}
