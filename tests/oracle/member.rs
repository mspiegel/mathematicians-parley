//! Claims for `membership`: a term built from atoms the page says are in a
//! number system, said to be in one (`METHODS.md`, membership).
//!
//! The oracle is the closure table the document gives, worked out over the
//! term: each atom is in the system its line says, a sum, product or power
//! to a numeral is in a system when its parts are, a difference or negation
//! when the system holds negatives, and a quotient by a numeral in ℚ, ℝ or
//! ℂ when its parts are. That is the least system the term is in; a claim of
//! that one or a larger one is proved, and of a smaller one is refused,
//! since the table is all the method reads.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::numeral;
use parley::formula::Sort;

use crate::gen::{made, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

/// The number systems, each inside the next.
const SYSTEMS: [&str; 6] = ["ℕ", "ℕ₀", "ℤ", "ℚ", "ℝ", "ℂ"];
const NAT: usize = 0;
const NAT0: usize = 1;
const INT: usize = 2;
const RATIONAL: usize = 3;
const REAL: usize = 4;

/// The lines every claim is written under: letters, said once, and
/// functions, whose values a step cites the type of.
const HEADER: [&str; 7] = [
    "let a ∈ ℕ",
    "let b ∈ ℕ₀",
    "let c ∈ ℤ",
    "let x ∈ ℝ",
    "let f : ℕ → ℤ",
    "let g : ℕ → ℝ",
    "let h : ℕ → ℕ",
];

/// A term of `membership`'s.
#[derive(Clone, Debug)]
enum Term {
    /// A numeral, 0 to 5.
    Num(u32),
    /// A letter, said to be in its system where it is let.
    Letter(&'static str),
    /// f(a), g(a) or h(a): the function's value at a.
    Value(&'static str),
    /// 2^b.
    TwoToB,
    /// c mod a.
    Remainder,
    Neg(Box<Term>),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    /// A power to a numeral, 2 or 3.
    Pow(Box<Term>, u32),
    /// A quotient by a numeral, 2 to 5.
    Div(Box<Term>, u32),
}

impl Term {
    /// Whether it holds anything but numerals: a term of numerals alone is
    /// worked out, not read by the table.
    fn open(&self) -> bool {
        match self {
            Term::Num(_) => false,
            Term::Letter(_) | Term::Value(_) | Term::TwoToB | Term::Remainder => true,
            Term::Neg(a) | Term::Pow(a, _) | Term::Div(a, _) => a.open(),
            Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) => a.open() || b.open(),
        }
    }

    /// Whether an atom past the letters is in it, which is what makes its
    /// membership a step's to write.
    fn has_atom(&self) -> bool {
        match self {
            Term::Num(_) | Term::Letter(_) => false,
            Term::Value(_) | Term::TwoToB | Term::Remainder => true,
            Term::Neg(a) | Term::Pow(a, _) | Term::Div(a, _) => a.has_atom(),
            Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) => {
                a.has_atom() || b.has_atom()
            }
        }
    }

    fn functions(&self, out: &mut Vec<&'static str>) {
        match self {
            Term::Value(f) => {
                if !out.contains(f) {
                    out.push(f);
                }
            }
            Term::Neg(a) | Term::Pow(a, _) | Term::Div(a, _) => a.functions(out),
            Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) => {
                a.functions(out);
                b.functions(out);
            }
            _ => {}
        }
    }
}

/// The value of a term of numerals alone.
fn value(t: &Term) -> BigRational {
    let two = |a: &Term, b: &Term| (value(a), value(b));
    match t {
        Term::Num(n) => BigRational::from_integer(BigInt::from(*n)),
        Term::Neg(a) => -value(a),
        Term::Add(a, b) => {
            let (a, b) = two(a, b);
            a + b
        }
        Term::Sub(a, b) => {
            let (a, b) = two(a, b);
            a - b
        }
        Term::Mul(a, b) => {
            let (a, b) = two(a, b);
            a * b
        }
        Term::Pow(a, k) => (0..*k).fold(BigRational::one(), |acc, _| acc * value(a)),
        Term::Div(a, d) => value(a) / BigRational::from_integer(BigInt::from(*d)),
        _ => unreachable!("a term of numerals alone"),
    }
}

/// The least system the closure table puts a term in. A term of numerals
/// alone is worked out, and is in the least system its value is in
/// (`SYNTAX.md`: `10 − 1 ∈ ℕ`, worked out).
fn least(t: &Term) -> usize {
    if !t.open() {
        let v = value(t);
        return if !v.is_integer() {
            RATIONAL
        } else if v.is_positive() {
            NAT
        } else if v.is_zero() {
            NAT0
        } else {
            INT
        };
    }
    match t {
        Term::Num(0) => NAT0,
        Term::Num(_) => NAT,
        Term::Letter("a") => NAT,
        Term::Letter("b") => NAT0,
        Term::Letter("c") => INT,
        Term::Letter(_) => REAL,
        Term::Value("f") => INT,
        Term::Value("g") => REAL,
        Term::Value(_) => NAT,
        Term::TwoToB => NAT,
        Term::Remainder => NAT0,
        Term::Neg(a) => least(a).max(INT),
        Term::Add(a, b) | Term::Mul(a, b) => least(a).max(least(b)),
        Term::Sub(a, b) => least(a).max(least(b)).max(INT),
        Term::Pow(a, _) => least(a),
        Term::Div(a, _) => least(a).max(RATIONAL),
    }
}

fn drawn(r: &mut Random, depth: u32) -> Term {
    if depth == 0 || r.below(3) == 0 {
        return match r.below(9) {
            0 | 1 => Term::Num(r.below(6) as u32),
            2 => Term::Letter(["a", "b", "c", "x"][r.below(4) as usize]),
            3..=5 => Term::Value(["f", "g", "h"][r.below(3) as usize]),
            6 | 7 => Term::TwoToB,
            _ => Term::Remainder,
        };
    }
    let sub = |r: &mut Random| Box::new(drawn(r, depth - 1));
    match r.below(7) {
        0 => Term::Neg(sub(r)),
        1 | 2 => Term::Add(sub(r), sub(r)),
        3 => Term::Sub(sub(r), sub(r)),
        4 => Term::Mul(sub(r), sub(r)),
        5 => Term::Pow(sub(r), 2 + r.below(2) as u32),
        _ => Term::Div(sub(r), 2 + r.below(4) as u32),
    }
}

fn letter(name: &str) -> Node {
    Node::name(Sort::of("number"), name)
}

fn node(g: &Grammar, t: &Term) -> Node {
    let two = |a: &Term, b: &Term, p: &str| made(g, p, vec![node(g, a), node(g, b)]);
    match t {
        Term::Num(n) => numeral(&n.to_string()),
        Term::Letter(x) => letter(x),
        Term::Value(f) => made(
            g,
            "_(_)",
            vec![
                Node::name(Sort::of("function from number to number"), f),
                letter("a"),
            ],
        ),
        Term::TwoToB => made(g, "_^_", vec![numeral("2"), letter("b")]),
        Term::Remainder => made(g, "_ mod _", vec![letter("c"), letter("a")]),
        Term::Neg(a) => made(g, "−_", vec![node(g, a)]),
        Term::Add(a, b) => two(a, b, "_ + _"),
        Term::Sub(a, b) => two(a, b, "_ − _"),
        Term::Mul(a, b) => two(a, b, "_ · _"),
        Term::Pow(a, k) => made(g, "_^_", vec![node(g, a), numeral(&k.to_string())]),
        Term::Div(a, d) => made(g, "_ / _", vec![node(g, a), numeral(&d.to_string())]),
    }
}

/// A claim for `membership`, drawn and judged.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let t = loop {
        let t = drawn(r, 3);
        if t.has_atom() {
            break t;
        }
    };
    let least = least(&t);
    // Systems at and around the least, so that claims a system too small
    // are drawn about as often as ones that hold.
    let system = (least + r.below(4) as usize)
        .saturating_sub(2)
        .min(SYSTEMS.len() - 1);
    let node = made(
        g,
        "_ ∈ _",
        vec![node(g, &t), made(g, SYSTEMS[system], Vec::new())],
    );
    // A function's value cites the function's type; a letter's membership,
    // the point's among them, is said once and is not cited.
    let mut functions = Vec::new();
    t.functions(&mut functions);
    // In the order a citation names labels, by number (`SYNTAX.md`).
    let mut places: Vec<usize> = functions
        .iter()
        .map(|f| {
            ["f", "g", "h"]
                .iter()
                .position(|x| x == f)
                .expect("a function")
        })
        .collect();
    places.sort();
    let labels: Vec<String> = places.iter().map(|at| format!("H{}", 5 + at)).collect();
    let justification = if labels.is_empty() {
        "membership".to_string()
    } else {
        format!("membership, from {}", labels.join(", "))
    };
    // Each system holds the ones before it.
    let holds = system >= least;
    Drawn {
        header: HEADER.iter().map(|s| s.to_string()).collect(),
        written: g.print(&node),
        justification,
        verdict: Verdict::Holds(holds),
        shown: format!("{t:?} least {}", SYSTEMS[least]),
    }
}
