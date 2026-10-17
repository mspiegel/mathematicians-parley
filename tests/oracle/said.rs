//! Claims for the rule that a membership is said once (`SYNTAX.md`, a
//! membership in a number system is said once): an identity `x·T = T·x`
//! by `algebra` with nothing cited, which holds whatever T is, so what is
//! asked is only whether every atom of T is a number and every divisor
//! not zero by what the page says once.
//!
//! The oracle is the rule as the document gives it, worked over the term:
//! a numeral and a letter let in a number system are said once, and so is
//! what +, −, · build from them, a quotient by a numeral other than 0, a
//! power to a numeral or to a letter let in ℕ or ℕ₀, a term of numerals
//! alone that `arithmetic` works out (a factorial), and a sum whose term is
//! such a number at every index. A letter let only as an element is not,
//! nor a power to a letter in ℤ, nor a factorial of a letter, nor a
//! quotient by a letter, whose not being zero the step has to cite, nor a
//! sum whose term divides by its index. A claim the rule says is said once
//! is built and verified; any other is refused for the membership or the
//! divisor it lacks.

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::numeral;
use parley::formula::Sort;

use crate::gen::{made, Drawn};
use crate::judge::Verdict;
use crate::shared::Random;

/// The lines every claim is written under: letters in each number system,
/// and one that is only an element.
const HEADER: [&str; 6] = [
    "let a ∈ ℕ",
    "let b ∈ ℕ₀",
    "let c ∈ ℤ",
    "let x ∈ ℝ",
    "let z ∈ ℂ",
    "let p be an element",
];

/// What the tools say of an atom no line says is a number, and of a
/// divisor no line says is not zero.
const UNSAID_ATOM: &str = "∈ ℝ or ∈ ℂ, which this step needs";
const UNSAID_DIVISOR: &str = "≠ 0, which this step needs to divide by it";

/// A term of the rule's.
#[derive(Clone, Debug)]
enum Term {
    /// A numeral, 2 to 5, so that no identity element is written.
    Num(u32),
    /// A letter of the header.
    Letter(&'static str),
    Add(Box<Term>, Box<Term>),
    Sub(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
    /// A quotient by a numeral, 2 to 5.
    DivNum(Box<Term>, u32),
    /// A quotient by a letter of the header.
    DivLetter(Box<Term>, &'static str),
    /// A power to a numeral, 2 or 3.
    PowNum(Box<Term>, u32),
    /// A power to a letter of the header.
    PowLetter(Box<Term>, &'static str),
    /// n! of a numeral, 0 to 5.
    Factorial(u32),
    /// b!, of a letter.
    FactorialOfLetter,
    /// Σ(k = 1 to a) of a term of k.
    Sum(Summand),
}

/// A sum's term, over its index k.
#[derive(Clone, Copy, Debug)]
enum Summand {
    Squared,
    TimesX,
    Halved,
    Constant,
    Reciprocal,
}

/// Whether the page says the term is a number once, by the rule; a
/// divisor's not being zero is asked with it.
fn said(t: &Term) -> bool {
    match t {
        Term::Num(_) | Term::Factorial(_) => true,
        Term::Letter(l) => *l != "p",
        Term::Add(a, b) | Term::Sub(a, b) | Term::Mul(a, b) => said(a) && said(b),
        Term::DivNum(a, _) | Term::PowNum(a, _) => said(a),
        Term::DivLetter(..) | Term::FactorialOfLetter => false,
        Term::PowLetter(a, e) => matches!(*e, "a" | "b") && said(a),
        Term::Sum(s) => !matches!(s, Summand::Reciprocal),
    }
}

fn letter(name: &str) -> Node {
    Node::leaf("name", Sort::of("number"), name)
}

fn summand(g: &Grammar, s: Summand) -> Node {
    let k = letter("k");
    match s {
        Summand::Squared => made(g, "_^_", vec![k, numeral("2")]),
        Summand::TimesX => made(g, "_ · _", vec![k, letter("x")]),
        Summand::Halved => made(g, "_ / _", vec![k, numeral("2")]),
        Summand::Constant => letter("x"),
        Summand::Reciprocal => made(g, "_ / _", vec![numeral("1"), k]),
    }
}

fn node(g: &Grammar, t: &Term) -> Node {
    let two = |a: &Term, b: &Term, p: &str| made(g, p, vec![node(g, a), node(g, b)]);
    match t {
        Term::Num(n) => numeral(&n.to_string()),
        Term::Letter(l) => letter(l),
        Term::Add(a, b) => two(a, b, "_ + _"),
        Term::Sub(a, b) => two(a, b, "_ − _"),
        Term::Mul(a, b) => two(a, b, "_ · _"),
        Term::DivNum(a, d) => {
            made(g, "_ / _", vec![node(g, a), numeral(&d.to_string())])
        }
        Term::DivLetter(a, d) => made(g, "_ / _", vec![node(g, a), letter(d)]),
        Term::PowNum(a, k) => made(g, "_^_", vec![node(g, a), numeral(&k.to_string())]),
        Term::PowLetter(a, e) => made(g, "_^_", vec![node(g, a), letter(e)]),
        Term::Factorial(n) => made(g, "_!", vec![numeral(&n.to_string())]),
        Term::FactorialOfLetter => made(g, "_!", vec![letter("b")]),
        Term::Sum(s) => made(
            g,
            "Σ(_ = _ to _) _",
            vec![letter("k"), numeral("1"), letter("a"), summand(g, *s)],
        ),
    }
}

const LETTERS: [&str; 6] = ["a", "b", "c", "x", "z", "p"];

/// A leaf: a numeral, a letter, a factorial or a sum.
fn leaf(r: &mut Random) -> Term {
    match r.below(10) {
        0..=2 => Term::Num(2 + r.below(4) as u32),
        3..=6 => Term::Letter(LETTERS[r.below(LETTERS.len() as u64) as usize]),
        7 => {
            if r.below(3) == 0 {
                Term::FactorialOfLetter
            } else {
                Term::Factorial(r.below(6) as u32)
            }
        }
        _ => Term::Sum(
            [
                Summand::Squared,
                Summand::TimesX,
                Summand::Halved,
                Summand::Constant,
                Summand::Reciprocal,
            ][r.below(5) as usize],
        ),
    }
}

fn drawn(r: &mut Random, depth: u32) -> Term {
    if depth == 0 || r.below(3) == 0 {
        return leaf(r);
    }
    let sub = |r: &mut Random| Box::new(drawn(r, depth - 1));
    match r.below(8) {
        0 => Term::Add(sub(r), sub(r)),
        1 => Term::Sub(sub(r), sub(r)),
        2 => Term::Mul(sub(r), sub(r)),
        3 => Term::DivNum(sub(r), 2 + r.below(4) as u32),
        4 => Term::DivLetter(sub(r), ["a", "c", "x"][r.below(3) as usize]),
        5 => Term::PowNum(sub(r), 2 + r.below(2) as u32),
        _ => Term::PowLetter(sub(r), ["a", "b", "c"][r.below(3) as usize]),
    }
}

/// A claim for the said-once rule, drawn and judged.
pub fn claim(r: &mut Random, g: &Grammar) -> Drawn {
    let t = drawn(r, 2);
    let x = letter("x");
    let claim = made(
        g,
        "_ = _",
        vec![
            made(g, "_ · _", vec![x.clone(), node(g, &t)]),
            made(g, "_ · _", vec![node(g, &t), x]),
        ],
    );
    let verdict = if said(&t) {
        Verdict::Holds(true)
    } else {
        Verdict::Refused(vec![UNSAID_ATOM, UNSAID_DIVISOR])
    };
    Drawn {
        header: HEADER.iter().map(|s| s.to_string()).collect(),
        written: g.print(&claim),
        justification: "algebra".to_string(),
        verdict,
        shown: format!("{t:?}"),
    }
}
