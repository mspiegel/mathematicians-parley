//! Claims drawn at random from the forms `METHODS.md` says a method takes,
//! held as trees of the test's own, and written as the page writes them.
//!
//! The tree is the oracle's to judge (`judge.rs`) and the page's to read:
//! each node becomes the notation the database declares for it (`made_as`),
//! and the printer brackets it as the parser reads it, so the brackets a
//! claim needs are what the tools would write.

use num_bigint::BigInt;

use parley::formula::grammar::Grammar;
use parley::formula::node::Node;
use parley::formula::page::{made_as, numeral};
use parley::formula::Sort;

use crate::shared::Random;

/// One theorem drawn for a method: the lines of its header, its claim as
/// the page writes it, the justification of its one step, the oracle's
/// verdict, and the tree drawn, to print beside a fault.
pub struct Drawn {
    pub header: Vec<String>,
    pub written: String,
    pub justification: String,
    pub verdict: crate::judge::Verdict,
    pub shown: String,
}

/// A term of numerals, and for `algebra` of letters: what a method works
/// out.
#[derive(Clone, Debug)]
pub enum Expr {
    Num(BigInt),
    Letter(&'static str),
    Neg(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    /// A power to a whole numeral.
    Pow(Box<Expr>, u32),
    Mod(Box<Expr>, Box<Expr>),
}

/// The number systems a membership is said of.
#[derive(Clone, Copy, Debug)]
pub enum System {
    Nat,
    Nat0,
    Int,
    Rat,
    Real,
}

impl System {
    const ALL: [System; 5] = [
        System::Nat,
        System::Nat0,
        System::Int,
        System::Rat,
        System::Real,
    ];

    fn written(self) -> &'static str {
        match self {
            System::Nat => "ℕ",
            System::Nat0 => "ℕ₀",
            System::Int => "ℤ",
            System::Rat => "ℚ",
            System::Real => "ℝ",
        }
    }
}

/// A relation between two terms.
#[derive(Clone, Copy, Debug)]
pub enum Rel {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Rel {
    const ALL: [Rel; 6] = [Rel::Eq, Rel::Ne, Rel::Lt, Rel::Le, Rel::Gt, Rel::Ge];

    fn pattern(self) -> &'static str {
        match self {
            Rel::Eq => "_ = _",
            Rel::Ne => "_ ≠ _",
            Rel::Lt => "_ < _",
            Rel::Le => "_ ≤ _",
            Rel::Gt => "_ > _",
            Rel::Ge => "_ ≥ _",
        }
    }
}

/// A claim `arithmetic` is asked: a relation, a membership, or one of the
/// words whose records name it, and the denial of a word.
#[derive(Clone, Debug)]
pub enum Claim {
    Rel(Rel, Expr, Expr),
    /// The term in the system, or with `false`, not in it.
    Member(Expr, System, bool),
    /// The divisor, the number, and whether it is said or denied.
    Divides(Expr, Expr, bool),
    /// The number, and whether it is said even or said odd.
    Parity(Expr, bool),
    /// a ≡ b (mod n).
    Congruent(Expr, Expr, Expr),
}

/// How deep a drawn term may nest.
const DEPTH: u32 = 3;

/// A numeral of one to three digits, or nought, of either sign.
fn numeral_drawn(r: &mut Random) -> BigInt {
    let size = match r.below(4) {
        0 => r.below(3),
        1 => r.below(10),
        2 => r.below(100),
        _ => r.below(1000),
    };
    let n = BigInt::from(size);
    if r.below(4) == 0 {
        -n
    } else {
        n
    }
}

/// A term of numerals, at most `depth` deep.
pub fn expr(r: &mut Random, depth: u32) -> Expr {
    if depth == 0 || r.below(3) == 0 {
        return Expr::Num(numeral_drawn(r));
    }
    let sub = |r: &mut Random| Box::new(expr(r, depth - 1));
    match r.below(8) {
        0 => Expr::Neg(sub(r)),
        1 => Expr::Add(sub(r), sub(r)),
        2 => Expr::Sub(sub(r), sub(r)),
        3 => Expr::Mul(sub(r), sub(r)),
        4 => Expr::Div(sub(r), sub(r)),
        // A small base and exponent, so that no power is past what
        // `arithmetic` works out.
        5 => Expr::Pow(
            Box::new(Expr::Num(BigInt::from(r.below(7)) - 2)),
            r.below(4) as u32,
        ),
        6 => Expr::Mod(sub(r), sub(r)),
        _ => Expr::Num(numeral_drawn(r)),
    }
}

/// A claim of each form in turn, its terms drawn.
pub fn claim(r: &mut Random) -> Claim {
    let e = |r: &mut Random| expr(r, DEPTH);
    match r.below(5) {
        0 | 1 => {
            let rel = Rel::ALL[r.below(6) as usize];
            Claim::Rel(rel, e(r), e(r))
        }
        2 => Claim::Member(e(r), System::ALL[r.below(5) as usize], r.below(2) == 0),
        3 => match r.below(3) {
            0 => Claim::Divides(e(r), e(r), r.below(2) == 0),
            1 => Claim::Parity(e(r), r.below(2) == 0),
            _ => Claim::Congruent(e(r), e(r), e(r)),
        },
        _ => {
            // Two sides that are often equal, so that true equations and
            // orders between near values are drawn as well as false ones.
            let left = e(r);
            let right = match r.below(2) {
                0 => left.clone(),
                _ => Expr::Add(
                    Box::new(left.clone()),
                    Box::new(Expr::Num(numeral_drawn(r))),
                ),
            };
            Claim::Rel(Rel::ALL[r.below(6) as usize], left, right)
        }
    }
}

/// A claim for `arithmetic`, drawn and judged.
pub fn arithmetic(r: &mut Random, g: &Grammar) -> Drawn {
    let c = claim(r);
    Drawn {
        header: Vec::new(),
        written: written(g, &c),
        justification: "arithmetic".to_string(),
        verdict: crate::judge::arithmetic(&c),
        shown: format!("{c:?}"),
    }
}

/// The node the notation written `pattern` builds over `children`; the
/// notations named here are the database's own, so one missing is a fault
/// of the test.
pub fn made(g: &Grammar, pattern: &str, children: Vec<Node>) -> Node {
    made_as(g, pattern, children).unwrap_or_else(|| {
        panic!("the database declares no notation written {pattern}")
    })
}

/// A term as the page writes it.
pub fn term(g: &Grammar, e: &Expr) -> Node {
    let two = |a: &Expr, b: &Expr, p: &str| made(g, p, vec![term(g, a), term(g, b)]);
    match e {
        Expr::Num(n) if *n < BigInt::from(0) => {
            made(g, "−_", vec![numeral(&(-n).to_string())])
        }
        Expr::Num(n) => numeral(&n.to_string()),
        Expr::Letter(x) => Node::leaf("name", Sort::of("number"), x),
        Expr::Neg(a) => made(g, "−_", vec![term(g, a)]),
        Expr::Add(a, b) => two(a, b, "_ + _"),
        Expr::Sub(a, b) => two(a, b, "_ − _"),
        Expr::Mul(a, b) => two(a, b, "_ · _"),
        Expr::Div(a, b) => two(a, b, "_ / _"),
        Expr::Pow(a, k) => made(g, "_^_", vec![term(g, a), numeral(&k.to_string())]),
        Expr::Mod(a, b) => two(a, b, "_ mod _"),
    }
}

/// A claim as the page writes it.
pub fn written(g: &Grammar, c: &Claim) -> String {
    let node = match c {
        Claim::Rel(rel, a, b) => made(g, rel.pattern(), vec![term(g, a), term(g, b)]),
        Claim::Member(a, system, inside) => made(
            g,
            if *inside { "_ ∈ _" } else { "_ ∉ _" },
            vec![term(g, a), made(g, system.written(), Vec::new())],
        ),
        Claim::Divides(d, n, said) => {
            let divides = made(g, "_ divides _", vec![term(g, d), term(g, n)]);
            if *said {
                divides
            } else {
                made(g, "not _", vec![divides])
            }
        }
        Claim::Parity(n, even) => made(
            g,
            if *even { "_ is even" } else { "_ is odd" },
            vec![term(g, n)],
        ),
        Claim::Congruent(a, b, n) => {
            made(g, "_ ≡ _ (mod _)", vec![term(g, a), term(g, b), term(g, n)])
        }
    };
    g.print(&node)
}
