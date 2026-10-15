//! Whether an `inspection` step holds (`METHODS.md`, inspection): a claim
//! about sets listed in full, checked element by element against what the
//! lines the step cites say. The terms are kernel terms (`terms::
//! term_of_node`), so that what a line says and what the claim asks meet as
//! their targets make them: "b₁ joins A and B" says the ends of b₁ are
//! {A, B}, and "A is incident with b₁" asks A among the ends of b₁. The
//! proof the build writes of what is decided here is `crate::elab::
//! inspection`.

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};

use super::field::{closed_value, decide_closed, Value, Verdict, Q};
use super::numerals::numeral_term;
use crate::mm::kernel::{same, Term};
use crate::outcome::Built;

/// What the lines an inspection cites say, sorted by the four kinds of
/// sentence the method reads, and every sentence as it stands.
pub struct Facts {
    /// A term and the set it is said to be: `V = {A, B, C, D}`, or the ends
    /// of an edge an edge's "joins" gives.
    listed: Vec<Said>,
    /// Two terms said to differ.
    distinct: Vec<Said>,
    /// A term and the term of numerals alone it is said to be worth.
    worth: Vec<Said>,
    /// "for all x ∈ S, l = r": what gives l at each element of S.
    every: Vec<Every>,
    /// Every sentence cited, which settles a property it says or denies.
    said: Vec<Term>,
    /// Why a claim was past what the method settles, where one was.
    past: std::cell::RefCell<Option<String>>,
}

/// One side of a cited sentence and what it says of it.
struct Said {
    term: Term,
    is: Term,
}

/// A cited "for all x ∈ set, left = right".
struct Every {
    letter: Term,
    set: Term,
    left: Term,
    right: Term,
}

impl Facts {
    /// The facts in what `cited` says, each sentence a kernel term.
    pub fn of(cited: &[Term]) -> Facts {
        let mut facts = Facts {
            listed: Vec::new(),
            distinct: Vec::new(),
            worth: Vec::new(),
            every: Vec::new(),
            said: cited.to_vec(),
            past: std::cell::RefCell::new(None),
        };
        for fact in cited {
            match (fact.label(), fact.children()) {
                (Some("wceq"), [term, is]) if listing(is) => facts.listed.push(Said {
                    term: term.clone(),
                    is: is.clone(),
                }),
                (Some("wceq"), [term, is]) if closed(is) => facts.worth.push(Said {
                    term: term.clone(),
                    is: is.clone(),
                }),
                (Some("wn"), [inner]) => {
                    if let (Some("wceq"), [a, b]) = (inner.label(), inner.children()) {
                        facts.distinct.push(Said {
                            term: a.clone(),
                            is: b.clone(),
                        });
                    }
                }
                (Some("wral"), [body, letter, set]) => {
                    if let (Some("wceq"), [left, right]) =
                        (body.label(), body.children())
                    {
                        facts.every.push(Every {
                            letter: letter.clone(),
                            set: set.clone(),
                            left: left.clone(),
                            right: right.clone(),
                        });
                    }
                }
                _ => {}
            }
        }
        facts
    }

    /// Whether `claim` holds by inspection of the facts.
    pub fn decide(&self, claim: &Term) -> Inspected {
        let found = self.holds(claim, DEPTH);
        if let Some(why) = self.past.borrow_mut().take() {
            return Inspected::Unsettled(why);
        }
        match found {
            Some(true) => Inspected::Holds,
            Some(false) => Inspected::Fails,
            None => Inspected::Undecided,
        }
    }

    fn holds(&self, claim: &Term, depth: usize) -> Option<bool> {
        let depth = depth.checked_sub(1)?;
        if self.said.iter().any(|s| same(s, claim)) {
            return Some(true);
        }
        if self.said.iter().any(|s| denies(s, claim)) {
            return Some(false);
        }
        match (claim.label(), claim.children()) {
            (Some("wn"), [inner]) => return self.holds(inner, depth).map(|b| !b),
            (Some("wcel"), [element, set]) if set.label() == Some("cprime") => {
                let n = whole(&self.number(element, depth)?)?;
                // A composite shows its least factor at any size, and a prime
                // is settled by the primes up to 23 only below 29².
                let prime = is_prime(&n);
                if prime && n >= BigUint::from(PRIMES_SETTLED) {
                    *self.past.borrow_mut() = Some(format!(
                        "inspection settles whether a number below {PRIMES_SETTLED} is prime, by trial division by the primes up to 23, and {n} is not below {PRIMES_SETTLED}"
                    ));
                    return None;
                }
                return Some(prime);
            }
            (Some("wcel"), [element, set]) => {
                if let Some(elements) = self.elements(set, depth) {
                    return self.among(element, &elements);
                }
            }
            (Some("wceq"), [a, b]) => {
                if let (Some(one), Some(other)) =
                    (self.elements(a, depth), self.elements(b, depth))
                {
                    return self.same_set(&one, &other);
                }
                if let (Some(one), Some(other)) =
                    (self.number(a, depth), self.number(b, depth))
                {
                    return Some(one == other);
                }
                if same(a, b) {
                    return Some(true);
                }
            }
            _ => {}
        }
        // A property of numbers at terms the facts give values: deg(A) is
        // odd once deg(A) = 5, worked out as `arithmetic` works it.
        let valued = self.valued(claim, depth);
        match decide_closed(&valued) {
            Built(Verdict::Holds(b)) => Some(b),
            _ => None,
        }
    }

    /// The elements of a set the claim or the facts list; None where none
    /// lists it.
    fn elements(&self, set: &Term, depth: usize) -> Option<Vec<Term>> {
        let depth = depth.checked_sub(1)?;
        match (set.label(), set.children()) {
            (Some("c0"), []) => return Some(Vec::new()),
            (Some("csn"), [a]) => return Some(vec![a.clone()]),
            (Some("cpr"), [a, b]) => return Some(vec![a.clone(), b.clone()]),
            (Some("ctp"), [a, b, c]) => {
                return Some(vec![a.clone(), b.clone(), c.clone()])
            }
            (Some("cun"), [a, b]) => {
                let mut out = self.elements(a, depth)?;
                out.extend(self.elements(b, depth)?);
                return Some(out);
            }
            (Some("crab"), [property, letter, over]) => {
                let mut kept = Vec::new();
                for element in self.elements(over, depth)? {
                    if self.holds(&put(property, letter, &element), depth)? {
                        kept.push(element);
                    }
                }
                return Some(kept);
            }
            _ => {}
        }
        self.listed
            .iter()
            .find(|l| same(&l.term, set))
            .and_then(|l| self.elements(&l.is, depth))
    }

    /// The value of a number the claim writes in numerals or the facts give
    /// one; None where nothing does.
    fn number(&self, term: &Term, depth: usize) -> Option<Q> {
        let depth = depth.checked_sub(1)?;
        if let Built(Value::Exact(v)) = closed_value(term) {
            return Some(v);
        }
        if let (Some("cfv"), [set, size]) = (term.label(), term.children()) {
            if size.label() == Some("chash") {
                let elements = self.elements(set, depth)?;
                return self.count(&elements).map(|n| Q::from_integer(n.into()));
            }
        }
        if let Some(w) = self.worth.iter().find(|w| same(&w.term, term)) {
            return self.number(&w.is, depth);
        }
        let given = self.given(term, depth)?;
        self.number(&given, depth)
    }

    /// What a cited "for all" equation gives `term` at an element of its
    /// set: `deg(B)` from "for all x ∈ V, deg(x) = …" once V lists B.
    fn given(&self, term: &Term, depth: usize) -> Option<Term> {
        for every in &self.every {
            let Some(elements) = self.elements(&every.set, depth) else {
                continue;
            };
            for element in elements {
                if same(&put(&every.left, &every.letter, &element), term) {
                    return Some(put(&every.right, &every.letter, &element));
                }
            }
        }
        None
    }

    /// `claim` with each part the facts give a value of numerals alone put
    /// as that value.
    fn valued(&self, claim: &Term, depth: usize) -> Term {
        if let Some(n) = self.number(claim, depth).and_then(|v| whole(&v)) {
            return numeral_term(&n);
        }
        if claim.variable().is_some() || claim.children().is_empty() {
            return claim.clone();
        }
        let children: Vec<Term> = claim
            .children()
            .iter()
            .map(|c| self.valued(c, depth))
            .collect();
        Term::apply(claim.label().unwrap_or(""), children)
    }

    /// Whether `element` is one of `elements`: Some(true) where it is,
    /// Some(false) where the facts say it differs from each.
    fn among(&self, element: &Term, elements: &[Term]) -> Option<bool> {
        let mut differs = true;
        for e in elements {
            match self.equal(element, e) {
                Some(true) => return Some(true),
                Some(false) => {}
                None => differs = false,
            }
        }
        differs.then_some(false)
    }

    /// Whether two sets the facts list have the same elements.
    fn same_set(&self, one: &[Term], other: &[Term]) -> Option<bool> {
        for e in one {
            if !self.among(e, other)? {
                return Some(false);
            }
        }
        for e in other {
            if !self.among(e, one)? {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Whether two elements are one: the same term, or two numbers of one
    /// value; Some(false) where they are numbers of two values, or the
    /// facts say they differ.
    fn equal(&self, a: &Term, b: &Term) -> Option<bool> {
        if same(a, b) {
            return Some(true);
        }
        if let (Built(Value::Exact(x)), Built(Value::Exact(y))) =
            (closed_value(a), closed_value(b))
        {
            return Some(x == y);
        }
        let said = self.distinct.iter().any(|d| {
            (same(&d.term, a) && same(&d.is, b)) || (same(&d.term, b) && same(&d.is, a))
        });
        if said {
            return Some(false);
        }
        None
    }

    /// How many elements a list holds, a name written twice counted once;
    /// None where the facts do not say two of them differ or are one.
    fn count(&self, elements: &[Term]) -> Option<u64> {
        let mut kept: Vec<&Term> = Vec::new();
        for e in elements {
            let mut seen = false;
            for k in &kept {
                if self.equal(e, k)? {
                    seen = true;
                    break;
                }
            }
            if !seen {
                kept.push(e);
            }
        }
        Some(kept.len() as u64)
    }
}

/// How deep the decider follows facts into facts: a property read through
/// a set-builder over a set a fact lists, at an element a "for all" gives a
/// value of.
const DEPTH: usize = 24;

/// The least number whose being prime trial division by the primes up to
/// 23 does not settle, 29² (`METHODS.md`, inspection).
const PRIMES_SETTLED: u32 = 841;

/// What inspection finds of a claim.
pub enum Inspected {
    Holds,
    /// The facts show it false.
    Fails,
    /// The method cannot settle it, and why: a prime past what trial
    /// division by the primes up to 23 settles.
    Unsettled(String),
    /// The facts settle it neither way.
    Undecided,
}

/// Whether a term is a set written by listing, or the empty set.
fn listing(term: &Term) -> bool {
    matches!(term.label(), Some("c0" | "csn" | "cpr" | "ctp" | "cun"))
}

/// Whether a term is built from numerals alone.
fn closed(term: &Term) -> bool {
    matches!(closed_value(term), Built(Value::Exact(_)))
}

/// Whether `said` is the denial of `claim`, or `claim` of `said`.
fn denies(said: &Term, claim: &Term) -> bool {
    let not = |a: &Term, b: &Term| matches!((a.label(), a.children()), (Some("wn"), [inner]) if same(inner, b));
    not(said, claim) || not(claim, said)
}

/// `term` with `letter`, an atom, put as `value` wherever it stands.
fn put(term: &Term, letter: &Term, value: &Term) -> Term {
    if same(term, letter) {
        return value.clone();
    }
    if term.variable().is_some() || term.children().is_empty() {
        return term.clone();
    }
    let children: Vec<Term> = term
        .children()
        .iter()
        .map(|c| put(c, letter, value))
        .collect();
    Term::apply(term.label().unwrap_or(""), children)
}

/// A value that is a whole number not below zero, as a numeral spells it.
fn whole(value: &Q) -> Option<BigUint> {
    (value.is_integer() && !value.is_negative())
        .then(|| value.numer().to_biguint())
        .flatten()
}

/// Whether `n` is prime: at least 2, and no number from 2 to its square
/// root divides it.
fn is_prime(n: &BigUint) -> bool {
    if *n < BigUint::from(2u32) {
        return false;
    }
    let mut d = BigUint::from(2u32);
    while &d * &d <= *n {
        if (n % &d).is_zero() {
            return false;
        }
        d += BigUint::one();
    }
    true
}
