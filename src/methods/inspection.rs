//! Whether an `inspection` step holds (`METHODS.md`, inspection): a claim
//! about sets listed in full, checked element by element against what the
//! lines the step cites say. The terms are kernel terms (`terms::
//! term_of_node`), so that what a line says and what the claim asks meet as
//! their targets make them: "b₁ joins A and B" says the ends of b₁ are
//! {A, B}, and "A is incident with b₁" asks A among the ends of b₁. The
//! proof the build writes of what is decided here is `crate::elab::
//! inspection`.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use super::field::{closed_value, decide_closed, Value, Verdict, Q};
use super::numerals::{integer_term, numeral_term};
use super::pairs;
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
                // An equation says its sides are one either way round:
                // `m = 97` and `97 = m` give m the value 97.
                (Some("wceq"), [a, b]) if listing(a) || listing(b) => {
                    let (term, is) = if listing(b) { (a, b) } else { (b, a) };
                    facts.listed.push(Said {
                        term: term.clone(),
                        is: is.clone(),
                    });
                }
                (Some("wceq"), [a, b]) if closed(a) || closed(b) => {
                    let (term, is) = if closed(b) { (a, b) } else { (b, a) };
                    facts.worth.push(Said {
                        term: term.clone(),
                        is: is.clone(),
                    });
                }
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
        let found = match self.membership_of(claim) {
            Some(member) => self.one_of(&member, claim),
            None => self.holds(claim, DEPTH),
        };
        if let Some(why) = self.past.borrow_mut().take() {
            return Inspected::Unsettled(why);
        }
        match found {
            Some(true) => Inspected::Holds,
            Some(false) => Inspected::Fails,
            None => Inspected::Undecided,
        }
    }

    /// The cited `t ∈ S` a line of equations joined by "or", or one equation
    /// alone, is read against: the first whose t is one side of every
    /// equation and whose S the facts list. None where the claim is no such
    /// line, or nothing cited puts its t in a listed set, and an equation is
    /// then read as an equation.
    fn membership_of(&self, claim: &Term) -> Option<Said> {
        if !matches!(claim.label(), Some("wo" | "wceq")) {
            return None;
        }
        let sentences = disjuncts(claim);
        self.said
            .iter()
            .find_map(|fact| match (fact.label(), fact.children()) {
                (Some("wcel"), [element, set])
                    if sentences.iter().all(|s| named(s, element).is_some())
                        && self.elements(set, DEPTH).is_some() =>
                {
                    Some(Said {
                        term: element.clone(),
                        is: set.clone(),
                    })
                }
                _ => None,
            })
    }

    /// Whether `claim`, a line of "or"s each saying what `member.term` is,
    /// has an equation for each element of the set `member` puts it in, and
    /// none for anything else, the elements compared as `equal` compares
    /// them, in any order (`METHODS.md`, inspection).
    fn one_of(&self, member: &Said, claim: &Term) -> Option<bool> {
        let elements = self.elements(&member.is, DEPTH)?;
        let names: Vec<Term> = disjuncts(claim)
            .iter()
            .filter_map(|s| named(s, &member.term))
            .collect();
        let one = |a: &Term, b: &Term| self.equal(a, b) == Some(true);
        if let Some(stray) = names.iter().find(|n| !elements.iter().any(|e| one(n, e)))
        {
            *self.past.borrow_mut() = Some(match shown(stray) {
                Some(s) => format!("{s} is not an element of the set the cited membership names"),
                None => "the claim names something that is not an element of the set the cited membership names".to_string(),
            });
            return None;
        }
        if let Some(missed) = elements.iter().find(|e| !names.iter().any(|n| one(e, n)))
        {
            *self.past.borrow_mut() = Some(match shown(missed) {
                Some(s) => format!("the claim leaves out {s}, an element of the set the cited membership names"),
                None => "the claim leaves out an element of the set the cited membership names".to_string(),
            });
            return None;
        }
        Some(true)
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
                if pairs::relation(claim).is_some() {
                    return self.equal(a, b);
                }
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
            // {a, …, b} lists the integers from a to b, none where b is
            // below a, its ends worked out where they are closed terms.
            (Some("co"), [from, to, how]) if how.label() == Some("cfz") => {
                let (Some(low), Some(high)) = (integer_value(from), integer_value(to))
                else {
                    *self.past.borrow_mut() = Some(
                        "inspection lists a range whose ends work out to integers, as arithmetic works one out".to_string(),
                    );
                    return None;
                };
                let listed = range_elements(&low, &high);
                if listed.is_none() {
                    let length = &high - &low + 1u32;
                    *self.past.borrow_mut() = Some(format!(
                        "inspection lists a range of at most {RANGE_LISTED} numerals, and the one from {low} to {high} holds {length}"
                    ));
                }
                return listed;
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
    /// facts say they differ. Two pairs are compared coordinate by
    /// coordinate (`super::pairs`).
    fn equal(&self, a: &Term, b: &Term) -> Option<bool> {
        if same(a, b) {
            return Some(true);
        }
        if let Some(pairs) =
            pairs::relation(&Term::apply("wceq", vec![a.clone(), b.clone()]))
        {
            let first = self.equal(&pairs.left[0], &pairs.right[0]);
            let second = self.equal(&pairs.left[1], &pairs.right[1]);
            return match (first, second) {
                (Some(false), _) | (_, Some(false)) => Some(false),
                (Some(true), Some(true)) => Some(true),
                _ => None,
            };
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

/// The most numerals a range `{a, …, b}` is read as a list of (`METHODS.md`,
/// inspection). A reader runs down a short list by eye, and a line of "or"s
/// with an equation for each of more numerals than this is no longer
/// something read at a glance; the build's proof also grows with each
/// element, a step of `fzsuc` and its numerals apiece.
pub const RANGE_LISTED: u32 = 64;

/// What inspection finds of a claim.
pub enum Inspected {
    Holds,
    /// The facts show it false.
    Fails,
    /// The method cannot settle it, and why: a prime past what trial
    /// division by the primes up to 23 settles, a range longer than
    /// `RANGE_LISTED`, or a line of "or"s that leaves out an element of the
    /// set it is read against or names something that set does not list.
    Unsettled(String),
    /// The facts settle it neither way.
    Undecided,
}

/// Whether a term is a set written by listing, the empty set, or a range
/// whose ends are integers.
fn listing(term: &Term) -> bool {
    match (term.label(), term.children()) {
        (Some("c0" | "csn" | "cpr" | "ctp" | "cun"), _) => true,
        (Some("co"), [from, to, how]) => {
            how.label() == Some("cfz")
                && integer_value(from).is_some()
                && integer_value(to).is_some()
        }
        _ => false,
    }
}

/// The integers from `low` to `high` as terms, none where `high` is below
/// `low`: a range as both tools list it. None past `RANGE_LISTED` of them.
pub fn range_elements(low: &BigInt, high: &BigInt) -> Option<Vec<Term>> {
    if high - low + 1u32 > BigInt::from(RANGE_LISTED) {
        return None;
    }
    let mut out = Vec::new();
    let mut k = low.clone();
    while k <= *high {
        out.push(integer_term(&k));
        k += 1u32;
    }
    Some(out)
}

/// The value of a term of numerals alone, where it is an integer: a range's
/// end as both tools read it.
pub fn integer_value(term: &Term) -> Option<BigInt> {
    match closed_value(term) {
        Built(Value::Exact(v)) if v.is_integer() => Some(v.to_integer()),
        _ => None,
    }
}

/// The sentences a line of "or"s joins, however it groups them, in the
/// order it writes them.
pub fn disjuncts(claim: &Term) -> Vec<Term> {
    match (claim.label(), claim.children()) {
        (Some("wo"), [a, b]) => {
            let mut out = disjuncts(a);
            out.extend(disjuncts(b));
            out
        }
        _ => vec![claim.clone()],
    }
}

/// What an equation says `t` is: its other side, of `t = s` or `s = t`.
fn named(sentence: &Term, t: &Term) -> Option<Term> {
    match (sentence.label(), sentence.children()) {
        (Some("wceq"), [a, b]) if same(a, t) => Some(b.clone()),
        (Some("wceq"), [a, b]) if same(b, t) => Some(a.clone()),
        _ => None,
    }
}

/// An element as a message names it: a number by its value, a name as it
/// is written; None for anything else.
fn shown(term: &Term) -> Option<String> {
    if let Some(name) = term.variable() {
        return Some(name.to_string());
    }
    match closed_value(term) {
        Built(Value::Exact(v)) => Some(v.to_string()),
        _ => None,
    }
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

/// The least factor of n above 1, n itself where n is prime; n at least 2.
pub(crate) fn least_factor(n: &BigUint) -> BigUint {
    let mut d = BigUint::from(2u32);
    while &d * &d <= *n {
        if (n % &d).is_zero() {
            return d;
        }
        d += BigUint::one();
    }
    n.clone()
}

/// Whether `n` is prime: at least 2, and no number from 2 to its square
/// root divides it.
pub(crate) fn is_prime(n: &BigUint) -> bool {
    *n >= BigUint::from(2u32) && least_factor(n) == *n
}
