//! Whole numbers as set.mm writes them, read and spelt.
//!
//! A digit is its own constant, `c7`, and a longer number is set.mm's
//! decimal `; A B`: A the number its digits before the last make, B the last
//! digit, so 123 is `; ; 1 2 3`. The numbers are held as big integers, so a
//! product of sixty digits is spelt as exactly as a digit is. The closed
//! facts about them, proved, are the build's (`crate::elab::numerals`).

use num_bigint::BigUint;
use num_traits::{ToPrimitive, Zero};

use crate::mm::kernel::Term;
use crate::mm::Rpn;
use crate::rules::{digit_of, numeral_label};
use crate::t;

/// The digits before the last, and the last.
pub(crate) fn last_off(n: &BigUint) -> (BigUint, u32) {
    let last = (n % 10u32).to_u32().expect("a digit");
    (n / 10u32, last)
}

/// The number itself where it is one digit.
pub(crate) fn one_digit(n: &BigUint) -> Option<u32> {
    (*n < BigUint::from(10u32)).then(|| n.to_u32().expect("a digit"))
}

/// A whole number as set.mm spells it, in reverse Polish.
pub fn spell(value: impl Into<BigUint>) -> Rpn {
    spelt(&value.into())
}

pub(crate) fn spelt(value: &BigUint) -> Rpn {
    thread_local! {
        /// Each number spelt so far, which a proof about numbers asks for
        /// again at every digit.
        static SPELT: std::cell::RefCell<rustc_hash::FxHashMap<BigUint, Rpn>> =
            std::cell::RefCell::new(rustc_hash::FxHashMap::default());
    }
    if let Some(known) = SPELT.with(|s| s.borrow().get(value).cloned()) {
        return known;
    }
    let made = match one_digit(value) {
        Some(d) => t!(digit(d)),
        None => {
            let (upper, last) = last_off(value);
            t!(spelt(&upper), digit(last), "cdc")
        }
    };
    SPELT.with(|s| s.borrow_mut().insert(value.clone(), made.clone()));
    made
}

/// The number a term spells, where it is a digit or a decimal of digits
/// spelt as `spell` spells it: `; 0 5` is not how five is written, and is
/// read as no number.
pub fn value(term: &Term) -> Option<BigUint> {
    if term.variable().is_some() {
        return None;
    }
    let label = term.label()?;
    if let Some(d) = digit_of(label) {
        return term.children().is_empty().then(|| BigUint::from(d));
    }
    if label != "cdc" || term.children().len() != 2 {
        return None;
    }
    let upper = value(&term.children()[0])?;
    let last = term.children()[1].label().and_then(digit_of)?;
    (!upper.is_zero() && term.children()[1].children().is_empty())
        .then(|| upper * 10u32 + last)
}

pub(crate) fn digit(value: u32) -> &'static str {
    numeral_label(value).expect("a digit")
}

/// The numeral `value` as a term.
pub(crate) fn numeral_term(value: &BigUint) -> Term {
    match one_digit(value) {
        Some(d) => Term::apply(digit(d), Vec::new()),
        None => {
            let (upper, last) = last_off(value);
            Term::apply(
                "cdc",
                vec![numeral_term(&upper), Term::apply(digit(last), Vec::new())],
            )
        }
    }
}

/// The integer `value` as a term: its numeral, negated where it is below 0,
/// as `field::spell_coefficient` spells one.
pub(crate) fn integer_term(value: &num_bigint::BigInt) -> Term {
    let numeral = numeral_term(value.magnitude());
    match value.sign() {
        num_bigint::Sign::Minus => Term::apply("cneg", vec![numeral]),
        _ => numeral,
    }
}

/// The term with the numeral `value` written for the letter k.
pub fn at_number(term: &Term, k: &str, value: &BigUint) -> Term {
    put(term, k, &numeral_term(value))
}

/// Whether a term is the letter k used as a number, `cv k`.
pub(crate) fn is_letter(term: &Term, k: &str) -> bool {
    term.label() == Some("cv")
        && term.children().len() == 1
        && term.children()[0].variable() == Some(k)
}

/// The term with `at` written for the letter k.
pub(crate) fn put(term: &Term, k: &str, at: &Term) -> Term {
    if is_letter(term, k) {
        return at.clone();
    }
    match term.label() {
        Some(label) if term.variable().is_none() => Term::apply(
            label,
            term.children().iter().map(|c| put(c, k, at)).collect(),
        ),
        _ => term.clone(),
    }
}
