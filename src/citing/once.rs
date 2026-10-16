//! A membership in a number system that the page says once, where a letter
//! is introduced, and no step writes again (`READERS.md`, membership said
//! once): a numeral, a letter in the set its introducing line names and the
//! number systems containing that one, and a term built from those by +, −,
//! ·, negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a
//! quotient whose divisor a fact says is not zero.
//!
//! The elaborator builds the same memberships by the same tables in
//! `rules` (`Elaborator::introduced_membership`), so the two tools agree on
//! which ones a step need not write.

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::formula::page::template;
use crate::formula::{Node, Sort, Sorts};
use crate::matching::{alike_top, standard, substitute_apart, Binding};
use crate::rules::{self, lookup, System};

use super::library::Library;
use super::parts::Parts;

/// The number system each letter is introduced in, by the letter as the
/// page writes it.
pub type Introduced = IndexMap<String, System>;

/// The letter and number system a sentence `x ∈ ℝ` introduces; None for any
/// other sentence, a term in place of the letter included.
pub fn introduction(said: &Node) -> Option<(String, System)> {
    let [letter, set] = said.children.as_slice() else {
        return None;
    };
    if said.notation != "membership" || said.text != "∈" || !letter.is_name() {
        return None;
    }
    let system = match set.notation.as_str() {
        "number-systems" => System::of_sign(&set.text)?,
        "integer-range" => range_system(set)?,
        _ => return None,
    };
    Some((letter.text.clone(), system))
}

/// The least number system the declared table puts a range {a, …, b} in:
/// ℕ from 1, ℕ₀ from 0, and ℤ from anywhere (`rules::RANGE_WITHIN`, which
/// the elaborator reads as well).
pub fn range_system(range: &Node) -> Option<System> {
    let start = range.children.first()?;
    let begins = (start.notation == "numeral")
        .then(|| {
            start
                .text
                .parse::<u32>()
                .ok()
                .and_then(rules::numeral_label)
        })
        .flatten();
    rules::RANGE_WITHIN
        .iter()
        .find(|(_, first, _)| first.is_none() || *first == begins)
        .and_then(|(system, _, _)| System::of_label(system))
}

/// The memberships the page says once of the terms `parts` names, in every
/// number system each is in, laid onto its facts. A letter is introduced by
/// `introduced` or by a fact of `parts` saying it is in a number system.
/// They are added after what a membership implies is read (`finished`), so
/// that `let k ∈ ℕ` gives k ∈ ℝ here and never k ≥ 1.
pub fn said_once(
    parts: &mut Parts,
    introduced: &Introduced,
    library: &Library,
    sorts: &Sorts,
) {
    let mut letters = introduced.clone();
    for f in &parts.facts {
        let [term, set] = f.children.as_slice() else {
            continue;
        };
        if f.notation == "membership"
            && term.is_name()
            && set.notation == "number-systems"
        {
            if let Some(system) = System::of_sign(&set.text) {
                letters.entry(term.text.clone()).or_insert(system);
            }
        }
    }
    let ctx = &library.ctx;
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    // The code's own forms read, each filled with the term at x and the set
    // at S. A notation database that does not declare what one writes says
    // nothing here, and its own checks report what it lacks.
    let form = |said: &'static str, term: &Node| -> Option<Node> {
        let made = template(said, library.env.g, &local).ok()?;
        let put = Binding::from([("x".to_string(), term.clone())]);
        Some(standard(&substitute_apart(&made, &put, ctx), ctx))
    };
    // S is read as the number system that fills it, whatever the page's S
    // is.
    let member = |sign: &'static str, term: &Node| -> Option<Node> {
        let set = template(sign, library.env.g, &local).ok()?;
        let mut sets = local.clone();
        sets.insert("S".into(), set.sort.clone());
        let made = template("x ∈ S", library.env.g, &sets).ok()?;
        let put =
            Binding::from([("x".to_string(), term.clone()), ("S".to_string(), set)]);
        Some(standard(&substitute_apart(&made, &put, ctx), ctx))
    };
    // A divisor is not zero where a fact says so, as `≠ 0` or as a sign.
    let nonzero = |d: &Node| -> bool {
        if numeral_nonzero(d) {
            return true;
        }
        ["x ≠ 0", "x > 0", "x < 0"].iter().any(|said| {
            form(said, d).is_some_and(|want| {
                parts.facts.iter().any(|f| alike_top(f, &want, ctx))
            })
        })
    };
    let seeded: Vec<Node> = parts.seed.values().cloned().collect();
    let mut seen = std::collections::BTreeSet::new();
    let mut out = Vec::new();
    for node in parts
        .facts
        .iter()
        .chain(&parts.claims)
        .chain(&seeded)
        .flat_map(|n| n.walk())
    {
        if !node.sort.is("number") || !seen.insert(node.shape().to_string()) {
            continue;
        }
        for (sign, label) in rules::SYSTEM_OF {
            let Some(system) = System::of_label(label) else {
                continue;
            };
            if within(&node, system, &letters, &nonzero, &|_, _| false) {
                out.extend(member(sign, &node));
            }
        }
    }
    parts.facts.extend(out);
}

/// Whether `term` is a number by what the page says once of the letters in
/// it: each letter one a fact puts in a number system or one `bound` binds
/// over one, as a "there is q ∈ ℤ" does its q; a divisor not zero only
/// where it is a numeral.
pub fn a_number_said_once(
    term: &Node,
    facts: &[Node],
    bound: &Introduced,
    ctx: &crate::matching::Context,
) -> bool {
    let mut letters = bound.clone();
    // A term a fact puts in a number system is a number there as a letter
    // is, and what +, − and · build from it is too: (x − a)·q(x) where a
    // line says q(x) ∈ ℂ.
    let mut atoms: Vec<(&Node, System)> = Vec::new();
    for f in facts {
        let [name, set] = f.children.as_slice() else {
            continue;
        };
        if f.notation != "membership" || set.notation != "number-systems" {
            continue;
        }
        let Some(system) = System::of_sign(&set.text) else {
            continue;
        };
        if name.is_name() {
            letters.entry(name.text.clone()).or_insert(system);
        } else {
            atoms.push((name, system));
        }
    }
    let nonzero = numeral_nonzero;
    let said = |t: &Node, system: System| {
        atoms.iter().any(|(a, s)| {
            crate::matching::alike(a, t, ctx, &IndexMap::new(), &IndexMap::new())
                && s.within(system)
        })
    };
    within(term, System::C, &letters, &nonzero, &said)
}

/// Whether `term` is in `system` by what the page says once, or by `said`,
/// which puts a term in a system as a line stating it does.
pub fn within(
    term: &Node,
    system: System,
    letters: &Introduced,
    nonzero: &dyn Fn(&Node) -> bool,
    said: &dyn Fn(&Node, System) -> bool,
) -> bool {
    if said(term, system) {
        return true;
    }
    if let Some(v) = value(term) {
        let whole = v.is_integer();
        return match system {
            System::N => whole && v.is_positive(),
            System::N0 => whole && !v.is_negative(),
            System::Z => whole,
            _ => true,
        };
    }
    if term.is_name() {
        return letters
            .get(&term.text)
            .is_some_and(|set| set.within(system));
    }
    let label = system.label();
    let both = |a: &Node, b: &Node| {
        within(a, system, letters, nonzero, said)
            && within(b, system, letters, nonzero, said)
    };
    match (
        term.notation.as_str(),
        term.text.as_str(),
        term.children.as_slice(),
    ) {
        ("unary-minus", _, [a]) => {
            lookup(rules::NEGATED, label).is_some()
                && within(a, system, letters, nonzero, said)
        }
        ("additive", "+", [a, b]) => {
            rules::closed("caddc", label).is_some() && both(a, b)
        }
        ("additive", "−", [a, b]) => {
            rules::closed("cmin", label).is_some() && both(a, b)
        }
        ("multiplicative", "·", [a, b]) | ("juxtaposition", _, [a, b]) => {
            rules::closed("cmul", label).is_some() && both(a, b)
        }
        ("multiplicative", "/", [a, b]) => {
            lookup(rules::DIVIDED, label).is_some() && both(a, b) && nonzero(b)
        }
        ("power", _, [a, e]) | ("superscript", _, [a, e]) => {
            whole_exponent(e, letters)
                && rules::closed("cexp", label).is_some()
                && within(a, system, letters, nonzero, said)
        }
        _ => false,
    }
}

/// Whether a power's exponent makes it a product of copies of its base:
/// a numeral in ℕ₀, or a letter introduced in ℕ or ℕ₀ (`READERS.md`,
/// membership said once). 2^j with j ∈ ℕ₀ is then a number wherever 2 is,
/// and 2^(−1), 0^k with k ∈ ℤ, or 2^(j + 1) are not said once this way.
fn whole_exponent(exponent: &Node, letters: &Introduced) -> bool {
    if let Some(v) = value(exponent) {
        return v.is_integer() && !v.is_negative();
    }
    exponent.is_name()
        && letters
            .get(&exponent.text)
            .is_some_and(|set| set.within(System::N0))
}

/// Whether a divisor is a numeral other than zero, the one divisor whose
/// `≠ 0` a step need not write (`SYNTAX.md`): 10^0 is worked out to 1, and
/// is no numeral.
pub fn numeral_nonzero(divisor: &Node) -> bool {
    divisor.notation == "numeral" && value(divisor).is_some_and(|v| !v.is_zero())
}

/// The value of a term built from numerals alone, worked out exactly; None
/// where a letter stands in it, or a division by zero.
fn value(term: &Node) -> Option<BigRational> {
    let kids = term.children.as_slice();
    match (term.notation.as_str(), term.text.as_str(), kids) {
        ("numeral", said, []) => numeral(said),
        ("unary-minus", _, [a]) => Some(-value(a)?),
        ("additive", "+", [a, b]) => Some(value(a)? + value(b)?),
        ("additive", "−", [a, b]) => Some(value(a)? - value(b)?),
        ("multiplicative", "·", [a, b]) | ("juxtaposition", _, [a, b]) => {
            Some(value(a)? * value(b)?)
        }
        ("multiplicative", "/", [a, b]) => {
            let d = value(b)?;
            (!d.is_zero()).then(|| value(a)).flatten().map(|n| n / d)
        }
        ("power", _, [a, e]) | ("superscript", _, [a, e]) => {
            let e = value(e)?;
            let k = e.is_integer().then(|| e.to_integer().to_u32()).flatten()?;
            // Past a few hundred the number is not one a page writes, and
            // working it out is not the point.
            let base = value(a)?;
            (k <= 512).then(|| num_traits::pow(base, k as usize))
        }
        _ => None,
    }
}

/// A decimal numeral's value: digits, with a point or without one.
fn numeral(said: &str) -> Option<BigRational> {
    let (whole, part) = said.split_once('.').unwrap_or((said, ""));
    if whole.is_empty()
        || !(whole.chars().chain(part.chars())).all(|c| c.is_ascii_digit())
    {
        return None;
    }
    let digits: BigInt = format!("{whole}{part}").parse().ok()?;
    let scale = num_traits::pow(BigInt::from(10), part.len());
    Some(BigRational::new(digits, scale))
}
