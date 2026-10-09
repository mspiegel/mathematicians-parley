//! A membership in a number system that the page says once, where a letter
//! is introduced, and no step writes again (`READERS.md`, membership said
//! once): a numeral, a letter in the set its introducing line names and the
//! number systems containing that one, and a term built from those by +, −,
//! ·, negation, a power to a numeral, and a quotient whose divisor a fact
//! says is not zero.
//!
//! The elaborator builds the same memberships by the same tables in
//! `rules` (`Elaborator::introduced_membership`), so the two tools agree on
//! which ones a step need not write.

use indexmap::IndexMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::formula::{parse_here, Node, Sort, Sorts};
use crate::matching::{alike_top, standard, substitute, Binding};
use crate::rules::{self, lookup};

use super::library::Library;
use super::parts::Parts;

/// The number system each letter is introduced in, by the letter as the
/// page writes it, as `rules::SYSTEM_OF` labels it.
pub type Introduced = IndexMap<String, &'static str>;

/// The letter and number system a sentence `x ∈ ℝ` introduces; None for any
/// other sentence, a term in place of the letter included.
pub fn introduction(sentence: &str) -> Option<(String, &'static str)> {
    let (name, sign) = str::trim(sentence).split_once(" ∈ ")?;
    let name = str::trim(name);
    let letter =
        !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '′');
    if !letter {
        return None;
    }
    Some((name.to_string(), rules::system_of(str::trim(sign))?))
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
            if let Some(system) = rules::system_of(&set.text) {
                letters.entry(term.text.clone()).or_insert(system);
            }
        }
    }
    let ctx = &library.ctx;
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    let form = |said: &str, term: &Node| -> Option<Node> {
        let mut put = Binding::new();
        put.insert("x".into(), term.clone());
        let made = parse_here(said, library.env.g, &local).ok()?;
        Some(standard(&substitute(&made, &put), ctx))
    };
    // A divisor is not zero where a fact says so, as `≠ 0` or as a sign.
    let nonzero = |d: &Node| -> bool {
        if let Some(v) = value(d) {
            return !v.is_zero();
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
        for (sign, system) in rules::SYSTEM_OF {
            if within(&node, system, &letters, &nonzero) {
                if let Some(fact) = form(&format!("x ∈ {sign}"), &node) {
                    out.push(fact);
                }
            }
        }
    }
    parts.facts.extend(out);
}

/// Whether `term` is in `system` by what the page says once.
fn within(
    term: &Node,
    system: &str,
    letters: &Introduced,
    nonzero: &dyn Fn(&Node) -> bool,
) -> bool {
    if let Some(v) = value(term) {
        let whole = v.is_integer();
        return match system {
            "cn" => whole && v.is_positive(),
            "cn0" => whole && !v.is_negative(),
            "cz" => whole,
            _ => true,
        };
    }
    if term.is_name() {
        return letters
            .get(&term.text)
            .is_some_and(|set| rules::within_path(Some(set), Some(system)).is_some());
    }
    let both = |a: &Node, b: &Node| {
        within(a, system, letters, nonzero) && within(b, system, letters, nonzero)
    };
    match (
        term.notation.as_str(),
        term.text.as_str(),
        term.children.as_slice(),
    ) {
        ("unary-minus", _, [a]) => {
            lookup(rules::NEGATED, system).is_some()
                && within(a, system, letters, nonzero)
        }
        ("additive", "+", [a, b]) => {
            rules::closed("caddc", system).is_some() && both(a, b)
        }
        ("additive", "−", [a, b]) => {
            rules::closed("cmin", system).is_some() && both(a, b)
        }
        ("multiplicative", "·", [a, b]) | ("juxtaposition", _, [a, b]) => {
            rules::closed("cmul", system).is_some() && both(a, b)
        }
        ("multiplicative", "/", [a, b]) => {
            lookup(rules::DIVIDED, system).is_some() && both(a, b) && nonzero(b)
        }
        ("power", _, [a, e]) => {
            value(e).is_some_and(|v| v.is_integer() && !v.is_negative())
                && rules::closed("cexp", system).is_some()
                && within(a, system, letters, nonzero)
        }
        ("square", _, [a]) => {
            rules::closed("cexp", system).is_some()
                && within(a, system, letters, nonzero)
        }
        _ => false,
    }
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
        ("power", _, [a, e]) => {
            let e = value(e)?;
            let k = e.is_integer().then(|| e.to_integer().to_u32()).flatten()?;
            // Past a few hundred the number is not one a page writes, and
            // working it out is not the point.
            let base = value(a)?;
            (k <= 512).then(|| num_traits::pow(base, k as usize))
        }
        ("square", _, [a]) => {
            let v = value(a)?;
            Some(v.clone() * v)
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
