//! The number system a set letter's members are in, as the page's lines say
//! it: D of `D ⊆ ℝ` or `D ∈ 𝒫ℝ` holds reals, and c of `{1, …, i} ∖ c`
//! holds integers, as the set it is joined with does.
//!
//! A set's sort says only that it holds numbers. The checker records which
//! numbers (`CheckedTheorem::set_systems`), for a backend whose sets are
//! typed: Lean's `Set ℤ` or `Set ℝ`. Metamath's sets are untyped, so it
//! needs none of this.

use indexmap::IndexMap;

use crate::formula::{Node, Whole};
use crate::rules::System;

use super::once::{set_system, Introduced};

/// The number system each letter is in by the lines putting it in sets of
/// numbers, A of `A ∈ ℝ ∖ ℚ`: the widest of those sets' systems, a set
/// letter's by `sets` (`set_letter_systems`). A letter no line puts in such
/// a set is not among them.
pub fn element_systems(
    lines: &[&Node],
    letters: &Introduced,
    sets: &IndexMap<String, System>,
) -> IndexMap<String, System> {
    let mut out: IndexMap<String, System> = IndexMap::new();
    for node in lines.iter().flat_map(|l| l.walk()) {
        let [x, set] = node.children.as_slice() else {
            continue;
        };
        if node.notation() != crate::notations::MEMBERSHIP || !x.is_name() {
            continue;
        }
        let system = match set_system(set, letters) {
            Some(s) => s,
            None if set.is_name() => match sets.get(&*set.text) {
                Some(s) => *s,
                None => continue,
            },
            None => continue,
        };
        out.entry(x.text.to_string())
            .and_modify(|held| {
                if held.within(system) {
                    *held = system;
                }
            })
            .or_insert(system);
    }
    out
}

/// The function letters a line gives a type between sets of numbers, f of
/// `f : D → ℝ` with D a set of numbers, each with the systems of its domain
/// and codomain: a number system's, a range's or an interval's, or a set
/// letter's by `sets`.
pub fn function_systems(
    lines: &[&Node],
    letters: &Introduced,
    sets: &IndexMap<String, System>,
) -> IndexMap<String, Between> {
    let system = |set: &Node| match set_system(set, letters) {
        Some(s) => Some(s),
        None if set.is_name() => sets.get(&*set.text).copied(),
        None => None,
    };
    let mut out = IndexMap::new();
    for node in lines.iter().flat_map(|l| l.walk()) {
        let [f, from, to] = node.children.as_slice() else {
            continue;
        };
        if node.notation() != crate::notations::FUNCTION_TYPE || !f.is_name() {
            continue;
        }
        if let (Some(from), Some(to)) = (system(from), system(to)) {
            out.entry(f.text.to_string())
                .or_insert(Between { from, to });
        }
    }
    out
}

/// The systems of a function's domain and codomain (`function_systems`).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Between {
    pub from: System,
    pub to: System,
}

/// The number system each set letter of numbers holds, by the first line
/// that says it, in the order the lines are walked: a subset or member of
/// 𝒫 of a set of numbers, or a letter joined by ∪, ∩ or ∖ with one.
/// `letters` are the number letters, for an interval's ends.
pub fn set_letter_systems(
    lines: &[&Node],
    letters: &Introduced,
) -> IndexMap<String, System> {
    let mut found: IndexMap<String, System> = IndexMap::new();
    // A letter found makes a set of numbers of a line read earlier: until
    // no more are.
    loop {
        let before = found.len();
        for node in lines.iter().flat_map(|l| l.walk()) {
            let said = subset_system(&node, &found, letters)
                .or_else(|| joined_system(&node, &found, letters));
            if let Some((letter, system)) = said {
                found.entry(letter).or_insert(system);
            }
        }
        if found.len() == before {
            return found;
        }
    }
}

/// The number system a set's members are in: a number system's, a range's
/// or an interval's (`set_system`), a set letter's found already, and what
/// a set made from one of those by ∪, ∩, ∖ or {x ∈ A : …} holds. None for
/// any other set.
pub fn members_system(
    set: &Node,
    found: &IndexMap<String, System>,
    letters: &Introduced,
) -> Option<System> {
    if set.is_name() {
        return found.get(&*set.text).copied();
    }
    if let Some(system) = set_system(set, letters) {
        return Some(system);
    }
    match (&*set.notation_name(), set.children.as_slice()) {
        ("closed-interval" | "open-interval", _) => Some(System::R),
        ("set-operations", [a, b]) => members_system(a, found, letters)
            .or_else(|| members_system(b, found, letters)),
        ("set-builder", [_, a, _]) => members_system(a, found, letters),
        _ => None,
    }
}

/// D and the system of `D ⊆ S` or `D ∈ 𝒫S` where S holds numbers; None
/// for any other node.
fn subset_system(
    node: &Node,
    found: &IndexMap<String, System>,
    letters: &Introduced,
) -> Option<(String, System)> {
    let [d, whole] = node.children.as_slice() else {
        return None;
    };
    let whole = match (&*node.notation_name(), whole.children.as_slice()) {
        ("subset", _) => whole,
        ("membership", [inner]) if &*whole.notation_name() == "powerset" => inner,
        _ => return None,
    };
    if !d.is_name() {
        return None;
    }
    Some((d.text.to_string(), members_system(whole, found, letters)?))
}

/// A set letter of numbers not found yet that ∪, ∩ or ∖ joins with a set of
/// numbers, c of `{1, …, i} ∖ c`, and that set's system; None for any other
/// node.
fn joined_system(
    node: &Node,
    found: &IndexMap<String, System>,
    letters: &Introduced,
) -> Option<(String, System)> {
    if &*node.notation_name() != "set-operations" {
        return None;
    }
    let [a, b] = node.children.as_slice() else {
        return None;
    };
    let open = |n: &Node| n.is_name() && !found.contains_key(&*n.text);
    let (letter, other) = match (open(a), open(b)) {
        (true, false) => (a, b),
        (false, true) => (b, a),
        _ => return None,
    };
    let of_numbers = matches!(letter.sort.full(), Some(Whole::Set(m))
        if matches!(**m, Whole::Number));
    if !of_numbers {
        return None;
    }
    Some((
        letter.text.to_string(),
        members_system(other, found, letters)?,
    ))
}

/// Whether the set of that name is the one a function maps from, `t : X →
/// Z`, and the lines apply the function only at letters a range binds,
/// t(k) of "for all k ∈ {a, …, b}" or ∏(k ∈ {a, …, b}) t(k): a set of
/// integers.
pub fn domain_at_integers(set: &str, functions: &[Node], said: &[&Node]) -> bool {
    let maps_from: Vec<&str> = functions
        .iter()
        .filter_map(|n| match n.children.as_slice() {
            [f, from, _] if from.is_name() && *from.text == *set => Some(&*f.text),
            _ => None,
        })
        .collect();
    let mut applied = said
        .iter()
        .flat_map(|n| n.walk())
        .filter(|n| n.notation() == crate::notations::APPLICATION)
        .filter(
            |n| matches!(n.children.first(), Some(f) if maps_from.contains(&&*f.text)),
        )
        .peekable();
    if applied.peek().is_none() {
        return false;
    }
    let range_letters: std::collections::BTreeSet<String> = said
        .iter()
        .flat_map(|n| n.walk())
        .filter_map(|n| match n.children.as_slice() {
            [k, range, _] if range.notation() == crate::notations::INTEGER_RANGE => {
                k.is_name().then(|| k.text.to_string())
            }
            _ => None,
        })
        .collect();
    applied.all(|n| {
        matches!(n.children.as_slice(), [_, x] if x.is_name() && range_letters.contains(&*x.text))
    })
}
