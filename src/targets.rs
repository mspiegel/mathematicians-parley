//! Where the readable layer's words land in set.mm.
//!
//! `corpus/db/notation.records` and the `corpus/stdlib/*.records` files carry a `target`
//! field beside `metamath`, and this reads it. `metamath` says in words
//! which set.mm construct a pattern or an item corresponds to, which is what
//! a person checking the database wants; `target` says the same thing as a
//! term, which is what a program needs. Neither is derivable from the other,
//! so both are written.
//!
//! Which set.mm lemmas an elaborator may lean on for what the readable layer
//! never writes is not a database field either; `rules` holds it.

use indexmap::IndexMap;

use crate::corpus::{Record, RecordKind};
use crate::regex;

regex!(HOLE, r"_(\d+)");
regex!(HOLE_WHOLE, r"^_(\d+)$");
// A part of a structure a `let` line introduced, which a target takes from
// there: `@op` is the operation of the group the theorem lets, so `g·h` is
// `g h ( +g ` W ) co` for that group's W, which nothing on the page names.
regex!(CONTEXT_WHOLE, r"^@[a-z]+$");
regex!(CONTEXT, r"@[a-z]+");

pub const FOLDED: &str = "folded";
pub const REVERSED: &str = "equation reversed";

/// What a `target` may say that is not a lemma: that a pattern builds
/// another notation's tree, and that the lemma writes its equation the other
/// way round from the `then` line. `DATABASE.md` documents both.
pub fn is_marker(entry: &str) -> bool {
    entry == FOLDED || entry == REVERSED
}

/// Whether a token is a hole, `_1`.
pub fn is_hole(token: &str) -> bool {
    HOLE_WHOLE.is_match(token)
}

/// Whether a token takes a part of a structure a `let` line introduced.
pub fn is_context(token: &str) -> bool {
    CONTEXT_WHOLE.is_match(token)
}

/// The context tokens a target takes, as written.
pub fn contexts(pattern: &str) -> Vec<&str> {
    CONTEXT.find_iter(pattern).map(|m| m.as_str()).collect()
}

/// The entries of a `target` field, one per pattern.
pub fn split_entries(value: &str) -> Vec<&str> {
    value
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .collect()
}

/// For each notation, the term each of its patterns builds.
///
/// A folded pattern builds another notation's tree, so it has no entry of
/// its own and is recorded as None.
pub fn terms(records: &[Record]) -> IndexMap<String, Vec<Option<String>>> {
    let mut out = IndexMap::new();
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let Some(target) = r.field("target") else {
            continue;
        };
        out.insert(
            r.name.clone(),
            split_entries(target)
                .into_iter()
                .map(|e| {
                    if e == FOLDED {
                        None
                    } else {
                        Some(e.to_string())
                    }
                })
                .collect(),
        );
    }
    out
}

/// The theorem that unfolds a definition, and whether it faces the other way
/// from the `then` line.
pub fn unfolding(record: &Record) -> (Option<String>, bool) {
    let Some(value) = record.field("target").filter(|v| !v.is_empty()) else {
        return (None, false);
    };
    let entries = split_entries(value);
    let reversed = entries.iter().skip(1).any(|e| e.contains("reversed"));
    (entries.first().map(|e| e.to_string()), reversed)
}

/// The set.mm theorem an item corresponds to, and what fills it.
///
/// A readable theorem and the lemma that supplies it are stated in
/// different variables, and nothing derives the correspondence: an item that
/// is double negation has its `ph` be what the readable statement calls `n
/// is even`. So the item says it, as `notnot with ph := n is even`, and each
/// right-hand side is a formula in the item's own names.
pub fn lemma(record: &Record) -> (Option<String>, IndexMap<String, String>) {
    let value = record.field("target").filter(|v| !v.is_empty());
    let Some(value) = value else {
        return (None, IndexMap::new());
    };
    let Some((head, rest)) = value.split_once(" with ") else {
        return (Some(str::trim(value).to_string()), IndexMap::new());
    };
    let mut fills = IndexMap::new();
    for piece in split_entries(rest) {
        if let Some((name, formula)) = piece.split_once(":=") {
            if !formula.is_empty() {
                fills.insert(
                    str::trim(name).to_string(),
                    str::trim(formula).to_string(),
                );
            }
        }
    }
    (Some(str::trim(head).to_string()), fills)
}

/// A pair of exchangeable operands: the constructor, the two positions the
/// holes occupy, and what stands in every other position.
#[derive(Clone, Debug)]
pub struct Commuting {
    pub constructor: String,
    pub places: (usize, usize),
    pub fixed: IndexMap<usize, String>,
}

/// The terms whose two operands may be exchanged, from `commutes`.
///
/// Each entry is the constructor, the two positions the holes occupy, and
/// what stands in every other position: the product is `co` with holes at 0
/// and 1 and `cmul` at 2. The positions are read off the target, so nothing
/// here assumes where a constructor keeps its operator.
pub fn commuting(records: &[Record]) -> Vec<Commuting> {
    let mut out = Vec::new();
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let Some(commutes) = r.field("commutes") else {
            continue;
        };
        let says = split_entries(commutes);
        let patterns = split_entries(r.field_or_empty("target"));
        for (pattern, yes) in patterns.iter().zip(says.iter()) {
            let places = slots(pattern);
            if *yes != "yes" || *pattern == FOLDED || places.len() != 2 {
                continue;
            }
            let tokens: Vec<&str> = pattern.split_whitespace().collect();
            let mut sorted: Vec<usize> = places.values().copied().collect();
            sorted.sort();
            let fixed = tokens[..tokens.len() - 1]
                .iter()
                .enumerate()
                .filter(|(i, _)| !places.values().any(|p| p == i))
                .map(|(i, t)| (i, t.to_string()))
                .collect();
            out.push(Commuting {
                constructor: tokens[tokens.len() - 1].to_string(),
                places: (sorted[0], sorted[1]),
                fixed,
            });
        }
    }
    out
}

/// The lemmas an item's `target` names, one per `then` group.
///
/// An item may state several things at once — that a sum and a difference
/// are both real — and set.mm proves each separately, so a step citing the
/// item claims one of them.
///
/// What stands before `with` is still a list, and the filling serves every
/// lemma in it. What stands after it is the filling and not a list, however
/// many commas it takes.
pub fn clauses(record: &Record) -> Vec<String> {
    let Some(value) = record.field("target").filter(|v| !v.is_empty()) else {
        return Vec::new();
    };
    let listed = if value.contains(" with ") {
        lemma(record).0.unwrap_or_default()
    } else {
        value.to_string()
    };
    // `equation reversed` says how the lemmas write their equation, and is
    // not one of them: a route that reached it would ask set.mm for a label
    // it does not have.
    split_entries(&listed)
        .into_iter()
        .filter(|e| !is_marker(e))
        .map(String::from)
        .collect()
}

/// A target with its holes replaced by the terms filling them.
pub fn fill(pattern: &str, holes: &[String]) -> String {
    HOLE.replace_all(pattern, |c: &regex::Captures| {
        let n: usize = c[1].parse().unwrap();
        holes[n - 1].clone()
    })
    .into_owned()
}

/// Which operand position each hole occupies, by hole number from 0.
pub fn slots(pattern: &str) -> IndexMap<usize, usize> {
    let mut places = IndexMap::new();
    for (i, token) in pattern.split_whitespace().enumerate() {
        if let Some(found) = HOLE.captures(token) {
            if found.get(0).unwrap().start() == 0 {
                places.insert(found[1].parse::<usize>().unwrap() - 1, i);
            }
        }
    }
    places
}
