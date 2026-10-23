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
use crate::formula::symbol::Symbol;
use crate::mm::{Rpn, Spell};
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

/// The parts of a group a target may take, each with the set.mm label of
/// the slot it is (`@op` is `+g` of the group the theorem lets): what a
/// group's `let` line gives.
pub const GROUP_PARTS: &[(&str, &str)] = &[
    ("@op", "cplusg"),
    ("@inv", "cminusg"),
    ("@subgroups", "csubg"),
    ("@lsm", "clsm"),
];

/// The parts of a graph a target may take, as `GROUP_PARTS`: what a
/// graph's `let` line gives.
pub const GRAPH_PARTS: &[(&str, &str)] = &[("@ends", "ciedg"), ("@deg", "cvtxdg")];

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

/// What a notation's `commutes` field says of one pattern's holes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Commutes {
    /// `yes`: the two holes may be exchanged, so 2k and k · 2 are one
    /// number, though the kernel writes them apart.
    Exchanged,
    /// `any order`: the holes stand in no order on the page, so {u, w} and
    /// {w, u} are one set.
    AnyOrder,
    /// `no`: the holes stand where they are written.
    Kept,
}

impl Commutes {
    /// One entry of the field read; None for a word that is none of the
    /// three, which `checker::database` reports.
    pub fn of(entry: &str) -> Option<Commutes> {
        match entry {
            "yes" => Some(Commutes::Exchanged),
            "any order" => Some(Commutes::AnyOrder),
            "no" => Some(Commutes::Kept),
            _ => None,
        }
    }

    /// Whether two holes may stand either way round: a pattern of two
    /// holes in no order is one whose two may be exchanged.
    pub fn exchanges(self) -> bool {
        matches!(self, Commutes::Exchanged | Commutes::AnyOrder)
    }
}

/// A notation record's `commutes` field read, one entry per pattern in the
/// order the patterns are written; empty where the record has none.
pub fn commutes_said(r: &Record) -> Vec<Option<Commutes>> {
    split_entries(r.field_or_empty("commutes"))
        .into_iter()
        .map(Commutes::of)
        .collect()
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
        let says = commutes_said(r);
        let patterns = split_entries(r.field_or_empty("target"));
        for (pattern, said) in patterns.iter().zip(says.iter()) {
            let places = slots(pattern);
            if !said.is_some_and(Commutes::exchanges)
                || *pattern == FOLDED
                || places.len() != 2
            {
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

/// An operation's identity element, from `identity`: the constructor, the
/// positions its two holes occupy, what stands in every other position, the
/// element, and which of the two holes it may stand in, 0 for the first.
#[derive(Clone, Debug)]
pub struct Identity {
    pub constructor: String,
    pub places: (usize, usize),
    pub fixed: IndexMap<usize, String>,
    pub element: u32,
    pub holes: Vec<usize>,
}

/// The identity elements the notation records declare, one entry per
/// pattern that has one: `0 on either side`, `0 on the right`.
pub fn identities(records: &[Record]) -> Vec<Identity> {
    let mut out = Vec::new();
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let Some(says) = r.field("identity") else {
            continue;
        };
        let says = split_entries(says);
        let patterns = split_entries(r.field_or_empty("target"));
        for (pattern, said) in patterns.iter().zip(says.iter()) {
            let Some(law) = identity_said(said) else {
                continue;
            };
            let places = slots(pattern);
            if *pattern == FOLDED || places.len() != 2 {
                continue;
            }
            let tokens: Vec<&str> = pattern.split_whitespace().collect();
            let fixed = tokens[..tokens.len() - 1]
                .iter()
                .enumerate()
                .filter(|(i, _)| !places.values().any(|p| p == i))
                .map(|(i, t)| (i, t.to_string()))
                .collect();
            out.push(Identity {
                constructor: tokens[tokens.len() - 1].to_string(),
                places: (places[&0], places[&1]),
                fixed,
                element: law.0,
                holes: law.1,
            });
        }
    }
    out
}

/// An `identity` entry read: the element, and the holes it may stand in.
/// None for `none`, and for anything the field does not say.
pub fn identity_said(said: &str) -> Option<(u32, Vec<usize>)> {
    let (element, side) = said.split_once(" on ")?;
    let element = element.trim().parse::<u32>().ok()?;
    let holes = match side.trim() {
        "either side" => vec![0, 1],
        "the left" => vec![0],
        "the right" => vec![1],
        _ => return None,
    };
    Some((element, holes))
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

/// A target with each hole, a token `_1` of its own, replaced by the term
/// filling it.
pub fn fill(pattern: &str, holes: &[Rpn]) -> Rpn {
    let mut out = Vec::new();
    for token in pattern.split_whitespace() {
        match HOLE_WHOLE.captures(token) {
            Some(hole) => {
                let n: usize = hole[1].parse().unwrap();
                holes[n - 1].spell_onto(&mut out);
            }
            None => out.push(Symbol::of(token)),
        }
    }
    Rpn::from(out)
}

/// A repeating notation's target for a node of `count` children: its own
/// target, which takes the holes the pattern writes, and then, for each
/// child after those, `building` with that child's hole in place of `_`:
/// `_1 _2 _3 ctp _4 csn cun` and `_5 csn cun` for {a, b, c, d, e}. `_′` is
/// the hole of the child before, as a chain's link joins each term to the
/// one before it: `_3 _4 wceq wa` for the fourth term of a = b = c = d.
pub fn repeated(target: &str, building: &str, written: usize, count: usize) -> String {
    let mut out = target.to_string();
    for k in written + 1..=count {
        for token in building.split_whitespace() {
            out.push(' ');
            match token {
                "_" => out.push_str(&format!("_{k}")),
                "_′" => out.push_str(&format!("_{}", k - 1)),
                _ => out.push_str(token),
            }
        }
    }
    out
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
