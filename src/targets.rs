//! Where the readable layer's words land in set.mm.
//!
//! `corpus/db/notation.records` carries a `metamath-builds` field, the term a
//! pattern builds, and the `corpus/stdlib/*.records` files a `metamath-proof`
//! field, the lemmas an item is proved with, and this reads them
//! (`Record::metamath_target`).
//!
//! Which set.mm lemmas an elaborator may lean on for what the readable layer
//! never writes is not a database field either; `rules` holds it.

use indexmap::IndexMap;

use crate::corpus::records::LemmaReading;
use crate::corpus::{Record, RecordKind};
use crate::formula::symbol::Symbol;
use crate::mm::{Rpn, Spell};
use crate::regex;
use crate::rules::PAIRS_EXCHANGED;

regex!(HOLE, r"_(\d+)");
regex!(HOLE_WHOLE, r"^_(\d+)$");
// `any order of holes 1 and 2`, a `commutes` entry naming two holes.
regex!(ANY_ORDER_OF, r"^any order of holes (\d+) and (\d+)$");
// A part of a structure a `let` line introduced, which a target takes from
// there: `@op` is the operation of the group the theorem lets, so `g·h` is
// `g h ( +g ` W ) co` for that group's W, which nothing on the page names.
regex!(CONTEXT_WHOLE, r"^@[a-z]+$");
regex!(CONTEXT, r"@[a-z]+");

pub const FOLDED: &str = "folded";

/// What a `metamath-builds` may say that is not a template: that a pattern
/// builds another notation's tree. `DATABASE.md` documents it.
pub fn is_marker(entry: &str) -> bool {
    entry == FOLDED
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

/// The entries of a `metamath-builds` field, one per pattern, or of a
/// `metamath-proof` field, one per `then` group.
pub fn split_entries(value: &str) -> Vec<&str> {
    value
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .collect()
}

/// Where a Metamath bridge's full name begins.
pub const METAMATH_BRIDGES: &str = "metamath-bridges/";

/// The label one entry of a `metamath-proof` names. A set.mm label is
/// written bare; a bridge is written by its full name,
/// `metamath-bridges/numbers/gzmodlt`, and is the lemma its last part
/// names, which `tools::labels` checks that group holds.
pub fn label_of(entry: &str) -> &str {
    match entry.strip_prefix(METAMATH_BRIDGES) {
        Some(rest) => rest.rsplit_once('/').map_or(rest, |(_, label)| label),
        None => entry,
    }
}

/// The entries of a `metamath-proof` field, each the label it names.
pub fn lemma_entries(value: &str) -> Vec<&str> {
    split_entries(value).into_iter().map(label_of).collect()
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
        let Some(target) = r.metamath_target() else {
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
/// from the `then` line (`metamath-reads` says `turned`).
pub fn unfolding(record: &Record) -> (Option<String>, bool) {
    let Some(value) = record.metamath_target().filter(|v| !v.is_empty()) else {
        return (None, false);
    };
    let entries = lemma_entries(value);
    let turned = record
        .metamath_reads()
        .is_ok_and(|readings| readings.first().is_some_and(|r| r.turned));
    (entries.first().map(|e| e.to_string()), turned)
}

/// The set.mm theorem an item corresponds to, and what fills it.
///
/// A readable theorem and the lemma that supplies it are stated in
/// different variables, and nothing derives the correspondence: an item that
/// is double negation has its `ph` be what the readable statement calls `n
/// is even`. So the item says it, as `notnot with ph := n is even`, and each
/// right-hand side is a formula in the item's own names.
pub fn lemma(record: &Record) -> (Option<String>, IndexMap<String, String>) {
    let value = record.metamath_target().filter(|v| !v.is_empty());
    let Some(value) = value else {
        return (None, IndexMap::new());
    };
    let labels = |head: &str| lemma_entries(head).join(", ");
    let Some((head, rest)) = value.split_once(" with ") else {
        return (Some(labels(value)), IndexMap::new());
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
    (Some(labels(head)), fills)
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
    /// `any order of holes 1 and 2`: those two holes, counted from 0 here,
    /// stand in no order and the rest where they are written, so a ≡ b
    /// (mod n) and b ≡ a (mod n) are one claim.
    AnyOrderOf(usize, usize),
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
            _ => {
                let m = ANY_ORDER_OF.captures(entry)?;
                let hole = |at: usize| m[at].parse::<usize>().ok().filter(|&h| h >= 1);
                let (i, j) = (hole(1)?, hole(2)?);
                (i != j).then_some(Commutes::AnyOrderOf(i - 1, j - 1))
            }
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
    r.field("commutes")
        .map(split_entries)
        .unwrap_or_default()
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
        let patterns = r.metamath_target().map(split_entries).unwrap_or_default();
        for (pattern, said) in patterns.iter().zip(says.iter()) {
            let places = slots(pattern);
            // A target whose two holes a lemma exchanges deeper than one
            // constructor, |PQ| inside a difference, is a pair in no order
            // (`pairs_in_any_order`), not one constructor's two children.
            let paired = PAIRS_EXCHANGED.iter().any(|(t, _)| t == pattern);
            if !said.is_some_and(Commutes::exchanges)
                || *pattern == FOLDED
                || places.len() != 2
                || paired
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

/// Two holes of a notation's target that stand in no order, from `commutes
/// any order of holes 1 and 2`: the target, the two holes counted from 1 as
/// the target writes them, how many holes it has, and the lemma that
/// exchanges them (`rules::PAIRS_EXCHANGED`).
#[derive(Clone, Debug)]
pub struct PairInAnyOrder {
    pub target: String,
    pub holes: (usize, usize),
    pub count: usize,
    pub lemma: &'static str,
}

/// Each `commutes any order of holes I and J` entry whose target has an
/// exchanging lemma.
pub fn pairs_in_any_order(records: &[Record]) -> Vec<PairInAnyOrder> {
    let mut out = Vec::new();
    for r in records.iter().filter(|r| r.kind == RecordKind::Notation) {
        let patterns = r.metamath_target().map(split_entries).unwrap_or_default();
        for (pattern, said) in patterns.iter().zip(commutes_said(r)) {
            // Two holes in no order, named or the only two the target has.
            let (i, j) = match said {
                Some(Commutes::AnyOrderOf(i, j)) => (i, j),
                Some(Commutes::AnyOrder) if slots(pattern).len() == 2 => (0, 1),
                _ => continue,
            };
            let Some((_, lemma)) = PAIRS_EXCHANGED.iter().find(|(t, _)| t == pattern)
            else {
                continue;
            };
            out.push(PairInAnyOrder {
                target: pattern.to_string(),
                holes: (i + 1, j + 1),
                count: slots(pattern).len(),
                lemma,
            });
        }
    }
    out
}

/// An identity element a notation record declares for one of its patterns,
/// `0 on the right`: the one table of them, which the checker keys by the
/// pattern's page spelling and the elaborator by its set.mm constructor. A
/// law is named by its notation and `pattern`, so what the checker records
/// dropping names the law the elaborator applies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityLaw {
    /// The notation record's name, `additive`.
    pub notation: String,
    /// The pattern, by its place in the record's lists: its `identity`
    /// entries, its targets and the notation's spellings stand in one order.
    pub pattern: usize,
    pub element: u32,
    /// The holes the element may stand in, 0 for the first.
    pub holes: Vec<usize>,
}

/// Every identity law the notation records declare (`IdentityLaw`), one
/// per pattern whose `identity` entry names one.
pub fn identity_laws(records: &[Record]) -> Vec<IdentityLaw> {
    let mut out = Vec::new();
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let Some(says) = r.field("identity") else {
            continue;
        };
        for (pattern, said) in split_entries(says).iter().enumerate() {
            let Some((element, holes)) = identity_said(said) else {
                continue;
            };
            out.push(IdentityLaw {
                notation: r.name.clone(),
                pattern,
                element,
                holes,
            });
        }
    }
    out
}

/// An operation's identity element as set.mm writes it: the law
/// (`IdentityLaw`), the constructor, the positions its two holes occupy, and
/// what stands in every other position.
#[derive(Clone, Debug)]
pub struct Identity {
    pub law: IdentityLaw,
    pub constructor: String,
    pub places: (usize, usize),
    pub fixed: IndexMap<usize, String>,
}

/// The identity laws (`identity_laws`) with their set.mm form, each read
/// from its pattern's target; a law whose target is folded or has other
/// than two holes is left out.
pub fn identities(records: &[Record]) -> Vec<Identity> {
    let mut out = Vec::new();
    for law in identity_laws(records) {
        let Some(record) = records
            .iter()
            .find(|r| r.kind == RecordKind::Notation && r.name == law.notation)
        else {
            continue;
        };
        let patterns = record
            .metamath_target()
            .map(split_entries)
            .unwrap_or_default();
        let Some(pattern) = patterns.get(law.pattern) else {
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
            law,
        });
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

/// The lemmas an item's `metamath-proof` names, one per `then` group.
///
/// An item may state several things at once — that a sum and a difference
/// are both real — and set.mm proves each separately, so a step citing the
/// item claims one of them.
///
/// What stands before `with` is still a list, and the filling serves every
/// lemma in it. What stands after it is the filling and not a list, however
/// many commas it takes.
pub fn clauses(record: &Record) -> Vec<String> {
    let Some(value) = record.metamath_target().filter(|v| !v.is_empty()) else {
        return Vec::new();
    };
    let listed = if value.contains(" with ") {
        lemma(record).0.unwrap_or_default()
    } else {
        value.to_string()
    };
    lemma_entries(&listed)
        .into_iter()
        .map(String::from)
        .collect()
}

/// The lemmas one `then` sentence of an item is read off, and how
/// (`metamath-reads`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SentenceLemma {
    /// The lemma, as `clauses` names it; for a witness, every lemma, each
    /// giving one part of what the sentence says of it.
    pub labels: Vec<String>,
    pub reading: LemmaReading,
}

/// The lemmas each `then` sentence of an item is read off, in order, with how
/// it is read (`Record::metamath_reads`). Each sentence takes the next lemma
/// `clauses` names, but one that is the next part of the same lemma as the
/// sentence before it (`LemmaReading::continues`): `gcd-integer`'s `as
/// stated, part 1, part 2` reads gcdcl, then gcddvds twice. A witness, the
/// item's one sentence, takes every lemma. Empty for an item with no
/// target; Err with what is wrong where the readings take more or fewer
/// lemmas than the target names.
pub fn sentence_lemmas(record: &Record) -> Result<Vec<SentenceLemma>, String> {
    let labels = clauses(record);
    if labels.is_empty() {
        return Ok(Vec::new());
    }
    let readings = record.metamath_reads()?;
    if let [reading] = readings.as_slice() {
        if reading.witness {
            return Ok(vec![SentenceLemma {
                labels,
                reading: *reading,
            }]);
        }
    }
    if readings.iter().any(|r| r.witness) {
        return Err(
            "a witness is the item's one sentence, and takes every lemma its metamath-proof names"
                .to_string(),
        );
    }
    let mut out: Vec<SentenceLemma> = Vec::new();
    let mut next = labels.iter();
    for (i, reading) in readings.iter().enumerate() {
        let labels = match out.last() {
            Some(before) if i > 0 && reading.continues(&readings[i - 1]) => {
                before.labels.clone()
            }
            _ => match next.next() {
                Some(label) => vec![label.clone()],
                None => {
                    return Err(format!(
                        "its {} sentences take more lemmas than its metamath-proof names, {}: a sentence that is a further part of the lemma before it says so in `metamath-reads`",
                        readings.len(),
                        labels.join(", ")
                    ))
                }
            },
        };
        out.push(SentenceLemma {
            labels,
            reading: *reading,
        });
    }
    if next.next().is_some() {
        return Err(format!(
            "its {} sentences take fewer lemmas than its metamath-proof names, {}",
            readings.len(),
            labels.join(", ")
        ));
    }
    Ok(out)
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
