//! Notation as data: patterns and precedence, read from the records.

use indexmap::{IndexMap, IndexSet};

use super::token::is_letter;
use crate::corpus::{Record, RecordKind};
use crate::outcome::{Built, Checked, Problem};
use crate::regex;

/// One piece of a pattern: a hole a term fills, or a literal token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Part {
    Hole,
    Lit(String),
}

impl Part {
    pub fn is_hole(&self) -> bool {
        matches!(self, Part::Hole)
    }

    pub fn literal(&self) -> Option<&str> {
        match self {
            Part::Lit(s) => Some(s),
            Part::Hole => None,
        }
    }
}

/// A notation's `wraps` line: the hole whose term the node puts inside
/// another notation, with that notation's name, literal and sort.
#[derive(Clone, Debug)]
pub struct Wrap {
    pub hole: usize,
    pub name: String,
    pub literal: String,
    pub yields: String,
}

/// A notation's `bounds` line: a binder written with a bound where its set
/// stands, "for all ε > 0". The name in hole 1 belongs to the set its
/// theorem declares for it (`Sorts::ranges`), and holes 1 to `to`, with the
/// tokens between them, are read as the condition. Without `join` the
/// condition takes a hole of its own after the set, as "for all ε ∈ ℝ with
/// ε > 0, …" has it; with one it is put in front of the body by that
/// notation, as "there is δ ∈ ℝ with δ > 0 and …" has it.
#[derive(Clone, Debug)]
pub struct Bounds {
    pub to: usize,
    pub join: Option<Wrap>,
}

/// A notation's `joins` line: two of its holes that the node it builds holds
/// as one, joined by another notation, as "for all x ∈ S with A, B" holds A
/// and B as "if A then B". The joined node stands in the first hole's place,
/// and the second hole is gone from the node.
#[derive(Clone, Debug)]
pub struct Join {
    pub first: usize,
    pub then: usize,
    pub by: Wrap,
}

/// A notation's `binds` line: the holes naming what a binder introduces, and
/// the holes where those names are its own, counted from 0.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binds {
    pub held: Vec<usize>,
    pub body: Vec<usize>,
}

/// One pattern of a notation record, ready to be matched.
#[derive(Clone, Debug)]
pub struct Notation {
    pub name: String,
    /// The pattern as its record writes it, `_ is a set`, for a message to
    /// quote.
    pub pattern: String,
    pub parts: Vec<Part>,
    /// The category each hole takes (`categories`).
    pub holes: Vec<String>,
    pub yields: String,
    pub level: String,
    pub assoc: Option<String>,
    pub binds: Option<Binds>,
    /// The notation this pattern is the negation under.
    pub folds: Option<String>,
    /// The tokens the node it builds stands for.
    pub literal: String,
    /// The record's name, or another it spells.
    pub stands_under: String,
    /// The literal of the notation that wraps it.
    pub fold_literal: String,
    /// Its `sort` field as written: the sort of each hole and of what it
    /// produces.
    pub sort: Option<String>,
    pub wrap: Option<Wrap>,
    /// For a pattern that spells another whose holes stand in another
    /// order, which of this pattern's holes, counted from 1, fills each hole
    /// of the node it builds (`places`).
    pub places: Option<Vec<usize>>,
    /// For a pattern that spells a binder once for each of several names,
    /// the (name, domain) holes of each binder, outermost first; the
    /// pattern's last hole is the innermost body (`nests`).
    pub nests: Option<Vec<(usize, usize)>>,
    pub bounds: Option<Bounds>,
    pub joins: Option<Join>,
}

impl Notation {
    /// What the node it builds binds, counted in that node's holes: a
    /// spelling that puts its holes in another notation's order (`places`)
    /// binds the same holes where they end up, so "x" in "f(x) ≠ B for all
    /// x ∈ A" is bound as it is in "for all x ∈ A, f(x) ≠ B".
    pub fn node_binds(&self) -> Option<Binds> {
        let binds = self.binds.as_ref()?;
        // Each node a nesting spelling builds has its name first, its
        // domain second and its body third, and binds the one over the other.
        if self.nests.is_some() {
            return Some(Binds {
                held: vec![0],
                body: vec![2],
            });
        }
        // A bounded spelling's node has its name, its set and then either the
        // condition and the body or the two joined, and binds the name over
        // what follows the set.
        if let Some(b) = &self.bounds {
            let after = match &b.join {
                Some(_) => 1,
                None => 1 + self.parts.iter().filter(|p| p.is_hole()).count() - b.to,
            };
            return Some(Binds {
                held: vec![0],
                body: (2..2 + after).collect(),
            });
        }
        if self.places.is_none() && self.joins.is_none() {
            return Some(binds.clone());
        }
        // A joined pair is one hole, where the first of the two stood.
        let at = |own: &usize| {
            let own = match &self.joins {
                Some(j) if own + 1 == j.then => j.first - 1,
                _ => *own,
            };
            match (&self.places, &self.joins) {
                (Some(places), _) => {
                    places.iter().position(|p| *p == own + 1).unwrap_or(own)
                }
                (None, Some(j)) if own > j.then - 1 => own - 1,
                _ => own,
            }
        };
        let mapped = |holes: &[usize]| {
            let mut out: Vec<usize> = Vec::new();
            for h in holes.iter().map(at) {
                if !out.contains(&h) {
                    out.push(h);
                }
            }
            out
        };
        Some(Binds {
            held: mapped(&binds.held),
            body: mapped(&binds.body),
        })
    }

    /// The name the node it builds carries.
    pub fn key(&self) -> &str {
        if self.stands_under.is_empty() {
            &self.name
        } else {
            &self.stands_under
        }
    }
}

regex!(
    NEGATES,
    r"pattern\s+(\d+)\s+is\s+(\S+)\s+of\s+pattern\s+(\d+)"
);
regex!(SPELLS, r"^\s*(\S+)\s+(\S+)");
// `wraps hole 2 in powerset`: the node built puts that hole's term inside
// the named notation, so `for all X ⊆ A` is `for all X ∈ 𝒫A` exactly.
regex!(WRAPS, r"^\s*hole\s+(\d+)\s+in\s+(\S+)\s*$");
// `joins hole 3 to hole 4 by conditional`: the node holds the two holes as
// one, that notation's node with them in its holes.
regex!(
    JOINS,
    r"^\s*hole\s+(\d+)\s+to\s+hole\s+(\d+)\s+by\s+(\S+)\s*$"
);
// `bounds hole 1 by hole 2, joined to hole 3 by conjunction`: the name in
// hole 1 ranges over its declared set, holes 1 to 2 are the condition, and
// the condition goes in front of hole 3 by the named notation.
regex!(
    BOUNDS,
    r"^\s*hole\s+1\s+by\s+hole\s+(\d+)(?:,\s*joined\s+to\s+hole\s+(\d+)\s+by\s+(\S+))?\s*$"
);
// `binds holes 1 and 3 over hole 5`: the holes naming what a binder
// introduces, and the holes where those names are its own.
const HOLE_LIST: &str = r"holes?\s+\d+(?:\s+and\s+\d+)*";
regex!(
    BINDS,
    format!(r"^\s*({HOLE_LIST})\s+over\s+(nothing|{HOLE_LIST})\s*$")
);
regex!(DIGIT_RUN, r"\d+");
regex!(WIDE_SPACE, r"\s{2,}");
regex!(PIECE, r"_|[^_\s]+");
regex!(BIT, r"[A-Za-zα-ωΑ-Ω]+|[^A-Za-zα-ωΑ-Ω]");

/// A notation's `binds` line, or None for a notation that binds nothing.
///
/// `there is _ ∈ _`, the nonempty set, binds over nothing: its name is
/// introduced and nothing is said of it.
fn binding(r: &Record) -> Checked<Option<Binds>> {
    let Some(said) = r.field("binds") else {
        return Ok(None);
    };
    let Some(m) = BINDS.captures(said) else {
        return Err(Problem::new(
            &r.path,
            r.lines.get("binds").copied().unwrap_or(r.line),
            format!(
                "notation {}: `binds {}` is not `hole N over hole M` or `hole N over nothing`",
                r.name,
                str::trim(said)
            ),
        ));
    };
    let holes = |g: &str| -> Vec<usize> {
        DIGIT_RUN
            .find_iter(g)
            .map(|d| d.as_str().parse::<usize>().unwrap() - 1)
            .collect()
    };
    Ok(Some(Binds {
        held: holes(&m[1]),
        body: holes(&m[2]),
    }))
}

/// What a notation record's holes take and what it yields, as the parser
/// reads them (`categories`). A `binds` line that does not read is a defect
/// the grammar reports when it is built; here it binds nothing.
pub fn categories_of(r: &Record) -> (Vec<String>, String) {
    let raw = str::trim(r.field_or_empty("pattern"));
    let binds = binding(r).ok().flatten();
    categories(r, raw, binds.as_ref())
}

/// The category each hole takes and the category the notation yields, read
/// off its `sort` field: the category of each sort (`Signature::categories`),
/// and `variable` for a hole its `binds` line says introduces a name.
///
/// A notation whose `sort` is missing or does not read is a defect
/// `check_notation` reports. Its holes, one per `_` of its first pattern,
/// then take any term and it yields any term, so that the rest of the
/// corpus is still read and every other defect still reported.
fn categories(r: &Record, raw: &str, binds: Option<&Binds>) -> (Vec<String>, String) {
    let said = r
        .field("sort")
        .map(|k| crate::sorts::infer::signature(str::trim(k)));
    let (mut holes, yields) = match said {
        Some(Built(sig)) => {
            let (holes, yields) = sig.categories();
            (
                holes.into_iter().map(String::from).collect::<Vec<_>>(),
                yields.to_string(),
            )
        }
        _ => {
            let count = patterns_of(raw)
                .first()
                .map_or(0, |p| p.matches('_').count());
            (vec!["any".to_string(); count], "any".to_string())
        }
    };
    if let Some(b) = binds {
        for &i in &b.held {
            if let Some(hole) = holes.get_mut(i) {
                *hole = "variable".to_string();
            }
        }
    }
    (holes, yields)
}

/// Split a pattern field into its patterns: two spaces or more between.
pub fn patterns_of(raw: &str) -> Vec<&str> {
    WIDE_SPACE.split(raw).collect()
}

/// Turn notation records into patterns the parser can match, with the
/// declared words and symbols, the symbols longest first.
pub fn compile_notations(
    records: &[Record],
) -> Checked<(Vec<Notation>, IndexSet<String>, Vec<String>)> {
    let mut out: Vec<Notation> = Vec::new();
    let mut words: IndexSet<String> = IndexSet::new();
    let mut symbols: IndexSet<String> = IndexSet::new();
    for r in records {
        if r.kind != RecordKind::Notation {
            continue;
        }
        let raw = str::trim(r.field_or_empty("pattern"));
        if raw.is_empty() {
            continue;
        }
        let levels: Vec<&str> = r
            .field_or_empty("level")
            .split(',')
            .map(str::trim)
            .collect();
        let assocs: Vec<&str> = r
            .field_or_empty("assoc")
            .split(',')
            .map(str::trim)
            .collect();
        // A record may declare that one of its patterns is the negation of
        // another. Both then build the same tree, so "n is not odd" and
        // "not (n is odd)" are one formula wherever two are compared.
        let folded = NEGATES.captures(r.field_or_empty("negates"));
        let spells = SPELLS.captures(r.field_or_empty("spells"));
        let wraps = WRAPS.captures(r.field_or_empty("wraps"));
        let places: Option<Vec<usize>> = r.field("places").map(|p| {
            p.split_whitespace()
                .filter_map(|n| n.parse::<usize>().ok())
                .collect()
        });
        let nests: Option<Vec<(usize, usize)>> = r.field("nests").map(|p| {
            p.split(',')
                .filter_map(|level| {
                    let holes: Vec<usize> = level
                        .split_whitespace()
                        .filter_map(|n| n.parse::<usize>().ok())
                        .collect();
                    match holes.as_slice() {
                        [name, domain] => Some((*name, *domain)),
                        _ => None,
                    }
                })
                .collect()
        });
        let bounds: Option<Bounds> = match r.field("bounds") {
            None => None,
            Some(said) => {
                let Some(m) = BOUNDS.captures(said) else {
                    return Err(Problem::new(
                        &r.path,
                        r.lines.get("bounds").copied().unwrap_or(r.line),
                        format!(
                            "notation {}: `bounds {}` is not `hole 1 by hole N`, with `, joined to hole M by <notation>` or without",
                            r.name,
                            str::trim(said)
                        ),
                    ));
                };
                Some(Bounds {
                    to: m[1].parse().unwrap(),
                    join: m.get(2).map(|hole| Wrap {
                        hole: hole.as_str().parse().unwrap(),
                        name: m[3].to_string(),
                        literal: String::new(),
                        yields: String::new(),
                    }),
                })
            }
        };
        let joins: Option<Join> = match r.field("joins") {
            None => None,
            Some(said) => {
                let Some(m) = JOINS.captures(said) else {
                    return Err(Problem::new(
                        &r.path,
                        r.lines.get("joins").copied().unwrap_or(r.line),
                        format!(
                            "notation {}: `joins {}` is not `hole N to hole M by <notation>`",
                            r.name,
                            str::trim(said)
                        ),
                    ));
                };
                Some(Join {
                    first: m[1].parse().unwrap(),
                    then: m[2].parse().unwrap(),
                    by: Wrap {
                        hole: m[1].parse().unwrap(),
                        name: m[3].to_string(),
                        literal: String::new(),
                        yields: String::new(),
                    },
                })
            }
        };
        let binds = binding(r)?;
        let (holes, yields) = categories(r, raw, binds.as_ref());
        let mut shapes: Vec<Vec<Part>> = Vec::new();
        for pat in patterns_of(raw) {
            let mut parts = Vec::new();
            for piece in PIECE.find_iter(pat) {
                let piece = piece.as_str();
                if piece == "_" {
                    parts.push(Part::Hole);
                    continue;
                }
                // A literal may run a word straight into a symbol, as `gcd(`
                // does. Split it, or the word is never declared and every use
                // of it falls back to single letters.
                for bit in BIT.find_iter(piece) {
                    let bit = bit.as_str();
                    parts.push(Part::Lit(bit.to_string()));
                    if bit.chars().all(is_letter) {
                        words.insert(bit.to_string());
                    } else if bit != "(" && bit != ")" {
                        symbols.insert(bit.to_string());
                    }
                }
            }
            shapes.push(parts);
        }
        // What a node is called and what stands in it: a record's name and the
        // literal of the pattern that matched. Both are needed, or `a < b` and
        // `a ≥ b` are one tree, since they are patterns of one record.
        //
        // A pattern that spells another builds the other's node, which is how
        // `2r` and `2·r` come out the same, and a pattern declared as the
        // negation of another carries that one's literal, so that the wrapping
        // in `not` is the only difference between the two spellings.
        let literal_of = |parts: &[Part]| -> String {
            parts.iter().filter_map(Part::literal).collect()
        };
        for (n, parts) in shapes.iter().enumerate() {
            let mut stands = literal_of(parts);
            let mut under = r.name.clone();
            let folds_here = folded
                .as_ref()
                .is_some_and(|f| f[1].parse::<usize>().ok() == Some(n + 1));
            if folds_here {
                let base: usize = folded.as_ref().unwrap()[3].parse().unwrap();
                stands = literal_of(&shapes[base - 1]);
            } else if let Some(sp) = &spells {
                under = sp[1].to_string();
                stands = sp[2].to_string();
            }
            let level = if n < levels.len() {
                levels[n]
            } else {
                levels[0]
            };
            let assoc = if n < assocs.len() {
                assocs[n]
            } else {
                assocs[0]
            };
            out.push(Notation {
                literal: stands,
                stands_under: under,
                name: r.name.clone(),
                pattern: patterns_of(raw)[n].to_string(),
                parts: parts.clone(),
                holes: holes.clone(),
                yields: yields.clone(),
                level: str::trim(level).to_string(),
                assoc: if assoc.is_empty() {
                    None
                } else {
                    Some(assoc.to_string())
                },
                binds: binds.clone(),
                folds: if folds_here {
                    Some(folded.as_ref().unwrap()[2].to_string())
                } else {
                    None
                },
                fold_literal: String::new(),
                sort: r.field("sort").map(String::from),
                wrap: wraps.as_ref().map(|w| Wrap {
                    hole: w[1].parse().unwrap(),
                    name: w[2].to_string(),
                    literal: String::new(),
                    yields: String::new(),
                }),
                places: places.clone(),
                nests: nests.clone(),
                bounds: bounds.clone(),
                joins: joins.clone(),
            });
        }
    }
    // A folded pattern builds the notation that wraps it, so it needs that
    // notation's literal too: `n is not odd` has to come out the same as
    // `not (n is odd)`, down to what stands in the outer node.
    let mut literals: IndexMap<String, String> = IndexMap::new();
    let mut yields: IndexMap<String, String> = IndexMap::new();
    for n in &out {
        literals
            .entry(n.key().to_string())
            .or_insert_with(|| n.literal.clone());
        yields
            .entry(n.key().to_string())
            .or_insert_with(|| n.yields.clone());
    }
    for n in &mut out {
        if let Some(folds) = &n.folds {
            n.fold_literal = literals.get(folds).cloned().unwrap_or_default();
        }
        // A wrapping notation's node carries its own literal and what it
        // yields, as it would parsed where it is written.
        if let Some(w) = &mut n.wrap {
            w.literal = literals.get(&w.name).cloned().unwrap_or_default();
            w.yields = yields.get(&w.name).cloned().unwrap_or_default();
        }
        let joining = n.joins.as_mut().map(|j| &mut j.by);
        let bounding = n.bounds.as_mut().and_then(|b| b.join.as_mut());
        for w in joining.into_iter().chain(bounding) {
            w.literal = literals.get(&w.name).cloned().unwrap_or_default();
            w.yields = yields.get(&w.name).cloned().unwrap_or_default();
        }
    }
    // A symbol may be a prefix of another, so try the longest first.
    let mut symbols: Vec<String> = symbols.into_iter().collect();
    symbols.sort_by(|a, b| {
        b.chars()
            .count()
            .cmp(&a.chars().count())
            .then_with(|| a.cmp(b))
    });
    Ok((out, words, symbols))
}

regex!(TIGHTER_THAN, r"^tighter than\s+(.*)");

/// The partial order. `tighter[a]` is everything a binds more tightly than,
/// closed under transitivity. Levels unrelated in either direction are
/// incomparable and an expression mixing them needs brackets.
pub fn compile_precedence(records: &[Record]) -> IndexMap<String, IndexSet<String>> {
    let mut direct: IndexMap<String, Vec<String>> = IndexMap::new();
    for r in records {
        if r.kind != RecordKind::Precedence {
            continue;
        }
        for (key, value) in &r.fields {
            if key == "note" {
                continue;
            }
            if let Some(m) = TIGHTER_THAN.captures(str::trim(value)) {
                direct.insert(
                    key.clone(),
                    m[1].split(',')
                        .map(|x| str::trim(x).trim_end_matches('.').to_string())
                        .collect(),
                );
            }
        }
    }
    let mut tighter = IndexMap::new();
    for start in direct.keys() {
        let mut seen: IndexSet<String> = IndexSet::new();
        let mut stack: Vec<String> = direct.get(start).cloned().unwrap_or_default();
        while let Some(lv) = stack.pop() {
            if seen.contains(&lv) {
                continue;
            }
            seen.insert(lv.clone());
            stack.extend(direct.get(&lv).cloned().unwrap_or_default());
        }
        tighter.insert(start.clone(), seen);
    }
    tighter
}

/// How two precedence levels stand to each other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tighter {
    Yes,
    No,
    Incomparable,
}

/// Whether a nests inside b.
pub fn binds_tighter(
    tighter: &IndexMap<String, IndexSet<String>>,
    a: &str,
    b: &str,
) -> Tighter {
    if a == b {
        return Tighter::Incomparable;
    }
    if tighter.get(a).is_some_and(|s| s.contains(b)) {
        return Tighter::Yes;
    }
    if tighter.get(b).is_some_and(|s| s.contains(a)) {
        return Tighter::No;
    }
    Tighter::Incomparable
}
