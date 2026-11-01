//! What each notation is in Lean: a notation record's `lean` field, read.
//!
//! The field has one entry for each of the record's patterns, in the order
//! of its `pattern` field, separated by ` ; ` since Lean text has commas in
//! it. An entry says what each hole takes, what the pattern yields, and the
//! Lean text with `_1`, `_2`, … for the holes:
//!
//! ```text
//! lean        α, α → α: _1 + _2 ; α, α → α: _1 - _2
//! lean        ℤ, ℤ → Prop: _1 ∣ _2
//! lean        α≥ℚ, α≥ℚ → α≥ℚ: _1 / _2
//! ```
//!
//! `α` is the number type a formula is computed in, the least of ℤ, ℚ, ℝ
//! and ℂ that holds every letter and operation in it (`LEAN.md`). `α≥ℚ`
//! is `α`, raised to at least ℚ: a quotient is never computed in ℤ, where
//! Lean's `/` rounds down. A fixed type, `ℤ` or `ℕ`, is one the hole is
//! always read at. `Prop` is a formula. An entry `-` is a pattern no tree
//! is built with, a negation the parser folds into another.
//!
//! This is Lean text, not page text: nothing here reads a formula.

use indexmap::IndexMap;

use crate::corpus::{Record, RecordKind};
use crate::outcome::{Checked, Problem};

/// A number type, in the order each holds the one before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Num {
    Nat,
    Int,
    Rat,
    Real,
    Complex,
}

impl Num {
    /// How Lean writes the type.
    pub fn lean(self) -> &'static str {
        match self {
            Num::Nat => "ℕ",
            Num::Int => "ℤ",
            Num::Rat => "ℚ",
            Num::Real => "ℝ",
            Num::Complex => "ℂ",
        }
    }

    fn read(text: &str) -> Option<Num> {
        match text {
            "ℕ" => Some(Num::Nat),
            "ℤ" => Some(Num::Int),
            "ℚ" => Some(Num::Rat),
            "ℝ" => Some(Num::Real),
            "ℂ" => Some(Num::Complex),
            _ => None,
        }
    }
}

/// What a hole takes, or a pattern yields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Slot {
    /// A number computed in the formula's type, raised to at least the
    /// given type.
    Alpha(Num),
    /// A number always read at this type.
    Fixed(Num),
    /// A formula.
    Prop,
}

impl Slot {
    fn read(text: &str) -> Option<Slot> {
        let text = text.trim();
        if text == "Prop" {
            return Some(Slot::Prop);
        }
        if text == "α" {
            return Some(Slot::Alpha(Num::Int));
        }
        if let Some(floor) = text.strip_prefix("α≥") {
            return Num::read(floor).map(Slot::Alpha);
        }
        Num::read(text).map(Slot::Fixed)
    }
}

/// One pattern in Lean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Template {
    pub holes: Vec<Slot>,
    pub yields: Slot,
    /// The Lean text, with `_1`, `_2`, … for the holes.
    pub text: String,
}

/// Every notation's patterns in Lean, by the record's name and the
/// pattern as its `pattern` field writes it.
#[derive(Clone, Debug, Default)]
pub struct Templates {
    by_pattern: IndexMap<(String, String), Template>,
    /// The notations with a `lean` field, by name.
    mapped: IndexMap<String, ()>,
    /// Each library function a definition record's `lean-builds` field
    /// gives a Lean form, by its name: `gcd(a, b)` is `Int.gcd a b`.
    functions: IndexMap<String, Template>,
}

impl Templates {
    /// The `lean` field of every notation record that has one.
    pub fn read(records: &[Record]) -> Checked<Templates> {
        let mut out = Templates::default();
        for r in records {
            if r.kind == RecordKind::Definition {
                if let Some(entry) = r.field("lean-builds") {
                    let line = r.lines.get("lean-builds").copied().unwrap_or(r.line);
                    let template = Template::read(entry.trim()).ok_or_else(|| {
                        Problem::new(
                            &r.path,
                            line,
                            format!(
                                "definition {}: lean-builds {entry:?} does not read",
                                r.name
                            ),
                        )
                    })?;
                    out.functions.insert(r.name.clone(), template);
                }
                continue;
            }
            if r.kind != RecordKind::Notation {
                continue;
            }
            let Some(field) = r.field("lean") else {
                continue;
            };
            let line = r.lines.get("lean").copied().unwrap_or(r.line);
            let patterns = patterns_of(r.field_or_empty("pattern"));
            let entries: Vec<&str> = field.split(" ; ").map(str::trim).collect();
            if entries.len() != patterns.len() {
                return Err(Problem::new(
                    &r.path,
                    line,
                    format!(
                        "notation {} has {} patterns and {} lean entries",
                        r.name,
                        patterns.len(),
                        entries.len()
                    ),
                ));
            }
            for (pattern, entry) in patterns.into_iter().zip(entries) {
                if entry == "-" {
                    continue;
                }
                let template = Template::read(entry).ok_or_else(|| {
                    Problem::new(
                        &r.path,
                        line,
                        format!(
                            "notation {}: lean entry {entry:?} does not read",
                            r.name
                        ),
                    )
                })?;
                out.by_pattern.insert((r.name.clone(), pattern), template);
            }
            out.mapped.insert(r.name.clone(), ());
        }
        Ok(out)
    }

    /// The template of a notation's pattern.
    pub fn get(&self, notation: &str, pattern: &str) -> Option<&Template> {
        self.by_pattern
            .get(&(notation.to_string(), pattern.to_string()))
    }

    /// Whether a notation has a `lean` field.
    pub fn maps(&self, notation: &str) -> bool {
        self.mapped.contains_key(notation)
    }

    /// The Lean form of a library function, by its name.
    pub fn function(&self, name: &str) -> Option<&Template> {
        self.functions.get(name)
    }
}

impl Template {
    /// One entry, `α, α → α: _1 + _2`; None where it does not read.
    fn read(entry: &str) -> Option<Template> {
        let (signature, text) = entry.split_once(": ")?;
        let (holes, yields) = signature.split_once('→')?;
        let holes = holes.trim();
        let holes = if holes.is_empty() {
            Vec::new()
        } else {
            holes
                .split(',')
                .map(Slot::read)
                .collect::<Option<Vec<Slot>>>()?
        };
        Some(Template {
            holes,
            yields: Slot::read(yields)?,
            text: text.trim().to_string(),
        })
    }
}

/// A `pattern` field's patterns, which two spaces or more set apart.
pub fn patterns_of(field: &str) -> Vec<String> {
    field
        .split("  ")
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(String::from)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_entry_reads_its_holes_and_text() {
        let t = Template::read("α≥ℚ, α≥ℚ → α≥ℚ: _1 / _2").unwrap();
        assert_eq!(t.holes, vec![Slot::Alpha(Num::Rat), Slot::Alpha(Num::Rat)]);
        assert_eq!(t.yields, Slot::Alpha(Num::Rat));
        assert_eq!(t.text, "_1 / _2");
        let d = Template::read("ℤ, ℤ → Prop: _1 ∣ _2").unwrap();
        assert_eq!(d.holes, vec![Slot::Fixed(Num::Int), Slot::Fixed(Num::Int)]);
        assert_eq!(d.yields, Slot::Prop);
        let pi = Template::read("→ α≥ℝ: Real.pi").unwrap();
        assert!(pi.holes.is_empty());
    }
}
