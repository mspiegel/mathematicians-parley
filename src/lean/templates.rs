//! What each notation is in Lean: a notation record's `lean-builds` field, read.
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

use crate::corpus::records::LEAN_BUILDS;
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
    /// Each notation's pattern's forms, by the record's name and the
    /// pattern: one, or one for each type its holes take, set apart by
    /// ` | ` in the field.
    by_pattern: IndexMap<(String, String), Vec<Template>>,
    /// The notations with a `lean-builds` field, by name.
    mapped: IndexMap<String, ()>,
    /// Each library function a definition record's `lean-builds` field
    /// gives a Lean form, by its name: `gcd(a, b)` is `Int.gcd a b`. A
    /// function Lean has at several types has one form for each, set apart
    /// by ` ; `: `ℝ → ℝ: Real.cos _1 ; ℂ → ℂ: Complex.cos _1`.
    functions: IndexMap<String, Vec<Template>>,
}

impl Templates {
    /// The `lean-builds` field of every notation record that has one.
    pub fn read(records: &[Record]) -> Checked<Templates> {
        let mut out = Templates::default();
        for r in records {
            if r.kind == RecordKind::Definition {
                if let Some(field) = r.field(LEAN_BUILDS) {
                    let line = r.lines.get(LEAN_BUILDS).copied().unwrap_or(r.line);
                    let mut forms = Vec::new();
                    for entry in field.split(" ; ").map(str::trim) {
                        let template = Template::read(entry).ok_or_else(|| {
                            Problem::new(
                                &r.path,
                                line,
                                format!(
                                    "definition {}: lean-builds {entry:?} does not read",
                                    r.name
                                ),
                            )
                        })?;
                        forms.push(template);
                    }
                    out.functions.insert(r.name.clone(), forms);
                }
                continue;
            }
            if r.kind != RecordKind::Notation {
                continue;
            }
            let Some(field) = r.lean_target() else {
                continue;
            };
            let line = r.lines.get(LEAN_BUILDS).copied().unwrap_or(r.line);
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
                let mut forms = Vec::new();
                for form in entry.split(" | ").map(str::trim) {
                    let template = Template::read(form).ok_or_else(|| {
                        Problem::new(
                            &r.path,
                            line,
                            format!(
                                "notation {}: lean entry {form:?} does not read",
                                r.name
                            ),
                        )
                    })?;
                    forms.push(template);
                }
                out.by_pattern.insert((r.name.clone(), pattern), forms);
            }
            out.mapped.insert(r.name.clone(), ());
        }
        Ok(out)
    }

    /// The template of a notation's pattern for terms of the types given:
    /// the form whose holes are of those types, else the first whose holes
    /// hold them, else the first (`pick`).
    pub fn get(
        &self,
        notation: &str,
        pattern: &str,
        args: &[Num],
    ) -> Option<&Template> {
        let forms = self
            .by_pattern
            .get(&(notation.to_string(), pattern.to_string()))?;
        pick(forms, args)
    }

    /// The holes of a pattern that every one of its forms reads at ℝ, the
    /// floor's, by place; empty where the pattern has no form.
    pub fn always_real(&self, notation: &str, pattern: &str) -> Vec<bool> {
        let Some(forms) = self
            .by_pattern
            .get(&(notation.to_string(), pattern.to_string()))
        else {
            return Vec::new();
        };
        let width = forms.iter().map(|t| t.holes.len()).max().unwrap_or(0);
        (0..width)
            .map(|i| {
                forms
                    .iter()
                    .all(|t| t.holes.get(i) == Some(&Slot::Fixed(Num::Real)))
            })
            .collect()
    }

    /// Whether a notation has a `lean-builds` field.
    pub fn maps(&self, notation: &str) -> bool {
        self.mapped.contains_key(notation)
    }

    /// The Lean form of a library function, by its name: its first, where
    /// it has one for each of several types.
    pub fn function(&self, name: &str) -> Option<&Template> {
        self.functions.get(name).and_then(|forms| forms.first())
    }

    /// The Lean form of a library function applied to arguments of the
    /// types given: the first whose holes hold them, a number of a type
    /// held in each fixed hole's type; else the first.
    pub fn function_at(&self, name: &str, args: &[Num]) -> Option<&Template> {
        let forms = self.functions.get(name)?;
        let holds = |t: &Template| {
            t.holes.len() == args.len()
                && t.holes.iter().zip(args).all(|(slot, arg)| match slot {
                    Slot::Fixed(n) => arg <= n,
                    _ => true,
                })
        };
        forms.iter().find(|t| holds(t)).or(forms.first())
    }
}

/// Of a pattern's forms, the one for terms of these types: the form whose
/// fixed holes are of exactly their types, so that |x| of a complex number
/// takes `‖x‖` though `α → α: abs _1` would hold it too; else the first
/// whose holes hold them, a number held in a fixed hole of a wider type;
/// else the first.
fn pick<'t>(forms: &'t [Template], args: &[Num]) -> Option<&'t Template> {
    let fits = |t: &Template, exact: bool| {
        t.holes.len() == args.len()
            && t.holes.iter().zip(args).all(|(slot, arg)| match slot {
                Slot::Fixed(n) if exact => arg == n,
                Slot::Fixed(n) => arg <= n,
                _ => !exact,
            })
    };
    forms
        .iter()
        .find(|t| forms.len() > 1 && fits(t, true))
        .or_else(|| forms.iter().find(|t| fits(t, false)))
        .or(forms.first())
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
