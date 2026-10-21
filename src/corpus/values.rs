//! The values a citation gives the letters of what it cites, `v := t`.
//!
//! The letter on the left is the cited item's own, and the value on the
//! right is written in the citing proof's names, as they stand before any
//! value is given: `a := b/k, b := a/k` swaps the two, and `n := d, d := a`
//! puts the proof's d at n. So the values are read together or not at all.
//! The skeleton reader cuts them out of a line once (`skeleton::cut`), and
//! this keeps their text to itself: what leaves this module is every value
//! read with one grammar and one set of sorts, or the tokens they are
//! written in, never one value's text for a tool to read after giving
//! another.

use crate::formula::page::{tokens, Written};
use crate::formula::token::Token;
use crate::formula::{fits, wanted_reading, Grammar, Node, Sorts};
use crate::outcome::Checked;

/// The `v := t` a line writes, in order, as the skeleton reader cut them.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Values {
    given: Vec<Given>,
}

/// One `v := t`: the cited item's letter, and the value as the line writes
/// it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Given {
    pub name: String,
    pub value: Written,
}

/// One value read: the cited item's letter, and the tree the proof's text
/// for it reads as.
#[derive(Clone, Debug)]
pub struct Value {
    pub name: String,
    pub value: Node,
    /// The value as written, for a message.
    pub shown: String,
}

impl Values {
    /// No values at all.
    pub const NONE: Values = Values { given: Vec::new() };

    /// The values the skeleton reader cut out of a justification
    /// (`skeleton::Slots::values`).
    pub(crate) fn of(given: &[Given]) -> Values {
        Values {
            given: given.to_vec(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.given.is_empty()
    }

    /// Each value as written, in order.
    pub fn written(&self) -> impl Iterator<Item = &Written> {
        self.given.iter().map(|g| &g.value)
    }

    /// The cited item's letters the values are given for, in order.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.given.iter().map(|g| g.name.as_str())
    }

    /// Every value, each read as one formula with the same grammar and
    /// sorts; a defect where one is not a formula that reads.
    pub fn read(&self, g: &Grammar, sorts: &Sorts) -> Checked<Vec<Value>> {
        self.given
            .iter()
            .map(|given| {
                Ok(Value {
                    name: given.name.clone(),
                    value: given.value.formula()?.read(g, sorts)?,
                    shown: given.value.text().to_string(),
                })
            })
            .collect()
    }

    /// `read`, each value as the place its letter stands in the cited item
    /// wants it (`formula::wanted_reading`): `U := (0, 1)`, where the item
    /// says U is a set, is the open interval. `letters` are the cited item's
    /// sorts, None where the item is not known.
    pub fn read_wanted(
        &self,
        g: &Grammar,
        sorts: &Sorts,
        letters: Option<&Sorts>,
    ) -> Checked<Vec<Value>> {
        let mut read = self.read(g, sorts)?;
        let Some(letters) = letters else {
            return Ok(read);
        };
        for v in &mut read {
            let Some(want) = letters.get(&v.name).and_then(|s| s.name()) else {
                continue;
            };
            if !fits(want, &v.value.sort) {
                if let Some(wanted) = wanted_reading(g, &v.value, want) {
                    v.value = wanted;
                }
            }
        }
        Ok(read)
    }

    /// The tokens each value is written in, for a question about how the
    /// theorem is written, which names it writes (`sorts::written_tokens`);
    /// a value that does not lex is left out, as the elaborator reports a
    /// value that does not read.
    pub fn tokens(&self, g: &Grammar) -> Vec<Vec<Token>> {
        self.given
            .iter()
            .filter_map(|given| tokens(&given.value, g).ok())
            .collect()
    }
}
