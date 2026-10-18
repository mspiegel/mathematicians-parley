//! A term or a proof written in reverse Polish, as the labels that build it.
//!
//! It is the tokens, each an interned symbol, shared: built by putting
//! token runs one after another, with nothing split or joined, and read as
//! text only where it is written out (`Display`). Two are equal where their
//! tokens are, and are ordered as their text is: tokens of printable
//! characters compare one by one as the joined text does, since a space
//! sorts below every character a token holds.

use std::fmt;
use std::rc::Rc;

use crate::formula::symbol::Symbol;

/// Labels in reverse Polish (the module's doc says how it compares). The
/// default is no labels.
#[derive(Clone, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Rpn(Rc<[Symbol]>);

impl Rpn {
    /// The tokens of text in reverse Polish, split where it has space.
    pub fn read(text: &str) -> Rpn {
        Rpn(text.split_whitespace().map(Symbol::of).collect())
    }

    /// The runs one after another.
    pub fn joined(parts: &[&[Symbol]]) -> Rpn {
        let mut out = Vec::with_capacity(parts.iter().map(|p| p.len()).sum());
        for part in parts {
            out.extend_from_slice(part);
        }
        Rpn(out.into())
    }

    pub fn tokens(&self) -> &[Symbol] {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The label applied last.
    pub fn last(&self) -> Option<Symbol> {
        self.0.last().copied()
    }

    /// The first label pushed.
    pub fn first(&self) -> Option<Symbol> {
        self.0.first().copied()
    }

    /// The one token, where there is one alone: a constant's label.
    pub fn alone(&self) -> Option<&'static str> {
        match *self.0 {
            [one] => Some(one.as_str()),
            _ => None,
        }
    }

    /// Whether some token is `label`.
    pub fn has(&self, label: &str) -> bool {
        self.0.iter().any(|t| *t == label)
    }

    /// Whether the last tokens are `ending`, in order.
    pub fn ends_with(&self, ending: &[&str]) -> bool {
        ending.len() <= self.0.len()
            && self.0[self.0.len() - ending.len()..]
                .iter()
                .zip(ending)
                .all(|(t, e)| *t == *e)
    }
}

/// What reverse Polish is put together from: tokens, one symbol, or text,
/// whose tokens are its words.
pub trait Spell {
    /// Its tokens, after what `out` holds.
    fn spell_onto(&self, out: &mut Vec<Symbol>);
}

impl Spell for Rpn {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        out.extend_from_slice(&self.0);
    }
}

impl Spell for Symbol {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        out.push(*self);
    }
}

impl Spell for str {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        out.extend(self.split_whitespace().map(Symbol::of));
    }
}

impl Spell for String {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        self.as_str().spell_onto(out);
    }
}

impl Spell for Rc<str> {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        (**self).spell_onto(out);
    }
}

impl<T: Spell + ?Sized> Spell for &T {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        (**self).spell_onto(out);
    }
}

impl Rpn {
    /// The parts' tokens one after another.
    pub fn of(parts: &[&dyn Spell]) -> Rpn {
        let mut out = Vec::new();
        for part in parts {
            part.spell_onto(&mut out);
        }
        Rpn(out.into())
    }

    /// One part's tokens.
    pub fn spelt(part: &(impl Spell + ?Sized)) -> Rpn {
        let mut out = Vec::new();
        part.spell_onto(&mut out);
        Rpn(out.into())
    }
}

impl From<&[Symbol]> for Rpn {
    fn from(tokens: &[Symbol]) -> Rpn {
        Rpn(tokens.into())
    }
}

impl From<Vec<Symbol>> for Rpn {
    fn from(tokens: Vec<Symbol>) -> Rpn {
        Rpn(tokens.into())
    }
}

impl fmt::Display for Rpn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (n, t) in self.0.iter().enumerate() {
            if n > 0 {
                f.write_str(" ")?;
            }
            f.write_str(t.as_str())?;
        }
        Ok(())
    }
}

impl fmt::Debug for Rpn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reverse_polish_is_ordered_as_its_text() {
        let texts = [
            "a",
            "a b",
            "ab",
            "a!",
            "a b c",
            "b",
            "cv vx",
            "vx cv",
            "c0 c1 caddc co",
            "c0 c1 caddc",
            "",
        ];
        for one in texts {
            for other in texts {
                assert_eq!(
                    Rpn::read(one).cmp(&Rpn::read(other)),
                    one.cmp(other),
                    "{one:?} against {other:?}"
                );
            }
        }
    }

    #[test]
    fn reverse_polish_reads_back_as_written() {
        let text = "vx cv cr wcel";
        assert_eq!(Rpn::read(text).to_string(), text);
        assert!(Rpn::read(text).ends_with(&["cr", "wcel"]));
        assert!(Rpn::read(text).has("cv"));
    }
}
