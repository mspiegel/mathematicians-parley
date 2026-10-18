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

/// Labels in reverse Polish (the module's doc says how it compares).
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
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
