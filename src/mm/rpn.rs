//! A term or a proof written in reverse Polish, as the labels that build it.
//!
//! It is the tokens, each an interned symbol, shared: built by putting
//! token runs one after another, with nothing split or joined, and read as
//! text only where it is written out (`Display`). Two are equal where their
//! tokens are, and are ordered as their text is: tokens of printable
//! characters compare one by one as the joined text does, since a space
//! sorts below every character a token holds.

use std::borrow::Cow;
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
        built(|out| text.spell_onto(out))
    }

    /// The runs one after another.
    pub fn joined(parts: &[&[Symbol]]) -> Rpn {
        built(|out| {
            for part in parts {
                out.extend_from_slice(part);
            }
        })
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

    /// Its tokens as reverse Polish: lent where they are held so already.
    fn as_rpn(&self) -> Cow<'_, Rpn> {
        Cow::Owned(built(|out| self.spell_onto(out)))
    }
}

thread_local! {
    /// The tokens a term is put together in before it is shared, kept from
    /// one term to the next so that a term is one allocation.
    static BUILDING: std::cell::Cell<Vec<Symbol>> = const { std::cell::Cell::new(Vec::new()) };
}

/// The tokens `fill` puts down, shared.
fn built(fill: impl FnOnce(&mut Vec<Symbol>)) -> Rpn {
    let mut out = BUILDING.with(std::cell::Cell::take);
    out.clear();
    fill(&mut out);
    let made = Rpn(Rc::from(&out[..]));
    BUILDING.with(|b| b.set(out));
    made
}

impl Spell for Rpn {
    fn spell_onto(&self, out: &mut Vec<Symbol>) {
        out.extend_from_slice(&self.0);
    }

    fn as_rpn(&self) -> Cow<'_, Rpn> {
        Cow::Borrowed(self)
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

    fn as_rpn(&self) -> Cow<'_, Rpn> {
        (**self).as_rpn()
    }
}

impl Rpn {
    /// The parts' tokens one after another.
    pub fn of(parts: &[&dyn Spell]) -> Rpn {
        if let [one] = parts {
            return one.as_rpn().into_owned();
        }
        built(|out| {
            for part in parts {
                part.spell_onto(out);
            }
        })
    }

    /// One part's tokens: the part itself where it is tokens already.
    pub fn spelt(part: &(impl Spell + ?Sized)) -> Rpn {
        part.as_rpn().into_owned()
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
