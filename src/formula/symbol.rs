//! A node's text as an interned string: a letter's name, a numeral's
//! digits, or a notation's literal.
//!
//! Each distinct text is held once for the life of the process, and a
//! `Symbol` points at it. Copying one is copying a pointer, and two are
//! equal exactly when they point at the same text, since a text is
//! interned once. It reads as a `&str` wherever a node's text is read.
//! Hashing and ordering go by the text itself, so a map or a sorted set
//! keyed by symbols walks in the order one keyed by strings did.

use std::borrow::Borrow;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::{OnceLock, RwLock};

use rustc_hash::FxHashSet;

/// An interned text (the module's doc says what is interned and why).
#[derive(Clone, Copy)]
pub struct Symbol(&'static str);

/// Every text interned so far. Texts are few, letters and literals, and
/// each is kept for the life of the process.
fn interned() -> &'static RwLock<FxHashSet<&'static str>> {
    static INTERNED: OnceLock<RwLock<FxHashSet<&'static str>>> = OnceLock::new();
    INTERNED.get_or_init(|| RwLock::new(FxHashSet::default()))
}

impl Symbol {
    /// The symbol of `text`, interning it the first time it is asked.
    pub fn of(text: &str) -> Symbol {
        if let Some(&held) = interned().read().expect("the interned texts").get(text) {
            return Symbol(held);
        }
        let mut write = interned().write().expect("the interned texts");
        if let Some(&held) = write.get(text) {
            return Symbol(held);
        }
        let held: &'static str = Box::leak(text.to_string().into_boxed_str());
        write.insert(held);
        Symbol(held)
    }

    pub fn as_str(self) -> &'static str {
        self.0
    }
}

impl Default for Symbol {
    fn default() -> Symbol {
        Symbol::of("")
    }
}

impl PartialEq for Symbol {
    fn eq(&self, other: &Symbol) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}

impl Eq for Symbol {}

impl Hash for Symbol {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl PartialOrd for Symbol {
    fn partial_cmp(&self, other: &Symbol) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Symbol {
    fn cmp(&self, other: &Symbol) -> std::cmp::Ordering {
        self.0.cmp(other.0)
    }
}

impl Deref for Symbol {
    type Target = str;
    fn deref(&self) -> &str {
        self.0
    }
}

impl AsRef<str> for Symbol {
    fn as_ref(&self) -> &str {
        self.0
    }
}

impl Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        self.0
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0, f)
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.0 == other
    }
}

impl PartialEq<&str> for Symbol {
    fn eq(&self, other: &&str) -> bool {
        self.0 == *other
    }
}

impl PartialEq<String> for Symbol {
    fn eq(&self, other: &String) -> bool {
        self.0 == other
    }
}

impl PartialEq<Symbol> for str {
    fn eq(&self, other: &Symbol) -> bool {
        self == other.0
    }
}

impl PartialEq<Symbol> for &str {
    fn eq(&self, other: &Symbol) -> bool {
        *self == other.0
    }
}

impl PartialEq<Symbol> for String {
    fn eq(&self, other: &Symbol) -> bool {
        self == other.0
    }
}

impl From<&str> for Symbol {
    fn from(text: &str) -> Symbol {
        Symbol::of(text)
    }
}

impl From<Symbol> for String {
    fn from(symbol: Symbol) -> String {
        symbol.0.to_string()
    }
}
