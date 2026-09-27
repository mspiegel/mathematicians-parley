//! The elaborator: from a readable proof to a Metamath file.
//!
//! `ELABORATION.md` describes the six parts it is built from, and each has a
//! module here: reading a line as kernel terms (`reading`), the scope each
//! line is proved under (`scopes`), fitting a lemma to a claim (`matcher`),
//! the rule tables (`tables`), the calculators (`calculators`, over `field`,
//! `linear` and `normal`), and what a step's proof may rest on
//! (`provenance`). `elaborate` is the main loop and the file it writes.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::IndexMap;

use crate::formula::Node;
use crate::mm::spell::{Part, Proof};

pub mod calculators;
pub mod definitions;
pub mod elaborate;
pub mod field;
pub mod linear;
pub mod matcher;
pub mod normal;
pub mod provenance;
pub mod reading;
pub mod scopes;
pub mod state;
pub mod tables;

pub use elaborate::{elaborate, statement_of, Elaborated, Library};
pub use state::Elaborator;

/// A table by claim that more than one holder may share and change, as the
/// frames of scopes and the step loop share what is known at a scope.
///
/// Cloning the table shares it; [`Table::copy`] is a table of its own with
/// the same entries.
pub struct Table<V>(Rc<RefCell<IndexMap<String, V>>>);

impl<V> Clone for Table<V> {
    fn clone(&self) -> Self {
        Table(self.0.clone())
    }
}

impl<V: Clone> Default for Table<V> {
    fn default() -> Self {
        Table::new()
    }
}

impl<V: Clone> Table<V> {
    pub fn new() -> Self {
        Table(Rc::new(RefCell::new(IndexMap::new())))
    }

    pub fn of(map: IndexMap<String, V>) -> Self {
        Table(Rc::new(RefCell::new(map)))
    }

    /// A table of its own with the same entries.
    pub fn copy(&self) -> Self {
        Table::of(self.0.borrow().clone())
    }

    pub fn get(&self, key: &str) -> Option<V> {
        self.0.borrow().get(key).cloned()
    }

    pub fn has(&self, key: &str) -> bool {
        self.0.borrow().contains_key(key)
    }

    pub fn set(&self, key: impl Into<String>, value: V) {
        self.0.borrow_mut().insert(key.into(), value);
    }

    /// The entry, where there is none yet.
    pub fn set_default(&self, key: impl Into<String>, value: V) {
        self.0.borrow_mut().entry(key.into()).or_insert(value);
    }

    /// Every entry as it stands now, in order.
    pub fn entries(&self) -> Vec<(String, V)> {
        self.0
            .borrow()
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect()
    }

    pub fn keys(&self) -> Vec<String> {
        self.0.borrow().keys().cloned().collect()
    }

    pub fn len(&self) -> usize {
        self.0.borrow().len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }

    /// This table's entries with `over`'s laid on top: `{**self, **over}`.
    pub fn with(&self, over: &Table<V>) -> Self {
        let mut out = self.0.borrow().clone();
        for (k, v) in over.0.borrow().iter() {
            out.insert(k.clone(), v.clone());
        }
        Table::of(out)
    }

    /// The entries that pass `keep`, as a table of their own.
    pub fn filtered(&self, keep: impl Fn(&str, &V) -> bool) -> Self {
        Table::of(
            self.0
                .borrow()
                .iter()
                .filter(|(k, v)| keep(k, v))
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        )
    }

    pub fn same(&self, other: &Table<V>) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

/// What is known at a scope: a proof of each claim under it.
pub type Facts = Table<Proof>;

/// A claim, a proof of it at one scope, and the sentences it was read from.
///
/// A line may say several things, and a substitution may land in one of
/// them, so what is kept is every sentence rather than the claim as one
/// tree. A line read from no text at all keeps none.
#[derive(Clone)]
pub struct Line {
    pub term: String,
    pub proof: Proof,
    pub sentences: Vec<Node>,
}

/// Each proved line of the theorem, by its label or number.
pub type Lines = Table<Line>;

/// One part of a proof being assembled, from whatever holds it.
pub trait PartOf {
    fn part(&self) -> Part<'_>;
}

impl PartOf for str {
    fn part(&self) -> Part<'_> {
        Part::Text(self)
    }
}

impl PartOf for String {
    fn part(&self) -> Part<'_> {
        Part::Text(self)
    }
}

impl PartOf for Rc<str> {
    fn part(&self) -> Part<'_> {
        Part::Text(self)
    }
}

impl PartOf for Proof {
    fn part(&self) -> Part<'_> {
        Part::Proof(self)
    }
}

impl<T: PartOf + ?Sized> PartOf for &T {
    fn part(&self) -> Part<'_> {
        (**self).part()
    }
}

pub fn part<T: PartOf + ?Sized>(x: &T) -> Part<'_> {
    x.part()
}

/// Tokens in order, skipping any that are empty: a term or a formula in
/// reverse Polish.
#[macro_export]
macro_rules! t {
    ($($x:expr),* $(,)?) => {
        $crate::mm::spell::seq(&[$(::std::convert::AsRef::<str>::as_ref(&$x)),*])
    };
}

/// A proof assembled from labels and proofs in order, on a builder.
#[macro_export]
macro_rules! pf {
    ($b:expr; $($x:expr),* $(,)?) => {
        $b.proof(&[$($crate::elab::part(&$x)),*])
    };
}

/// What was built, or the decline handed back to the caller as it stands.
#[macro_export]
macro_rules! take {
    ($e:expr) => {
        match $e {
            $crate::outcome::Route::Built(v) => v,
            $crate::outcome::Route::Declined(d) => {
                return Ok($crate::outcome::Route::Declined(d))
            }
        }
    };
}
