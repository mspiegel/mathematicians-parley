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

pub(crate) mod calculators;
pub(crate) mod definitions;
pub mod elaborate;
pub(crate) use crate::methods::field;
mod inspection;
pub(crate) use crate::methods::linear;
pub(crate) mod matcher;
pub(crate) mod normal;
pub mod numerals;
pub(crate) mod provenance;
pub(crate) mod reading;
pub(crate) mod scopes;
mod spoken;
pub(crate) mod state;
pub(crate) mod tables;

pub use elaborate::{elaborate, statement_of, Elaborated, Library, ReadLibrary};

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

    /// This table's entries made `saved`'s again, for every holder of it.
    pub fn restore(&self, saved: &Table<V>) {
        *self.0.borrow_mut() = saved.0.borrow().clone();
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
///
/// A fact is found by its standard form, the one the normalizer gives it
/// (`Elaborator::fact_key`), so a fact written one way is held whichever way
/// a route asks for it: `0 ≠ k`, `k ≠ 0` and `¬ k = 0` are one fact. The
/// table keeps each claim as it was proved, with its standard form beside
/// it, and only the elaborator stores or finds one (`Elaborator::know`,
/// `Elaborator::held`): reading a standard form and proving one spelling
/// from another are its.
///
/// Cloning the table shares it; [`Facts::copy`] is a table of its own with
/// the same entries.
#[derive(Clone, Default)]
pub struct Facts {
    proofs: Table<Proof>,
    /// Each standard form, and the claims held under it in the order they
    /// were proved.
    standard: Table<Vec<String>>,
    /// Each claim as each line proved it, by `line_key`: two lines may say
    /// one thing, and a step naming one rests on that one, where `proofs`
    /// holds the claim as it was proved last.
    by_line: Table<Proof>,
}

/// Where a line's proof of a claim is kept in `Facts::by_line`.
fn line_key(line: &str, claim: &str) -> String {
    format!("{line}\u{0}{claim}")
}

/// The claim a `line_key` is kept under.
fn claim_of_key(key: &str) -> &str {
    key.split_once('\u{0}').map_or(key, |(_, claim)| claim)
}

/// The line a proof is that line's own proof of, where it rests on one
/// line alone, as a sealed step's proof and what is carried from it do.
fn sole_line(proof: &Proof) -> Option<&str> {
    match proof.origin.iter().collect::<Vec<_>>().as_slice() {
        [one] => Some(one.as_str()),
        _ => None,
    }
}

impl Facts {
    pub fn new() -> Self {
        Facts::default()
    }

    /// A table of its own with the same entries.
    pub fn copy(&self) -> Self {
        Facts {
            proofs: self.proofs.copy(),
            standard: self.standard.copy(),
            by_line: self.by_line.copy(),
        }
    }

    /// Every claim and its proof as they stand now, in order.
    pub fn entries(&self) -> Vec<(String, Proof)> {
        self.proofs.entries()
    }

    /// Every claim, in order.
    pub fn keys(&self) -> Vec<String> {
        self.proofs.keys()
    }

    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.proofs.is_empty()
    }

    /// This table's facts with `over`'s laid on top.
    pub fn with(&self, over: &Facts) -> Self {
        let standard = self.standard.copy();
        for (key, claims) in over.standard.entries() {
            // What is laid on top is the latest under its standard form.
            let mut held = standard.get(&key).unwrap_or_default();
            for claim in claims {
                held.retain(|c| *c != claim);
                held.push(claim);
            }
            standard.set(key, held);
        }
        Facts {
            proofs: self.proofs.with(&over.proofs),
            standard,
            by_line: self.by_line.with(&over.by_line),
        }
    }

    /// The facts that pass `keep`, as a table of their own.
    pub fn filtered(&self, keep: impl Fn(&str, &Proof) -> bool) -> Self {
        let by_line = self
            .by_line
            .filtered(|key, proof| keep(claim_of_key(key), proof));
        let proofs = self.proofs.filtered(keep);
        let standard = Table::new();
        for (key, claims) in self.standard.entries() {
            let kept: Vec<String> =
                claims.into_iter().filter(|c| proofs.has(c)).collect();
            if !kept.is_empty() {
                standard.set(key, kept);
            }
        }
        Facts {
            proofs,
            standard,
            by_line,
        }
    }

    /// `filtered`, keeping what each line gave as it stands: a claim left
    /// out of the scope is still the claim of the line that gave it, which a
    /// step naming that line reads (`named_first`, `carried`).
    pub fn filtered_claims(&self, keep: impl Fn(&str, &Proof) -> bool) -> Self {
        let mut out = self.filtered(keep);
        out.by_line = self.by_line.filtered(|_, _| true);
        out
    }

    pub fn same(&self, other: &Facts) -> bool {
        self.proofs.same(&other.proofs)
    }

    /// The same claims, each proved by what `carry` makes of its proof, as a
    /// table of its own: a fact's standard form is its claim's, whatever
    /// proves it, so the table is carried to a wider scope as it stands.
    pub fn rebased(&self, mut carry: impl FnMut(&str, Proof) -> Proof) -> Self {
        let proofs = Table::new();
        for (claim, proof) in self.proofs.entries() {
            let made = carry(&claim, proof);
            proofs.set(claim, made);
        }
        let by_line = Table::new();
        for (key, proof) in self.by_line.entries() {
            let made = carry(claim_of_key(&key), proof);
            by_line.set(key, made);
        }
        Facts {
            proofs,
            standard: self.standard.copy(),
            by_line,
        }
    }

    /// The proof of `claim` that `line` gave, carried to this scope, where
    /// the table holds one.
    pub(crate) fn line_proof(&self, line: &str, claim: &str) -> Option<Proof> {
        self.by_line.get(&line_key(line, claim))
    }

    /// Every claim `line` gave, with the proof it gave, in order.
    pub(crate) fn of_line(&self, line: &str) -> Vec<(String, Proof)> {
        let prefix = line_key(line, "");
        self.by_line
            .entries()
            .into_iter()
            .filter_map(|(key, proof)| {
                key.strip_prefix(&prefix)
                    .map(|claim| (claim.to_string(), proof))
            })
            .collect()
    }

    /// The line `proof` rests on as having given `claim`, leaving the claim
    /// as it was proved last: a part of a line that an earlier line said too.
    pub(crate) fn store_for_line(&self, claim: &str, proof: Proof) {
        if let Some(line) = sole_line(&proof) {
            self.by_line.set(line_key(line, claim), proof.clone());
        }
    }

    /// `claim` proved by `proof`, held under `standard`, its standard form.
    pub(crate) fn store(&self, claim: String, standard: String, proof: Proof) {
        if let Some(line) = sole_line(&proof) {
            self.by_line.set(line_key(line, &claim), proof.clone());
        }
        self.proofs.set(claim.clone(), proof);
        // The claims under a standard form stand in the order they were
        // last proved, so the latest is last.
        let mut held = self.standard.get(&standard).unwrap_or_default();
        held.retain(|c| *c != claim);
        held.push(claim);
        self.standard.set(standard, held);
    }

    /// `store`, where the claim is not held yet as it is spelt.
    pub(crate) fn store_default(&self, claim: String, standard: String, proof: Proof) {
        if !self.proofs.has(&claim) {
            self.store(claim, standard, proof);
        }
    }

    /// The claims held under a standard form, in the order they were last
    /// proved.
    pub(crate) fn under(&self, standard: &str) -> Vec<String> {
        self.standard.get(standard).unwrap_or_default()
    }

    /// The proof of a claim held as it is spelt.
    pub(crate) fn proof(&self, claim: &str) -> Option<Proof> {
        self.proofs.get(claim)
    }
}

/// What the lines of the step being proved wrote, each with the scope it
/// was proved under, which the membership lookup and the one-lemma bridge
/// read before any search (`Elaborator::writing`). A fact here is found by
/// its standard form as one in `Facts` is (`Elaborator::written_held`).
///
/// A clone is a table of its own, since what a step wrote is set aside and
/// put back around the work that changes it.
#[derive(Default)]
pub struct Written {
    facts: Facts,
    /// Each claim, as it was proved, and the scope it was proved under.
    at: IndexMap<String, String>,
}

/// A fact the step's lines wrote: its proof, and the scope it is under.
pub struct WrittenFact {
    pub proof: Proof,
    pub at: String,
}

impl Clone for Written {
    fn clone(&self) -> Self {
        Written {
            facts: self.facts.copy(),
            at: self.at.clone(),
        }
    }
}

impl Written {
    pub fn new() -> Self {
        Written::default()
    }

    /// Each claim, its proof and its scope, in order.
    pub fn entries(&self) -> Vec<(String, WrittenFact)> {
        self.facts
            .entries()
            .into_iter()
            .map(|(claim, proof)| {
                let at = self.at.get(&claim).cloned().unwrap_or_default();
                (claim, WrittenFact { proof, at })
            })
            .collect()
    }

    /// The facts whose proofs pass `keep`.
    pub fn filtered(&self, keep: impl Fn(&Proof) -> bool) -> Self {
        let facts = self.facts.filtered(|_, p| keep(p));
        let at = self
            .at
            .iter()
            .filter(|(claim, _)| facts.proof(claim).is_some())
            .map(|(c, s)| (c.clone(), s.clone()))
            .collect();
        Written { facts, at }
    }

    /// `claim`, proved by `proof` under `at`, held under `standard`.
    pub(crate) fn store(
        &mut self,
        claim: String,
        standard: String,
        at: String,
        proof: Proof,
    ) {
        self.at.insert(claim.clone(), at);
        self.facts.store(claim, standard, proof);
    }

    /// The facts held under a standard form, and the latest of them.
    pub(crate) fn facts(&self) -> &Facts {
        &self.facts
    }

    /// The scope a claim was proved under.
    pub(crate) fn at(&self, claim: &str) -> Option<&String> {
        self.at.get(claim)
    }
}

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

impl PartOf for crate::mm::Rpn {
    fn part(&self) -> Part<'_> {
        Part::Tokens(self)
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
