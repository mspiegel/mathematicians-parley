//! The library's items in Lean: each sentence an item concludes is a
//! theorem whose statement is printed from the record, as the checker read
//! it, and whose proof is the record's `lean` entry for that sentence.
//!
//! A citation then applies a theorem that says exactly what the page reads,
//! and `lake build` checks each mapped record against Mathlib, as a
//! citation's test checks it against set.mm in the Metamath build.

use indexmap::IndexMap;

use super::expr::Writer;
use super::names::{module_of, snake};
use super::statement::{binders, Asked, Binder};
use crate::checker::CheckedCorpus;
use crate::corpus::{Record, RecordKind};
use crate::formula::Node;
use crate::outcome::Route;

/// One sentence an item concludes, as Lean has it.
#[derive(Clone, Debug)]
pub struct Sentence {
    /// The theorem's full Lean name.
    pub decl: String,
    pub binders: Vec<Binder>,
    /// The sentence, as the checker read it.
    pub says: Node,
    /// The sentence in Lean.
    pub prop: String,
    /// Where the item is a corpus theorem whose statement holds several
    /// sentences joined, the projection that takes this one, `.2.1`.
    pub part: String,
    /// The arithmetic the page writes in the whole of the declaration's
    /// statement, what it asks included, which the gate's read-back
    /// compares with what Lean elaborated (`readback`).
    pub arithmetic: std::collections::BTreeMap<String, usize>,
}

/// An item of the library in Lean: its sentences, counted across its
/// groups in order, as a citation counts them.
#[derive(Clone, Debug)]
pub struct Item {
    pub module: String,
    pub sentences: Vec<Sentence>,
    /// The record's `lean` entry for each sentence; empty for a corpus
    /// theorem, which its own file proves.
    pub proofs: Vec<String>,
}

/// The prefix a citation writes before an item of this kind.
pub fn prefix(record: &Record) -> &'static str {
    match record.kind {
        RecordKind::Definition => "def",
        RecordKind::Axiom => "axi",
        _ if record.mundane => "mun",
        _ => "thm",
    }
}

/// The module that holds a record's items: `Parley.Items.Stdlib.Divisibility`
/// for the records of `corpus/stdlib/divisibility.records`.
pub fn items_module(record: &Record) -> String {
    module_of(&format!("items/{}", record.module()))
}

/// The record of an item, by its full name.
pub fn record_of<'c>(checked: &'c CheckedCorpus, full: &str) -> Option<&'c Record> {
    checked
        .corpus
        .records
        .iter()
        .find(|r| format!("{}/{}", r.module(), r.name) == full)
}

/// The item a record states, in Lean; declined where a sentence of it does
/// not print. The record's `lean` field holds one proof for each sentence,
/// set apart by ` ; `.
pub fn item(writer: &Writer, checked: &CheckedCorpus, record: &Record) -> Route<Item> {
    let full = format!("{}/{}", record.module(), record.name);
    let Some(Some(groups)) = checked.library.groups.get(&full) else {
        return Route::no(format!("{full} has no reading as an item"));
    };
    let module = items_module(record);
    let base = format!("{}_{}", prefix(record), snake(&record.name));
    let total: usize = groups.iter().map(|g| g.gives.len()).sum();
    let mut sentences = Vec::new();
    for group in groups.iter() {
        for says in &group.gives {
            let mut w = Writer {
                grammar: writer.grammar,
                templates: writer.templates,
                letters: IndexMap::new(),
            };
            let asked: Vec<Asked> = group
                .wants
                .iter()
                .enumerate()
                .map(|(i, (_, node))| Asked {
                    node,
                    name: format!("h{}", i + 1),
                })
                .collect();
            let binders = match binders(&mut w, &asked) {
                Route::Built(b) => b,
                Route::Declined(d) => return Route::Declined(d),
            };
            let prop = match w.formula(says) {
                Route::Built(p) => p.text,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = if total == 1 {
                base.clone()
            } else {
                format!("{base}_{}", sentences.len() + 1)
            };
            let mut stated: Vec<Node> =
                group.wants.iter().map(|(_, n)| n.clone()).collect();
            stated.push(says.clone());
            let arithmetic = super::readback::page_arithmetic(&w, &stated);
            sentences.push(Sentence {
                decl: format!("{module}.{name}"),
                binders,
                says: says.clone(),
                prop,
                part: String::new(),
                arithmetic,
            });
        }
    }
    let proofs: Vec<String> = record
        .field("lean")
        .map(|f| f.split(" ; ").map(|p| p.trim().to_string()).collect())
        .unwrap_or_default();
    if proofs.len() != sentences.len() {
        return Route::no(format!(
            "{full} concludes {} sentences and its lean field gives {} proofs",
            sentences.len(),
            proofs.len()
        ));
    }
    Route::Built(Item {
        module,
        sentences,
        proofs,
    })
}

/// A Lean theorem's declaration, its name taken from its full name.
pub fn declaration(sentence: &Sentence, proof: &str) -> String {
    let short = sentence.decl.rsplit('.').next().unwrap_or(&sentence.decl);
    let binders: Vec<String> = sentence.binders.iter().map(Binder::lean).collect();
    let space = if binders.is_empty() { "" } else { " " };
    format!(
        "theorem {short}{space}{} :\n    {} :=\n  {proof}",
        binders.join(" "),
        sentence.prop
    )
}
