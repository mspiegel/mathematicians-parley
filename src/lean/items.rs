//! The library's items in Lean: each sentence an item concludes is a
//! theorem whose statement is printed from the record, as the checker read
//! it, and whose proof is the record's `lean` entry for that sentence.
//!
//! A citation then applies a theorem that says exactly what the page reads,
//! and `lake build` checks each mapped record against Mathlib, as a
//! citation's test checks it against set.mm in the Metamath build.

use indexmap::IndexMap;

use super::expr::{LetterType, Writer, GENERAL};
use super::names::{module_of, snake};
use super::statement::{binders, Asked, Binder};
use super::templates::Num;
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
    /// What its general letters range over; None where it has none.
    pub general: Option<General>,
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

/// What an item's general letters range over: the number type the record
/// puts them in, and the kind of ring a statement of that type needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct General {
    /// ℂ or ℝ, as the record says.
    pub num: Num,
    /// Whether the statement divides, so that it holds in a field.
    pub field: bool,
    /// Whether it orders, so that it holds in an ordered ring.
    pub ordered: bool,
    /// Whether it takes a floor, so that it holds in a ring with one.
    pub floor: bool,
}

impl General {
    /// The Lean binders of the type and its class.
    pub fn binders(&self) -> String {
        // A domain, so that a statement that cancels a factor, or says a
        // product is 0 only where a factor is, holds; ℤ, ℚ, ℝ and ℂ are
        // all domains, and a field is one already.
        let ring = if self.field {
            format!("[Field {GENERAL}]")
        } else {
            format!("[CommRing {GENERAL}] [IsDomain {GENERAL}]")
        };
        let order = if self.ordered {
            format!(" [LinearOrder {GENERAL}] [IsStrictOrderedRing {GENERAL}]")
        } else {
            String::new()
        };
        let floor = if self.floor {
            format!(" [FloorRing {GENERAL}]")
        } else {
            String::new()
        };
        format!("{{{GENERAL} : Type*}} {ring}{order}{floor}")
    }
}

/// The notations a statement may use and hold in any ring of a kind: its
/// arithmetic, order, floor and connectives. A statement using any other, √
/// or π, is about ℝ or ℂ themselves.
const ALGEBRAIC: &[&str] = &[
    "name",
    "numeral",
    "additive",
    "multiplicative",
    "power",
    "superscript",
    "unary-minus",
    "equality",
    "order",
    "absolute-value",
    "floor",
    "conjunction",
    "comma-conjunction",
    "disjunction",
    "logical-not",
    "biconditional",
    "conditional",
    "implication",
    "membership",
    "number-systems",
];

/// Whether an item's sentence holds of any ring of a kind, and which: where
/// the record puts a letter in ℂ or ℝ and the sentence uses only arithmetic,
/// order and connectives, it is said of any commutative ring, a field where
/// it divides, ordered where it orders, as Mathlib states such facts. A
/// citation then applies it in the citing claim's own type.
fn general_kind(group: &crate::citing::Group, says: &Node) -> Option<General> {
    let nodes: Vec<&Node> = group
        .wants
        .iter()
        .map(|(_, n)| n)
        .chain(std::iter::once(says))
        .collect();
    let systems: Vec<Num> = nodes
        .iter()
        .filter_map(|n| super::statement::introduces(n))
        .map(|(_, s)| super::expr::letter_type(s))
        .collect();
    let num = if systems.contains(&Num::Complex) {
        Num::Complex
    } else if systems.contains(&Num::Real) {
        Num::Real
    } else {
        return None;
    };
    let parts: Vec<Node> = nodes.iter().flat_map(|n| n.walk()).collect();
    if !parts
        .iter()
        .all(|p| ALGEBRAIC.contains(&&*p.notation_name()))
    {
        return None;
    }
    let field = parts
        .iter()
        .any(|p| p.spelling() == crate::notations::DIVIDED);
    let floor = parts.iter().any(|p| &*p.notation_name() == "floor");
    let ordered = floor
        || parts.iter().any(|p| {
            matches!(
                p.notation(),
                crate::notations::ORDER | crate::notations::ABSOLUTE_VALUE
            )
        });
    if num == Num::Complex && ordered {
        return None;
    }
    Some(General {
        num,
        field,
        ordered,
        floor,
    })
}

/// The letters that stand where a statement stands: a whole sentence, or a
/// part an "and", "or", "not", "if" or "↔" joins, the P and Q of a rule of
/// reasoning.
fn statement_letters(sentences: &[Node]) -> std::collections::BTreeSet<String> {
    use crate::notations::{
        BICONDITIONAL, COMMA_CONJUNCTION, CONDITIONAL, CONJUNCTION, DISJUNCTION,
        IMPLICATION, LOGICAL_NOT,
    };
    let mut out = std::collections::BTreeSet::new();
    for s in sentences {
        if s.is_name() {
            out.insert(s.text.to_string());
        }
        for n in s.walk() {
            let joins = matches!(
                n.notation(),
                BICONDITIONAL
                    | COMMA_CONJUNCTION
                    | CONDITIONAL
                    | CONJUNCTION
                    | DISJUNCTION
                    | IMPLICATION
                    | LOGICAL_NOT
            );
            if joins {
                out.extend(
                    n.children
                        .iter()
                        .filter(|c| c.is_name())
                        .map(|c| c.text.to_string()),
                );
            }
        }
    }
    out
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
/// not print. The record's `lean-proof` field holds one proof for each sentence,
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
                general: None,
                integers: Vec::new(),
            };
            let kind = general_kind(group, says);
            w.general = kind.map(|k| k.num);
            let asked: Vec<Asked> = group
                .wants
                .iter()
                .enumerate()
                .map(|(i, (_, node))| Asked {
                    node,
                    name: format!("h{}", i + 1),
                })
                .collect();
            // A letter of the item that stands for a statement, the P of
            // "P or Q", is a proposition it is stated for.
            let mut statements = Vec::new();
            let stated: Vec<Node> = group
                .wants
                .iter()
                .map(|(_, n)| n.clone())
                .chain(std::iter::once(says.clone()))
                .collect();
            let said = statement_letters(&stated);
            for name in group.free_names(&writer.grammar.binders()) {
                if said.contains(&name) {
                    w.letters.insert(name.clone(), LetterType::Statement);
                    statements.push(Binder::Letter {
                        name: super::names::letter(&name),
                        page: name,
                        ty: LetterType::Statement,
                        general: false,
                    });
                }
            }
            let binders = match binders(&mut w, &asked) {
                Route::Built(b) => statements.into_iter().chain(b).collect(),
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
                general: kind,
            });
        }
    }
    let proofs: Vec<String> = record
        .lean_target()
        .map(|f| f.split(" ; ").map(|p| p.trim().to_string()).collect())
        .unwrap_or_default();
    if proofs.len() != sentences.len() {
        return Route::no(format!(
            "{full} concludes {} sentences and its lean-proof field gives {} proofs",
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
    let mut binders: Vec<String> =
        sentence.general.iter().map(General::binders).collect();
    binders.extend(sentence.binders.iter().map(Binder::lean));
    let space = if binders.is_empty() { "" } else { " " };
    format!(
        "theorem {short}{space}{} :\n    {} :=\n  {proof}",
        binders.join(" "),
        sentence.prop
    )
}
