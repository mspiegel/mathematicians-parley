//! Turn a readable proof into a Metamath proof.
//!
//! `ELABORATION.md` lists what the expansion language has to have. `obtain`,
//! `contradiction`, `proof` and `induction` open scopes; `substitute`,
//! `calculation`, `join` and `exhibit` are steps; a definition may be
//! unfolded, read the other way, or used to conclude an existence claim; a
//! name may be introduced by a `define`; and a theorem may be cited whether
//! set.mm supplies it or this corpus proves it.
//!
//! Two things shape the code. A step is elaborated in deduction form, so
//! every line is an implication whose antecedent is the scope it sits in.
//! And the readable layer writes which side condition a step needs but never
//! how to prove it, so what the text leaves out is settled from the lemmas
//! `rules::MEMBERSHIP` names.
//!
//! What is not expanded is stated at the head of the file it writes: a
//! closure method, or an item the database gives no target for.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::Arc;

use indexmap::IndexMap;

use super::field::{self, Verdict};
use super::matcher::{conjuncts_of, ChainLink};
use super::provenance::requirement;
use super::reading::{is_subgroup, CLASS_NAMES};
use super::scopes::written_parts;
use super::state::{
    fit, names_of, number_of, Binding, Block, ByPart, Closer, Contradicted, Elaborator,
    PartEnd, ProvedClaim, Vars,
};
use super::tables::Leaf;
use super::{linear, Facts, Line, Lines};
use crate::checker::record::{
    CheckedTheorem, Cited, FirstAt, LibraryReading, SuppliedBy,
};
use crate::citing::{self, filled};
use crate::corpus::proof::{
    chain, requires_as_step, substitute_rows, ChainLine, Head, Justification, Requires,
};
use crate::corpus::{
    define_parts, Corpus, DefineParts, Hypothesis, Intro, Item, Method, Record, Step,
    Theorem, Value,
};
use crate::formula::page::{related, Written};
use crate::formula::symbol::Symbol;
use crate::formula::{Grammar, Node};
use crate::matching::{Binding as NodeBinding, Defined};
use crate::methods::{reals, surds};
use crate::mm::compress::{compressed, labels as compress_labels, shapes_of};
use crate::mm::kernel::{Syntax, Term};
use crate::mm::library::thousands;
use crate::mm::spell::Proof;
use crate::mm::{Kind, Layered, Lookup, Rpn, Signature, Signatures};
use crate::notations::{
    COMMA_CONJUNCTION, CONJUNCTION, EQUAL_CHAIN, EXISTS, FUNCTION_TYPE, IS_A_POINT,
    MEMBERSHIP,
};
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules::{self, lookup};
use crate::sorts::introduction::{Form, Introduction};
use crate::text::repr;
use crate::{binds, pf, t, take, targets};

use self::library::*;
pub use self::library::{Elaborated, Library, Options, ReadLibrary};
use crate::corpus::proof;
use crate::text;

mod chains;
mod cited_items;
mod cites;
mod corpus;
mod defines;
mod library;
mod running;
mod unfolds;

/// Why a side of a step citing a define is not what the define names.
const NAMES_NO_DEFINE: &str = "this side names no define";

/// The letters a map read from a rule a citation binds may bind, the first
/// one free taken (`rule_as_map`).
const MAP_LETTERS: [&str; 6] = ["u", "v", "w", "s", "r", "q"];

/// The two sides of an equation, as written (`Elaborator::equation_sides`).
pub(crate) struct Sides {
    /// The side before `=`.
    pub left: Rpn,
    /// The side after it.
    pub right: Rpn,
}

/// A citation of a theorem proved in another file (`Elaborator::cited_pushes`).
struct Pushed {
    /// What the citation pushes for each of the theorem's variables, in order.
    values: Vec<Rpn>,
    /// The theorem's statement, typecode first, over its own variables.
    statement: Vec<Symbol>,
    /// Each of those variables with its typecode, in the order pushed.
    floats: Vec<(Symbol, Symbol)>,
}

impl Pushed {
    /// Whether two of the theorem's set variables are given one letter,
    /// which its disjointness forbids.
    fn letters_meet(&self) -> bool {
        let letters: Vec<&Rpn> = self
            .floats
            .iter()
            .zip(&self.values)
            .filter(|((typecode, _), _)| typecode.as_str() == "setvar")
            .map(|(_, value)| value)
            .collect();
        letters
            .iter()
            .enumerate()
            .any(|(i, a)| letters[i + 1..].contains(a))
    }
}

/// Which of the four ways a biconditional definition reaches a claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Way {
    /// The biconditional itself is what the step claims, and its lemma is
    /// applied as it stands, as a theorem's is.
    AsStated,
    /// It concludes an existence claim from a witness.
    Conclude,
    /// Its right side is what the step holds, read right to left.
    Equivalent,
    /// Its left side is what the step holds, unfolded and taken apart.
    Unfolded,
}

/// What this elaborator calls a theorem it has written out: its full name,
/// file and theorem, with a dot where the name has a slash, which Metamath
/// does not allow in a label: `proofs.wiedijk.sqrt2-irrational.even-square`.
///
/// The label depends on nothing but the theorem's own name, so adding or
/// renaming another theorem never moves it. Two theorems of one file have
/// two names, and set.mm writes a dot only in a hypothesis's label, after
/// its theorem's, so no set.mm label begins `proofs.` or `tests.`; a label
/// already taken is a defect all the same rather than one moved aside. A
/// label is ASCII, as Metamath asks, so a Greek letter in a name is spelt by
/// its English name: a theorem named σ is labelled from `sigma`.
pub fn label_of(
    name: &str,
    taken: &dyn Lookup,
    syntax: &Syntax,
    path: &str,
    line: usize,
) -> Checked<String> {
    let label = text::spelt_in_ascii(&name.replace('/', "."));
    let allowed = |c: char| c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '.');
    if !label.chars().all(allowed) {
        return Err(Problem::new(
            path,
            line,
            format!(
                "{} cannot be a Metamath label, which is letters, digits, `-`, `_` and `.`",
                repr(&label)
            ),
        ));
    }
    if taken.contains_key(&label) || syntax.is_symbol(&label) {
        return Err(Problem::new(
            path,
            line,
            format!("{} is a label set.mm already uses", repr(&label)),
        ));
    }
    Ok(label)
}

/// An item's full name: its file's module, then its own name.
fn qualified(item: Item) -> String {
    match item {
        Item::Record(r) => r.qualified(),
        Item::Theorem(t) => t.qualified(),
    }
}

/// The prefix a citation of the item writes.
fn item_kind(item: Item) -> &'static str {
    item.cited_as().prefix()
}

/// Whether `block` is still open at a step standing in the parts `around`
/// (`CheckedTheorem::around`, each part named by its block's owner): a
/// block a part's `by` line opened is open while its part is, any other
/// while its owner's block is.
fn stands_open(thm: &Theorem, block: &Block, around: &[ByPart]) -> bool {
    match block.by_part {
        Some(by) => around
            .iter()
            .any(|p| p.owner == by.owner && p.part == by.part),
        None => CheckedTheorem::index_of(thm, &block.owner)
            .is_some_and(|i| around.iter().any(|p| p.owner == i)),
    }
}

/// The methods the build expands itself; the others open a block or take
/// apart what a citation gives, and are expanded where those are.
const EXPANDED: [Method; 14] = [
    Method::Algebra,
    Method::Arithmetic,
    Method::RealArithmetic,
    Method::Inequalities,
    Method::Transitivity,
    Method::Antisymmetry,
    Method::Membership,
    Method::Inspection,
    Method::Substitute,
    Method::Instantiate,
    Method::Calculation,
    Method::Join,
    Method::Restate,
    Method::Exhibit,
];

/// How a step is expanded, by what its justification opens with.
enum How {
    /// One of the methods the build expands itself (`EXPANDED`).
    Named(Method),
    /// A define, cited by its label.
    Define,
    TakeDefinition,
    Reading(Way),
    UnfoldEquation,
    Cite,
}

/// A conjunction taken apart, left to right, with every conjunction in it
/// taken apart too, as the checker counts its parts (`citing::conjuncts`).
fn conjunction_parts(term: &Term) -> Vec<Term> {
    if matches!(term.label(), Some("wa") | Some("w3a")) {
        return term.children().iter().flat_map(conjunction_parts).collect();
    }
    vec![term.clone()]
}

/// The parts of a sentence's set.mm form, taken apart where the sentence
/// itself joins claims by "and" or chains equations, as the checker counts
/// a `FirstAt`'s part (`citing::conjuncts`). A claim whose own set.mm form
/// is a conjunction, as "n is odd" is n ∈ ℤ ∧ ¬ 2 ∥ n, stays one part.
pub(super) fn parts_along(node: &Node, term: &Term) -> Vec<Term> {
    if node.notation() == EQUAL_CHAIN {
        return conjunction_parts(term);
    }
    let joins = node.notation() == CONJUNCTION || node.notation() == COMMA_CONJUNCTION;
    if joins
        && node.children.len() == 2
        && term.label() == Some("wa")
        && term.children().len() == 2
    {
        let mut out = parts_along(&node.children[0], &term.children()[0]);
        out.extend(parts_along(&node.children[1], &term.children()[1]));
        return out;
    }
    vec![term.clone()]
}

/// Whether `piece` says what a function the binding fixes maps between.
fn function_fixed(piece: &Term, binding: &Binding) -> bool {
    if piece.variable().is_some()
        || !matches!(
            piece.label(),
            Some("wf") | Some("wf1") | Some("wfo") | Some("wf1o")
        )
        || piece.children().len() != 3
    {
        return false;
    }
    piece.children()[2]
        .variable()
        .is_some_and(|v| binding.contains_key(v))
}

/// The theorems `cited` names, each after every other of them it rests on,
/// directly or through theorems not cited here, and otherwise in the order
/// given.
fn rested_first(cited: &[String], corpus: &Corpus) -> Vec<String> {
    fn visit(
        name: &str,
        cited: &[String],
        corpus: &Corpus,
        seen: &mut BTreeSet<String>,
        out: &mut Vec<String>,
    ) {
        if !seen.insert(name.to_string()) {
            return;
        }
        if let Some(thm) = corpus.theorems.iter().find(|t| t.qualified() == name) {
            for (other, _) in proof::cited_items(thm) {
                visit(&other, cited, corpus, seen, out);
            }
        }
        if cited.iter().any(|c| c == name) {
            out.push(name.to_string());
        }
    }
    let mut seen = BTreeSet::new();
    let mut out = Vec::new();
    for name in cited {
        visit(name, cited, corpus, &mut seen, &mut out);
    }
    out
}

/// Elaborate one theorem of the corpus into its file.
///
/// `statements` gives the statement a cited theorem's file proves, where it
/// is known, and `library_read` every item a citation may name, as the
/// checker read it.
#[allow(clippy::too_many_arguments)]
pub fn elaborate(
    corpus: &Corpus,
    g: &Grammar,
    items: &IndexMap<String, Item>,
    thm: &Theorem,
    checked: &CheckedTheorem,
    library: &Library,
    library_read: &LibraryReading,
    statements: &dyn Fn(&str) -> Option<String>,
    options: Options,
) -> Checked<Elaborated> {
    // What the checker refuses is not built, and is said as the checker says
    // it (`checker::checked`).
    if let Some(first) = checked.problems.first() {
        return Err(first.clone());
    }
    let mut sigs = Layered::new(Arc::clone(&library.sigs));
    declare_constants(&mut sigs, &corpus.records)?;
    let syntax = library.syntax_for(&sigs);
    let mut work = Elaborator::new(
        thm,
        checked.clone(),
        g,
        items,
        sigs,
        &corpus.records,
        library_read,
        &corpus.scopes,
        statements,
    );
    work.b.share_syntax(syntax);
    work.whole_scope = options.whole_scope_offered;
    work.map_types_off = options.map_types_off;
    work.said_back = options.say_back.then(Vec::new);
    // The checker accepted the theorem, so what stops its proof here is the
    // build's to fix (`Problem::gap`).
    let (goal, hypotheses, mut proof) = work.run().map_err(Problem::gap)?;
    let mut antecedent = hypotheses.first().cloned();
    for extra in hypotheses.iter().skip(1) {
        antecedent = Some(t!(antecedent.unwrap(), extra, "wa"));
    }
    if antecedent.is_none() {
        // Nothing is assumed, so the scope that carried the proof was truth
        // and the statement says only what the theorem concludes.
        proof = pf!(work.b; goal, proof, "mptru");
    }
    // What is written out is the proof's steps, numbered into their shapes
    // once, and which labels the proof uses is read off those.
    let (root, kinds) =
        shapes_of(&proof.items).map_err(|e| Problem::new(&thm.path, thm.line, e))?;
    let used = compress_labels(&kinds);
    let mut out = String::new();
    out.push_str(&format!(
        "$( {}, elaborated from {} by parley build.\n",
        text::spelt_in_ascii(&thm.qualified()),
        thm.path
    ));
    // A line no route builds stops the build, so every file says this.
    out.push_str("   Nothing here is assumed.\n");
    out.push_str(&format!(
        "   Checked against a set.mm of {} assertions, sha256\n   {}. $)\n",
        thousands(library.size),
        library.digest
    ));
    out.push('\n');
    // A proof that reaches a label of proved.mm includes it, whatever else it
    // includes: a cited theorem's file brings in only what that proof
    // reached. It rests on no theorem of the corpus, so it comes first.
    // proved.mm includes the definitions, so it is the one include where
    // nothing is cited.
    let wants = used.iter().any(|l| library.provided.contains(&**l));
    if wants {
        out.push_str("$[ stdlib/proved.mm $]\n");
    }
    // A theorem this corpus proves is cited as one label, so the file that
    // elaborated it is read first and the rest comes in through it. With a
    // cited theorem's file included after one that rests on it, metamath-rs
    // rejects the proof ("Step used before definition"), so each comes after
    // the cited theorems it rests on, however it reaches them.
    for name in rested_first(&work.cited, corpus) {
        out.push_str(&format!("$[ {}.mm $]\n", text::spelt_in_ascii(&name)));
    }
    if work.cited.is_empty() && !wants {
        out.push_str("$[ stdlib/definitions.mm $]\n");
    }
    out.push('\n');
    // Every variable the proof touches has to be disjoint from every other
    // it binds: a name it binds from everything else.
    let sigs = &work.b.sigs;
    let held: Vec<&str> = used
        .iter()
        .map(|l| l.as_str())
        .filter(|t| sigs.get(t).is_some_and(|s| s.kind == Kind::Float))
        .collect();
    let mut bound: Vec<String> = held
        .iter()
        .filter(|t| sigs[**t].statement[0] == "setvar")
        .map(|t| sigs[*t].statement[1].to_string())
        .collect();
    bound.sort();
    let mut free: Vec<String> = held
        .iter()
        .filter(|t| sigs[**t].statement[0] != "setvar")
        .map(|t| sigs[*t].statement[1].to_string())
        .collect();
    free.sort();
    out.push_str("${\n");
    if bound.len() > 1 {
        out.push_str(&format!("  $d {} $.\n", bound.join(" ")));
    }
    for one in &free {
        if !bound.is_empty() {
            out.push_str(&format!("  $d {one} {} $.\n", bound.join(" ")));
        }
    }
    let label = work.own_label()?;
    let says = match &antecedent {
        Some(a) => {
            format!("( {} -> {} )", work.kernel_text(a), work.kernel_text(&goal))
        }
        None => work.kernel_text(&goal),
    };
    let mut mandatory: Vec<String> = says
        .split_whitespace()
        .filter_map(|t| work.b.flabel.get(t).map(String::from))
        .collect::<BTreeSet<String>>()
        .into_iter()
        .collect();
    mandatory.sort_by_key(|one| work.b.float_order(one).unwrap_or(usize::MAX));
    out.push_str(&format!("  {label} $p |- {says} $=\n"));
    out.push_str(&format!(
        "    {} $.\n",
        compressed(root, &kinds, &mandatory)
    ));
    out.push_str("$}\n");
    Ok(Elaborated {
        text: out,
        statement: format!("|- {says}"),
        said_back: work.said_back.take().unwrap_or_default(),
    })
}

/// Where a theorem's elaboration stands when its last step is taken
/// (`Elaborator::finish_proof`).
struct Finishing {
    /// The blocks still open.
    blocks: Vec<Block>,
    /// What is still to be applied to the proof, outermost first.
    closers: Vec<Closer>,
    /// The scope the last step sits in.
    scope: Rpn,
    /// What the proof may rest on there.
    facts: Facts,
    /// The theorem's conclusion.
    goal: Rpn,
    /// The theorem's hypotheses.
    terms: Vec<Rpn>,
}

/// A run of a transitivity step's chain, or one of its links: `left`
/// related to `right`, each as set.mm writes it, and its proof.
#[derive(Clone)]
struct ChainRun {
    left: Rpn,
    right: Rpn,
    /// The order, `clt` or `cle`, low side first; None for an equation.
    relation: Option<String>,
    proof: Proof,
}

/// One order link of a calculation's chain, as set.mm writes it: `left`
/// related to `right` by `relation`, `clt` or `cle`, and its proof.
struct OrderLink<'a> {
    left: &'a Rpn,
    right: &'a Rpn,
    relation: &'a str,
    proof: &'a Proof,
}

/// A congruence a ≡ b (mod n), as set.mm writes it, n ∥ (a − b).
struct Congruence {
    modulus: Rpn,
    /// a.
    left: Rpn,
    /// b.
    right: Rpn,
}

/// A chain's proof from `left` to `middle`, an equation or a congruence
/// modulo `modulus`, and its next link from `middle` to `right`, a
/// congruence modulo `modulus`.
struct Joining<'s> {
    modulus: &'s Rpn,
    left: &'s Rpn,
    middle: &'s Rpn,
    right: &'s Rpn,
    /// ( scope -> left = middle ), or the congruence where
    /// `before_congruent`.
    before: Proof,
    before_congruent: bool,
    /// ( scope -> middle ≡ right (mod modulus) ).
    after: Proof,
    /// What the chain's equations made of `left` before its first
    /// congruence, where it began with equations.
    equated: Option<&'s Equated>,
}

/// The term a chain's opening equations reach from its first term, and
/// ( scope -> first = term ): the chain says its first term is a number as
/// that term is (`SYNTAX.md`, a chain that says ≡ relates integers, each
/// one beside one in an equation a link cites).
#[derive(Clone)]
struct Equated {
    term: Rpn,
    proof: Proof,
}

/// A cited theorem read under what a citation gives its letters
/// (`cite_corpus`, and an obtain from a theorem).
pub(super) struct Reading {
    /// Its hypotheses, in order.
    pub(super) wanted: Vec<Rpn>,
    /// Its statement.
    pub(super) whole: Rpn,
    /// Each letter the citation or the match gave a value.
    pub(super) given: Vec<Given>,
}

/// One letter of a cited theorem and what the citation puts for it.
pub(super) struct Given {
    pub(super) name: String,
    /// The class of its own the letter is read as where it is kept apart.
    pub(super) class: Rpn,
    /// What it stands for, in the citing proof's kernel spelling.
    pub(super) term: Rpn,
}

/// What a substitution aims at, and how what it makes there becomes the
/// claim.
enum Toward {
    /// The claim as written.
    Claim,
    /// An equation claimed the other way round, turned by the lemma.
    Turned(&'static str),
    /// The claim in its other form (`rules::OTHER_FORMS`), carried back.
    OtherForm,
}

/// Where what a substitution rewrites and what it makes differ: by the
/// equation, or by the order of a distance's points, which is no
/// difference on the page.
fn substitution_leaf() -> Leaf {
    Leaf::Rows(vec![
        super::tables::Row::Held,
        super::tables::Row::InNoOrder,
    ])
}

/// The statement a written file proves, read off its `$p` line: what a
/// theorem citing it pushes is decided by what that statement binds.
pub fn statement_of(text: &str) -> Option<String> {
    for line in text.lines() {
        if let Some((_, rest)) = line.split_once(" $p ") {
            return Some(
                rest.split_once("$=")
                    .map_or(rest, |(said, _)| said)
                    .to_string(),
            );
        }
    }
    None
}
