//! One theorem of the corpus written as a Lean theorem, step by step.
//!
//! Each step is a `have` whose type is the step's claim and whose proof is
//! what its method is in Lean (`LEAN.md`, "What each method becomes"). A
//! step that owns a block proves its claim by the block's steps, opened by
//! what the block's lines introduce. Tactics see every line above them, as
//! Mathlib's proofs do. A comment above each step says where it stands on
//! the page, and each line written records the step it was written for, so
//! that a line Lean refuses is reported against the page.

use indexmap::IndexMap;

use super::doc::bridges::{BridgeModule, BridgeTactic};
use super::doc::{Tactic, TacticArg};
use super::expr::{LetterType, Printed, Writer};
use super::items::{Item, Sentence};
use super::names::{line_name, snake};
use super::statement::{binders, introduces, Asked, Binder};
use super::templates::Templates;
use crate::checker::record::Cited;
use crate::checker::{CheckedCorpus, CheckedTheorem};
use crate::citing::Way;
use crate::corpus::{Head, Intro, Justification, Method, Step, Theorem};
use crate::formula::page::Written;
use crate::formula::Node;
use crate::notations::{BICONDITIONAL, CONDITIONAL, EQUALITY, IMPLICATION, ORDER};
use crate::outcome::Route;

/// A Lean file, and for each of its lines the place on the page it was
/// written for.
#[derive(Clone, Debug, Default)]
pub struct LeanFile {
    pub text: String,
    pub origins: Vec<Origin>,
    /// Where a citation's item writes a term in another form than the line
    /// it proves.
    pub forms: Vec<FormNote>,
}

/// A citation whose item, read as written, writes a term in another form
/// than the line it proves.
#[derive(Clone, Debug)]
pub struct FormNote {
    /// The line of the proof file the citation is on.
    pub page_line: usize,
    /// The item cited, by its full name.
    pub item: String,
    pub difference: super::doc::forms::FormDifference,
}

/// An item applied to what a citation gives it.
pub struct Instance {
    /// The item's declaration applied to its arguments, with the
    /// projection that takes the sentence: `(Decl (x := v) h).2`.
    pub term: super::expr::Printed,
    /// What it then says: the item's sentence with each letter put for by
    /// the value the citation gives it, to be compared with the line it
    /// proves.
    pub statement: super::expr::Printed,
}

/// A line of a proof as the writer pushes it, which may hold several of the
/// file's lines, and what it was written for; its line number is set where
/// the file is put together.
struct ProofLine {
    /// How deep in the proof's blocks it stands.
    depth: usize,
    tactic: Tactic,
    origin: Origin,
}

impl ProofLine {
    /// The line as Lean text, indented to its depth, each line its tactic
    /// runs over too.
    fn text(&self) -> String {
        let pad = pad(self.depth);
        format!("{pad}{}", indented(&self.tactic.text(), &pad))
    }
}

/// A proof given as an argument, as Lean text: a line's name or `(by
/// parley_side)`.
fn proof_arg(text: &str) -> super::doc::Arg {
    super::doc::Arg::Explicit(super::expr::Printed::atom(text))
}

/// The module a declaration's full name is in, `Parley.Items.Stdlib.Counting`
/// of `Parley.Items.Stdlib.Counting.mun_card_singleton`.
fn module_of_decl(decl: &str) -> String {
    match decl.rsplit_once('.') {
        Some((module, _)) => module.to_string(),
        None => decl.to_string(),
    }
}

/// Where a line of a Lean file comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The line of the Lean file, from 1.
    pub line: usize,
    /// The line of the proof file it was written for.
    pub page_line: usize,
    /// What it was written for.
    pub spot: Spot,
}

/// What a line of a Lean file was written for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spot {
    /// The theorem's statement, or a line of the file around it.
    Statement,
    /// A step, by its number as the page writes it.
    Step(String),
}

/// What writing a theorem reads: the corpus as checked, the notations and
/// items in Lean, and the theorems of the corpus as items in Lean.
pub struct Sources<'a> {
    pub checked: &'a CheckedCorpus,
    pub templates: &'a Templates,
    /// What each notation is to the methods' decisions, which `algebra`
    /// asks for its multipliers.
    pub targets: &'a crate::methods::terms::Targets,
    /// Every item a citation may name that has a Lean form, by full name:
    /// the library's records and the corpus's theorems.
    pub items: &'a IndexMap<String, Item>,
    /// What the checker matches terms with, its identity elements among
    /// them, so that a step is read as the checker decided it.
    pub ctx: &'a crate::matching::Context,
}

/// The terms a theorem puts in a hole of type ℝ, the A/B of ⌊A/B⌋ (set.mm's
/// floor being of reals), as the page prints them: each is a real wherever
/// the theorem writes it, so that a line about it meets the floor's.
fn held_real(rec: &CheckedTheorem, writer: &Writer) -> Vec<String> {
    let mut out = Vec::new();
    for (_, node) in rec.page.entries() {
        for n in node.walk() {
            // A letter has its own type; a term of numerals alone, the 2 of
            // √2, takes the type of where it stands.
            for arg in writer.always_real_args(&n) {
                let printed = writer.grammar.print(arg);
                let of_letters = arg.walk().iter().any(|m| m.is_name());
                if !arg.is_name() && of_letters && !out.contains(&printed) {
                    out.push(printed);
                }
            }
        }
    }
    out
}

/// Why a function a proof defines whose values are sets, I(k) = {|x| : x ∈
/// 𝒫{1, …, k}}, is not written: the writer types a function letter as one
/// into numbers only.
pub const SET_VALUED: &str = "a function a proof defines whose values are sets";

/// Whether the checker reads the name a proof defines as a function whose
/// values are sets.
pub fn set_valued(rec: &CheckedTheorem, name: &str) -> bool {
    matches!(
        rec.sorts.get(name).and_then(|s| s.full()),
        Some(crate::formula::Whole::Function(_, to))
            if matches!(**to, crate::formula::Whole::Set(_))
    )
}

/// The theorem as the checker read it with each function its file defines
/// outside it written out where it is applied, T(k + 1) of `define T(k) :=
/// k(k + 1)/2` as (k + 1)(k + 2)/2, as the Metamath build reads it
/// (`elab::reading`): Lean has no name for such a function, and set.mm's
/// statement never names one. Unchanged where the file defines none.
pub fn outside_written<'r>(
    checked: &CheckedCorpus,
    thm: &Theorem,
    rec: &'r CheckedTheorem,
) -> std::borrow::Cow<'r, CheckedTheorem> {
    let rules: crate::matching::Definitions = rec
        .outside
        .iter()
        .filter(|(_, d)| matches!(d, crate::matching::Defined::Rule(_)))
        .map(|(n, d)| (n.clone(), d.clone()))
        .collect();
    let phrases = phrase_meanings(checked, rec);
    let written_page = rec
        .page
        .entries()
        .flat_map(|(_, n)| n.walk())
        .any(|n| phrases.contains_key(&n.notation()));
    if rules.is_empty() && !written_page {
        return std::borrow::Cow::Borrowed(rec);
    }
    let out = |n: &Node| {
        let n = crate::matching::expand(n, &rules);
        phrases_written(&n, &phrases, &checked.grammar, 8)
    };
    let binding = |b: &crate::matching::Binding| -> crate::matching::Binding {
        b.iter().map(|(k, v)| (*k, out(v))).collect()
    };
    let mut written = rec.clone();
    written.page = crate::checker::record::PageReading::new(
        rec.page
            .entries()
            .map(|(k, n)| (k.clone(), out(n)))
            .collect(),
    );
    written.asserted = rec
        .asserted
        .iter()
        .map(|line| line.iter().map(out).collect())
        .collect();
    for c in written.cited.iter_mut().flatten() {
        c.binding = binding(&c.binding);
    }
    for c in written.cited_requires.values_mut() {
        c.binding = binding(&c.binding);
    }
    for all in written.exhibited.values_mut() {
        for b in all.iter_mut().flatten() {
            *b = binding(b);
        }
    }
    // The sets the page makes finite, read of the page as written here: a
    // letter bound in a define written out, the c of {c ∈ 𝒫{1, …, k} : …},
    // is one the page as read does not bind.
    written.said_finite = crate::checker::finite_of(&checked.grammar, thm, &written);
    written.set_systems = crate::checker::set_systems_of(&written);
    std::borrow::Cow::Owned(written)
}

/// A phrase a define gives, `c is a counting ahead through k`: its slots
/// and what it means, from the definition record the define stands for,
/// whose statement is the phrase, `↔`, and the meaning.
pub(super) struct Phrase {
    slots: Vec<crate::formula::symbol::Symbol>,
    meaning: Node,
}

/// Each phrase the library's phrase defines give, by its notation, read
/// from the definition records' own groups, for the items that state one.
pub(super) fn library_phrases(
    checked: &CheckedCorpus,
) -> IndexMap<crate::formula::notation_id::NotationId, Phrase> {
    let mut out = IndexMap::new();
    let made = checked.corpus.records.iter().filter(|r| {
        r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
    });
    for r in made {
        let full = format!("{}/{}", r.module(), r.name);
        let Some(Some(groups)) = checked.library.groups.get(&full) else {
            continue;
        };
        for read in groups.iter().flat_map(|g| &g.gives) {
            let [phrase, meaning] = read.children.as_slice() else {
                continue;
            };
            if read.notation() != crate::notations::BICONDITIONAL
                || !phrase.children.iter().all(Node::is_name)
            {
                continue;
            }
            out.insert(
                phrase.notation(),
                Phrase {
                    slots: phrase.children.iter().map(|c| c.text).collect(),
                    meaning: meaning.clone(),
                },
            );
        }
    }
    out
}

/// An item's group with each phrase in it written out as its meaning, as a
/// theorem's page is (`outside_written`).
pub(super) fn group_written(
    group: &crate::citing::Group,
    phrases: &IndexMap<crate::formula::notation_id::NotationId, Phrase>,
    grammar: &crate::formula::Grammar,
) -> crate::citing::Group {
    let out = |n: &Node| phrases_written(n, phrases, grammar, 8);
    crate::citing::Group {
        wants: group
            .wants
            .iter()
            .map(|(text, n)| (text.clone(), out(n)))
            .collect(),
        gives: group.gives.iter().map(out).collect(),
        functions: group.functions.clone(),
        identities: group.identities.clone(),
    }
}

/// Each phrase a theorem can read, by its notation, as the Metamath build
/// reads it (`Elaborator::phrase_meanings`).
fn phrase_meanings(
    checked: &CheckedCorpus,
    rec: &CheckedTheorem,
) -> IndexMap<crate::formula::notation_id::NotationId, Phrase> {
    let mut out = IndexMap::new();
    let made = checked.corpus.records.iter().filter(|r| {
        r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
    });
    for r in made {
        for written in r.stated() {
            let Ok(sentence) = written.formula() else {
                continue;
            };
            let Some(Ok(read)) = rec.items.get(&sentence) else {
                continue;
            };
            let [phrase, meaning] = read.children.as_slice() else {
                continue;
            };
            if read.notation() != crate::notations::BICONDITIONAL
                || !phrase.children.iter().all(Node::is_name)
            {
                continue;
            }
            out.insert(
                phrase.notation(),
                Phrase {
                    slots: phrase.children.iter().map(|c| c.text).collect(),
                    meaning: meaning.clone(),
                },
            );
        }
    }
    out
}

/// The tree with each phrase written out as its meaning at what fills its
/// slots, the meaning's own letters kept apart from what is put in.
fn phrases_written(
    node: &Node,
    phrases: &IndexMap<crate::formula::notation_id::NotationId, Phrase>,
    grammar: &crate::formula::Grammar,
    depth: usize,
) -> Node {
    if depth == 0 {
        return node.clone();
    }
    if let Some(p) = phrases.get(&node.notation()) {
        if p.slots.len() == node.children.len() {
            let put: crate::matching::Binding = p
                .slots
                .iter()
                .copied()
                .zip(node.children.iter().cloned())
                .collect();
            let at = crate::matching::substitute_apart_by(
                &p.meaning,
                &put,
                &grammar.binders(),
            );
            return phrases_written(&at, phrases, grammar, depth - 1);
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| phrases_written(c, phrases, grammar, depth))
            .collect(),
    )
}

/// The theorem as an item of the library: its statement's binders, and its
/// `then` sentences joined into one Lean statement, each taken by its
/// projection.
pub fn as_item(sources: &Sources, thm: &Theorem, rec: &CheckedTheorem) -> Route<Item> {
    let written = outside_written(sources.checked, thm, rec);
    let rec: &CheckedTheorem = &written;
    let mut writer = Writer::new(&sources.checked.grammar, sources.templates);
    writer.reals = held_real(rec, &writer);
    writer.finite_from(&rec.said_finite);
    writer.bounds_from(&crate::checker::hypothesis_lines(thm, rec));
    let stated = match statement(&mut writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    let module = super::names::module_of(&thm.qualified());
    let decl = format!("{module}.{}", snake(&thm.name));
    let n = stated.conclusion.len();
    let mut written: Vec<Node> = hypothesis_sentences(thm, rec)
        .into_iter()
        .flat_map(|(_, s)| s.into_iter().map(|(node, _)| node))
        .collect();
    written.extend(stated.conclusion.iter().map(|c| c.says.clone()));
    let mut arithmetic = super::readback::page_arithmetic(&writer, &written);
    for (op, n) in recursion_arithmetic(&writer, thm, rec) {
        *arithmetic.entry(op).or_insert(0) += n;
    }
    let sentences = stated
        .conclusion
        .into_iter()
        .enumerate()
        .map(|(i, c)| Sentence {
            decl: decl.clone(),
            binders: stated.binders.clone(),
            says: c.says,
            prop: c.prop,
            part: projection(i, n),
            arithmetic: arithmetic.clone(),
            general: None,
            domains: writer.domains.clone(),
        })
        .collect();
    Route::Built(Item {
        module,
        sentences,
        proofs: Vec::new(),
    })
}

/// The parts of an "and" as its tree nests them, in order: ((A ∧ B) ∧ C)
/// gives A, B, C; anything else is one part.
fn and_parts(node: &Node) -> Vec<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let mut out = and_parts(l);
            out.extend(and_parts(r));
            out
        }
        _ => vec![node],
    }
}

/// The projection that takes part `i` of an "and" as its tree nests it,
/// `.1.2` for B of ((A ∧ B) ∧ C); None where it has no part `i`.
fn leaf_path(node: &Node, i: usize) -> Option<String> {
    match (node.notation(), node.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let left = and_parts(l).len();
            if i < left {
                leaf_path(l, i).map(|p| format!(".1{p}"))
            } else {
                leaf_path(r, i - left).map(|p| format!(".2{p}"))
            }
        }
        _ => (i == 0).then(String::new),
    }
}

/// The projection that takes sentence `i` of `n` joined by `∧`, which
/// chains to the right: `.1`, `.2.1`, …, and the last `.2.2…`.
fn projection(i: usize, n: usize) -> String {
    if n == 1 {
        return String::new();
    }
    let mut out = ".2".repeat(i);
    if i + 1 < n {
        out.push_str(".1");
    }
    out
}

/// Each `let` and `assume` line of a theorem, by its label, with each of
/// its sentences and the Lean name of the hypothesis it is: the label, or
/// `H3a`, `H3b` for a line of several sentences.
fn hypothesis_sentences(
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Vec<(String, Vec<(Node, String)>)> {
    let mut out = Vec::new();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
        let mut nodes: Vec<Node> = h
            .body(&thm.path)
            .sentences()
            .iter()
            .filter_map(|s| rec.page.get(s).cloned())
            .collect();
        // A `let` the page does not read as a formula, `f : A → B be
        // one-to-one`, says what the checker reads it to assert.
        if nodes.is_empty() {
            nodes = rec.asserted.get(i).cloned().unwrap_or_default();
        }
        let base = line_name(&label);
        let n = nodes.len();
        let said = nodes
            .into_iter()
            .enumerate()
            .map(|(k, node)| {
                let name = if n == 1 {
                    base.clone()
                } else {
                    format!("{base}{}", (b'a' + k as u8) as char)
                };
                (node, name)
            })
            .collect();
        out.push((label, said));
    }
    out
}

/// A tree of the statement with each name a define of it, or of its file,
/// gives written out as the term it names, as the checker reads the
/// statement (`CheckedTheorem::statement_definitions`).
fn defined_out(node: &Node, rec: &CheckedTheorem, writer: &Writer) -> Node {
    let put: crate::matching::Binding = rec
        .statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => {
                Some((crate::formula::symbol::Symbol::of(name), t.clone()))
            }
            crate::matching::Defined::Rule(_) => None,
        })
        .collect();
    if put.is_empty() {
        return node.clone();
    }
    crate::matching::substitute_apart_by(node, &put, &writer.grammar.binders())
}

/// The defines a theorem's statement is read with, each a name and the term
/// it stands for, in the order defined.
fn statement_terms(rec: &CheckedTheorem) -> Vec<(String, Node)> {
    rec.statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => Some((name.clone(), t.clone())),
            crate::matching::Defined::Rule(_) => None,
        })
        .collect()
}

/// What a citation gives an item's things (`Proof::things_given`).
#[derive(Default)]
struct ThingsGiven {
    /// The least type that holds the numbers given each type variable's
    /// things, by the variable.
    at: std::collections::BTreeMap<usize, super::templates::Num>,
    /// The type variables whose sets are given sets of numbers, X := {2n :
    /// n ∈ ℤ}.
    numbers: std::collections::BTreeSet<usize>,
    /// What the members are of a set given for each type variable's set
    /// where they are not numbers, sets of integers of X := {e ⊆ {1, …, m}
    /// : |e| = m}.
    others: std::collections::BTreeMap<usize, super::expr::Members>,
}

impl ThingsGiven {
    /// What an item's members are here, its things given numbers or sets
    /// put for them at any depth: a property of sets of α, given sets of
    /// integers, is one of `Set ℤ`. `at` is the type each variable's
    /// numbers are taken at.
    fn put(
        &self,
        members: &super::expr::Members,
        at: &dyn Fn(&usize) -> super::templates::Num,
    ) -> super::expr::Members {
        use super::expr::Members;
        match members {
            Members::Things(var) if self.numbers.contains(var) => {
                Members::Numbers(at(var))
            }
            Members::Things(var) if self.others.contains_key(var) => {
                self.others[var].clone()
            }
            Members::Sets(inner) => Members::Sets(Box::new(self.put(inner, at))),
            other => other.clone(),
        }
    }

    fn raise(&mut self, var: usize, n: super::templates::Num) {
        let at = self.at.entry(var).or_insert(n);
        *at = (*at).max(n);
    }
}

/// What a theorem states, in Lean.
struct Statement {
    /// Its binders, from its `let` and `assume` lines.
    binders: Vec<Binder>,
    /// Each sentence of its `then` line.
    conclusion: Vec<Concluded>,
}

/// One sentence a theorem concludes: its tree, and its Lean text.
struct Concluded {
    says: Node,
    prop: Printed,
}

/// The number type of `let A be an element` where later lines say A is in
/// sets of numbers, A ∈ ℝ ∖ ℚ: the widest of those sets' types. None where
/// no line puts A in a set of numbers.
fn element_number_type(
    name: &str,
    rec: &CheckedTheorem,
    writer: &Writer,
) -> Option<LetterType> {
    rec.page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter_map(|n| match n.children.as_slice() {
            [x, set]
                if n.notation() == crate::notations::MEMBERSHIP
                    && x.is_name()
                    && *x.text == *name =>
            {
                match writer.set_members(set)? {
                    super::expr::Members::Numbers(at) => Some(at),
                    _ => None,
                }
            }
            _ => None,
        })
        .max()
        .map(LetterType::Number)
}

/// The type of `let T be a set` where T is a set of numbers the checker
/// records the system of, T of {1, …, i} ∩ T or D of D ⊆ ℝ
/// (`CheckedTheorem::set_systems`): a set of those. None where it records
/// none.
fn recorded_number_set_type(name: &str, rec: &CheckedTheorem) -> Option<LetterType> {
    let system = rec.set_systems.get(name)?;
    Some(LetterType::Set(super::expr::Members::Numbers(
        super::expr::recorded_set_type(*system),
    )))
}

/// A theorem's binders, from its `let` and `assume` lines, and each
/// sentence of its `then` line with its Lean text.
/// A function the header lets by its value, `let f(x) = 2x + 1, for x ∈ ℝ`:
/// as the page reads a let, a letter of the type the value computes in,
/// taking the domain's numbers (integers for ℕ, ℕ₀ or a range, as the
/// writer's sequences do), and the equation for every x as one hypothesis
/// named by the label.
fn header_function(
    writer: &mut Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let read: Vec<&Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == d.line)
        .map(|(_, node)| node)
        .collect();
    let over = |n: &&&Node| {
        matches!(
            n.notation(),
            crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
        )
    };
    // The domain: a number system or range written in the line, or a set,
    // a letter or a set the header itself defines, written out.
    let domain = match read.iter().find(over) {
        Some(n) => (**n).clone(),
        None => {
            let sets: Vec<&&Node> = read
                .iter()
                .filter(|n| !(n.is_name() && *n.text == *param.name))
                .filter(|n| {
                    let out = defined_out(n, rec, writer);
                    writer.set_members(&out).is_some()
                })
                .collect();
            match sets.as_slice() {
                [one] => defined_out(one, rec, writer),
                _ => {
                    return Route::no(
                        "a function the header lets on no set Lean has a type for",
                    )
                }
            }
        }
    };
    let bodies: Vec<&&Node> = read
        .iter()
        .filter(|n| !over(n))
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        .filter(|n| writer.set_members(&defined_out(n, rec, writer)).is_none())
        .collect();
    let [body] = bodies.as_slice() else {
        return Route::no(
            "a function the header lets whose value did not read as one term",
        );
    };
    // What it takes: the domain's numbers, integers for ℕ, ℕ₀ or a range
    // as the writer's sequences take; or the things of a set of things.
    let takes = match super::expr::system_of(&domain) {
        Some(system) => super::expr::Members::Numbers(
            super::expr::letter_type(system).max(Num::Int),
        ),
        None if domain.notation() == crate::notations::INTEGER_RANGE => {
            super::expr::Members::Numbers(Num::Int)
        }
        None => match writer.set_members(&domain) {
            Some(m) => m,
            None => {
                return Route::no(
                    "a function the header lets on no set Lean has a type for",
                )
            }
        },
    };
    let before = writer.letters.insert(param.name.clone(), takes.letter());
    // Said for every x of the domain: all of a type, or each member of a
    // set, x ∈ D, as the writer writes that membership.
    let whole_type = matches!(
        super::expr::system_of(&domain),
        Some(super::expr::System::Type(_))
    );
    let x = Node::name(crate::formula::Sort::none(), &param.name);
    let member = Node::of(
        crate::notations::IN,
        crate::formula::Sort::none(),
        vec![x, domain.clone()],
    );
    let guard = match whole_type {
        true => Route::Built(None),
        false => writer.formula(&member).map(|p| Some(p.text())),
    };
    // The value is read where x is in the domain: √x of x ∈ {y ∈ ℝ : y >
    // 0} the real square root.
    let inside = writer.knowing(std::slice::from_ref(&member));
    // A function of a real or complex argument gives values of at least
    // that type, as continuity and derivatives read it: a step of 0 and 1
    // on [0, 1] is a function into ℝ.
    let value = match &takes {
        super::expr::Members::Numbers(from) => match inside.carrier(body) {
            Route::Built(to) => {
                let to = match *from >= Num::Real {
                    true => to.max(*from),
                    false => to,
                };
                inside
                    .number_fixed(body, to)
                    .map(|v| (LetterType::Function { from: *from, to }, v))
            }
            Route::Declined(why) => Route::Declined(why),
        },
        m => match writer.member_kind(body) {
            Some(to) => writer.set_term(body).map(|v| {
                (
                    LetterType::Map {
                        from: m.clone(),
                        to,
                    },
                    v,
                )
            }),
            None => {
                Route::no("a function the header lets whose value has no Lean type")
            }
        },
    };
    match before {
        Some(ty) => writer.letters.insert(param.name.clone(), ty),
        None => writer.letters.shift_remove(&param.name),
    };
    let ((ty, value), guard) = match (value, guard) {
        (Route::Built(v), Route::Built(g)) => (v, g),
        (Route::Declined(why), _) | (_, Route::Declined(why)) => {
            return Route::Declined(why)
        }
    };
    writer.letters.insert(def.name.clone(), ty.clone());
    // On a set, D ∖ {c}: that set is its domain, within which its images,
    // preimages and limits are taken (`domain_of`).
    if !whole_type {
        let written = match &takes {
            super::expr::Members::Numbers(n) => writer.numbers_at(&domain, *n),
            _ => writer.set_term(&domain),
        };
        match written {
            Route::Built(p) => {
                writer.domains.insert(def.name.clone(), p);
            }
            Route::Declined(why) => return Route::Declined(why),
        }
    }
    let f = super::names::letter(&def.name);
    let x = super::names::letter(&param.name);
    let guard = guard.map_or(String::new(), |g| format!("{g} → "));
    Route::Built(vec![
        Binder::Letter {
            name: f.clone(),
            page: def.name.clone(),
            general: false,
            ty,
        },
        Binder::Fact {
            name: line_name(&d.label),
            says: super::expr::Printed::notation(
                vec![
                    super::doc::Piece::text(format!(
                        "∀ {x} : {}, {guard}{f} {x} = ",
                        takes.lean()
                    )),
                    super::doc::Piece::term(value, 51),
                ],
                0,
                super::doc::LeanType::Prop,
            ),
            line: None,
        },
    ])
}

/// One function's rules of a recursion, as the checker read them: its name,
/// its value at 0, and its value at k + 1.
struct RecursionRule<'r> {
    name: &'r String,
    start: Node,
    step: Node,
}

/// Each function's rules of a recursion, as the checker read them.
fn recursion_rules<'r>(
    r: &'r crate::corpus::Recursion,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Route<Vec<RecursionRule<'r>>> {
    let mut out = Vec::new();
    for name in &r.names {
        let (Some(start), Some(step)) = (
            r.start.get(name).and_then(|rule| rule_tree(rule, d, rec)),
            r.step.get(name).and_then(|rule| rule_tree(rule, d, rec)),
        ) else {
            return Route::no(format!(
                "a recursion whose rules for {name} did not read"
            ));
        };
        out.push(RecursionRule { name, start, step });
    }
    Route::Built(out)
}

/// A rule of a recursion as the checker read it; None where it read none.
fn rule_tree(
    rule: &crate::corpus::RuleText,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Option<Node> {
    match rule.written(&d.path, d.line).sentences().as_slice() {
        [one] => rec.page.get(one).cloned(),
        _ => None,
    }
}

/// The arithmetic the page writes in the recursions a theorem's header
/// lets, as their hypothesis states them (`header_recursions`): each rule's
/// value, and the k + 1 each function is applied to in its step.
fn recursion_arithmetic(
    writer: &Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> std::collections::BTreeMap<String, usize> {
    let mut out = std::collections::BTreeMap::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value: the value, which its
            // hypothesis states (`header_function`).
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                let values: Vec<Node> = rec
                    .page
                    .entries()
                    .filter(|(key, _)| key.line == d.line)
                    .map(|(_, n)| n.clone())
                    .filter(|n| {
                        !matches!(
                            n.notation(),
                            crate::notations::NUMBER_SYSTEMS
                                | crate::notations::INTEGER_RANGE
                        )
                    })
                    .filter(|n| !n.is_name())
                    .collect();
                for (op, n) in super::readback::page_arithmetic(writer, &values) {
                    *out.entry(op).or_insert(0) += n;
                }
                continue;
            }
            _ => continue,
        };
        let Route::Built(rules) = recursion_rules(&r, d, rec) else {
            continue;
        };
        let values: Vec<Node> = rules
            .iter()
            .flat_map(|rule| [rule.start.clone(), rule.step.clone()])
            .collect();
        for (op, n) in super::readback::page_arithmetic(writer, &values) {
            *out.entry(op).or_insert(0) += n;
        }
        *out.entry("addition".to_string()).or_insert(0) += rules.len();
    }
    out
}

/// The recursions a theorem's header lets,
/// `let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`:
/// as the page reads a let,
/// letters for its functions, of ℤ into the type its rules compute in, and
/// its rules one hypothesis named by its label, its step for k ≥ 0. Of
/// every pair F, G the rules hold of, which agree from 0 on, the theorem
/// says what it says of the Fibonacci numbers. A recursion from 1, over ℕ,
/// is declined.
fn header_recursions(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::templates::Num;
    let mut out = Vec::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value, f(x) = 2x + 1, for x
            // ∈ ℝ: a function letter, and that equation for every x.
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                match header_function(writer, d, &one, rec) {
                    Route::Built(b) => {
                        out.extend(b);
                        continue;
                    }
                    Route::Declined(why) => return Route::Declined(why),
                }
            }
            _ => continue,
        };
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(&r, d, rec) {
            Route::Built(rules) => rules,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The functions take integers, as the writer's sequences do, so
        // that F(k) of a sum's index is written as it stands; the rules say
        // what they are from 0. What they give is the type their rules
        // compute in, an integer at least.
        let index = r.index.clone();
        let before = writer
            .letters
            .insert(index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        for rule in &rules {
            for n in [&rule.start, &rule.step] {
                match writer.carrier(n) {
                    Route::Built(c) => to = to.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        let k = super::names::letter(&index);
        let mut starts = Vec::new();
        let mut steps = Vec::new();
        for rule in &rules {
            let f = super::names::letter(rule.name);
            let (s, t) = match (
                writer.number_fixed(&rule.start, to),
                writer.number_fixed(&rule.step, to),
            ) {
                (Route::Built(s), Route::Built(t)) => (s, t),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
            starts.push(format!("{f} 0 = {}", s.at(51)));
            steps.push(format!("{f} ({k} + 1) = {}", t.at(51)));
        }
        match before {
            Some(ty) => writer.letters.insert(index.clone(), ty),
            None => writer.letters.shift_remove(&index),
        };
        for name in &r.names {
            out.push(Binder::Letter {
                name: super::names::letter(name),
                page: name.clone(),
                general: false,
                ty: LetterType::Function { from: Num::Int, to },
            });
        }
        out.push(Binder::Fact {
            name: line_name(&d.label),
            says: super::expr::Printed::raw(
                format!(
                    "{} ∧ ∀ {k} : ℤ, 0 ≤ {k} → {}",
                    starts.join(" ∧ "),
                    steps.join(" ∧ ")
                ),
                0,
            ),
            line: None,
        });
    }
    Route::Built(out)
}

/// Hypothesis sentences, each its tree and its Lean name, as `binders`
/// takes them.
fn asked_of(written: &[(Node, String)]) -> Vec<Asked<'_>> {
    written
        .iter()
        .map(|(node, name)| Asked {
            node,
            name: name.clone(),
        })
        .collect()
}

fn statement(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Statement> {
    let said = hypothesis_sentences(thm, rec);
    // A `let` that is no formula, `A be a set` or `x be an element`, gives
    // its letter the type its sort settles, ahead of the lines that use it.
    let mut binders_of_sets = Vec::new();
    let mut read: usize = said.iter().map(|(_, s)| s.len()).sum();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let body = h.body(&thm.path);
        if body.sentences().iter().all(|s| rec.page.get(s).is_some()) {
            continue;
        }
        use crate::sorts::introduction::{Form, Introduction};
        let name = match Introduction::read(body.clone()).form {
            Form::Set(name)
            | Form::Element(name)
            | Form::Property { name, .. }
            | Form::FunctionOn { name, .. } => name,
            // `let G be a group with operation · and identity e`: the type
            // of its elements with Mathlib's group on it, and e its 1. What
            // else the line asserts, that G is finite, is among `said`.
            Form::Group {
                group, identity, ..
            } => {
                writer.letters.insert(group.clone(), LetterType::Group);
                writer
                    .letters
                    .insert(identity, LetterType::Identity(group.clone()));
                binders_of_sets.push(Binder::Letter {
                    name: super::names::letter(&group),
                    page: group,
                    general: false,
                    ty: LetterType::Group,
                });
                if rec.asserted.get(i).is_none_or(Vec::is_empty) {
                    read += body.sentences().len();
                }
                continue;
            }
            _ => continue,
        };
        // An element nothing settles a sort of, `let B be an element` of a
        // B only listed, {B}, is a thing.
        let unsorted_element =
            matches!(Introduction::read(body.clone()).form, Form::Element(_))
                && rec.sorts.get(&name).is_none();
        let Some(ty) = rec
            .sorts
            .get(&name)
            .and_then(super::sets::set_letter_type)
            .or_else(|| element_number_type(&name, rec, writer))
            .or_else(|| recorded_number_set_type(&name, rec))
            .or_else(|| {
                unsorted_element
                    .then_some(LetterType::Member(super::expr::Members::Things(0)))
            })
        else {
            continue;
        };
        writer.letters.insert(name.clone(), ty.clone());
        binders_of_sets.push(Binder::Letter {
            name: super::names::letter(&name),
            page: name,
            general: false,
            ty,
        });
        // A line that asserts something of its letter, F is a function on
        // A, is read among `said` already.
        if rec.asserted.get(i).is_none_or(Vec::is_empty) {
            read += body.sentences().len();
        }
    }
    let written: usize = thm
        .hypotheses
        .iter()
        .map(|h| h.body(&thm.path).sentences().len())
        .sum();
    if read != written {
        return Route::no("a hypothesis the checker did not read");
    }
    // A define the statement is read with is written out in it: Lean's
    // statement says what the name stands for, and the proof names it again
    // (`theorem`, `set`).
    // The hypotheses above a recursion or function the header lets are
    // read before it, as its rules may use their letters, F(0) = M; those
    // below after it, as they may use its functions.
    let recursion_line = thm
        .defines
        .iter()
        .filter(|d| d.line < thm.conclusion_line)
        .filter(|d| match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        })
        .map(|d| d.line)
        .min();
    let above = |label: &str| {
        let line = thm
            .hypotheses
            .iter()
            .find(|h| h.label.as_deref() == Some(label))
            .map(|h| h.line);
        match (recursion_line, line) {
            (Some(r), Some(l)) => l < r,
            _ => true,
        }
    };
    let mut written_above: Vec<(Node, String)> = Vec::new();
    let mut written_below: Vec<(Node, String)> = Vec::new();
    for (label, s) in &said {
        let into = match above(label) {
            true => &mut written_above,
            false => &mut written_below,
        };
        for (node, name) in s {
            into.push((defined_out(node, rec, writer), name.clone()));
        }
    }
    let first = match binders(writer, &asked_of(&written_above), &[]) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let recursions = match header_recursions(writer, thm, rec) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let binders = match binders(writer, &asked_of(&written_below), &[]) {
        Route::Built(b) => binders_of_sets
            .into_iter()
            .chain(first)
            .chain(recursions)
            .chain(b)
            .collect::<Vec<_>>(),
        Route::Declined(d) => return Route::Declined(d),
    };
    let mut conclusion = Vec::new();
    for s in thm.stated().sentences() {
        let Some(node) = rec.page.get(&s) else {
            return Route::no(format!("{}, which the checker did not read", s.text()));
        };
        let node = &defined_out(node, rec, writer);
        let prop = match writer.formula(node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        conclusion.push(Concluded {
            says: node.clone(),
            prop,
        });
    }
    Route::Built(Statement {
        binders,
        conclusion,
    })
}

/// Where a step takes its counts in ℕ∞ to integers (`Proof::count_conversion`).
enum CountConversion {
    /// Nowhere: its lines say their counts one way.
    None,
    /// Before its tactic, the goal and the lines in scope.
    Before,
    /// After its tactic, what it built and the goal together.
    After,
}

/// How a step's lines say their counts (`Proof::count_forms`).
struct CountForms {
    /// One says a count in ℕ∞.
    extended: bool,
    /// One set's count is said both in ℕ∞ and as an integer.
    mixed: bool,
}

/// How one set's count is said across a step's lines.
#[derive(Default)]
struct CountSaid {
    /// In ℕ∞, somewhere.
    extended: bool,
    /// As an integer, somewhere.
    integer: bool,
}

/// Writes one theorem's proof.
struct Proof<'a> {
    sources: &'a Sources<'a>,
    thm: &'a Theorem,
    rec: &'a CheckedTheorem,
    writer: Writer<'a>,
    /// The proof's lines in order, each with what it was written for.
    lines: Vec<ProofLine>,
    /// The Lean names of each line the page can cite, by the reference
    /// that cites it: a step's number or a label.
    named: IndexMap<String, Vec<String>>,
    /// What each line the page can cite says, sentence by sentence, with
    /// the Lean name of each sentence's proof, by the reference that cites
    /// it.
    trees: IndexMap<String, Vec<(Node, String)>>,
    /// The defines written so far, by their index in the theorem's.
    defined: indexmap::IndexSet<usize>,
    /// While a calculation's rows are written, the type it is worked out
    /// in: a row's claim alone, Σ j² = 1², may hold in a narrower type than
    /// the calculation's ℚ, which a citation in the row is applied at.
    worked_in: std::cell::Cell<Option<super::templates::Num>>,
    /// The lines whose numbers a citation was given while its step was
    /// written, A/B of `A/B ∈ ℤ`, which the step's goal is put in terms of.
    said_used: std::cell::RefCell<Vec<SaidUsed>>,
    /// Where a citation's item, read as written, writes a term in another
    /// form than the line it proves (`doc::forms`).
    forms: std::cell::RefCell<Vec<FormNote>>,
    /// While a step that names whole numbers is written
    /// (`proof_with_named`), the equations of each with its term: what a
    /// row citing a line in the page's forms is put in terms of.
    named_specs: Vec<String>,
    /// The labels of the defines that name the number their reason shows,
    /// `let e = p/d, a positive integer` (`kinded_witness`): their equation
    /// is a line about an obtained number, cited as any line is, not a
    /// `set` written out.
    witnessed: std::collections::BTreeSet<String>,
    /// Each such define's value, m/p, and the letter that names the number,
    /// r: a citation given the value, as the checker reads one from the
    /// define's fact `m/p ∈ ℕ`, is given the letter.
    witness_letters: Vec<WitnessLetter>,
}

/// The fact a define of a kind says of its value, as `Proof::kind_shown`
/// reads it.
struct KindShown {
    /// The fact, `gcd(t, w) ∈ ℕ`.
    fact: Node,
    /// The fact in Lean.
    says: Printed,
    /// Its proof by the define's reason.
    proof: String,
}

/// A whole number a step names for a term Lean does not compute as one,
/// 2^(p − 1): the `have` that names it, and the term written as it.
struct NamedAtom {
    have: String,
    said: super::expr::SaidInteger,
}

/// A line a step names that puts a term in a number system, `p − 1 ∈ ℕ₀`:
/// its Lean name and the system it says.
struct StatedLine {
    name: String,
    system: crate::rules::System,
}

/// The line among `facts` that puts the term `t` in `within` or a system
/// inside it, `p − 1 ∈ ℕ₀` asked of ℕ₀; None where none does.
fn stated_line(
    facts: &[super::algebra::Cited],
    t: &Node,
    within: crate::rules::System,
    ctx: &crate::matching::Context,
) -> Option<StatedLine> {
    facts.iter().find_map(|f| {
        let [x, set] = f.node.children.as_slice() else {
            return None;
        };
        let system = crate::rules::System::of_sign(&set.text)?;
        (f.node.notation() == crate::notations::MEMBERSHIP
            && set.notation() == crate::notations::NUMBER_SYSTEMS
            && crate::matching::alike_top(x, t, ctx)
            && system.within(within))
        .then(|| StatedLine {
            name: f.proof.clone(),
            system,
        })
    })
}

/// A line a step cites in the witness form, `∃ m : ℤ, ↑m = t ∧ P m`, or its
/// negation, which the step restates of the number it names for t.
struct CitedWitness {
    /// The line's Lean name.
    name: String,
    /// The term t the witness stands for.
    term: Node,
    /// The type the witness is in, ℤ or ℕ.
    whole: super::templates::Num,
    /// Whether the line says no whole number is t with P.
    negated: bool,
}

/// A define that names the number its reason shows its value is.
struct WitnessLetter {
    /// The value, m/p.
    value: Node,
    /// The letter, r.
    letter: Node,
}

/// A line whose number a citation was given: its Lean name, and the term
/// it says is in ℤ or ℚ as the page prints it.
struct SaidUsed {
    line: String,
    term: String,
}

/// A recursion the header lets, as a step cites it.
struct CitedRecursion {
    rule: crate::corpus::Recursion,
    /// The Lean name of its hypothesis, `hD1`.
    hypothesis: String,
    /// Whether a rule of it is by cases, F(k) if b(k) = 0, G(k) otherwise.
    by_cases: bool,
}

/// The theorem written as a Lean file's declaration: its statement and its
/// proof, with an origin for every line, counted from the first line of
/// the declaration.
pub fn theorem(
    sources: &Sources,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<LeanFile> {
    let written = outside_written(sources.checked, thm, rec);
    let rec: &CheckedTheorem = &written;
    let mut proof = Proof {
        sources,
        thm,
        rec,
        writer: Writer::new(&sources.checked.grammar, sources.templates),
        lines: Vec::new(),
        named: IndexMap::new(),
        trees: IndexMap::new(),
        defined: indexmap::IndexSet::new(),
        worked_in: std::cell::Cell::new(None),
        said_used: std::cell::RefCell::new(Vec::new()),
        forms: std::cell::RefCell::new(Vec::new()),
        named_specs: Vec::new(),
        witnessed: std::collections::BTreeSet::new(),
        witness_letters: Vec::new(),
    };
    proof.writer.reals = held_real(rec, &proof.writer);
    proof.writer.finite_from(&rec.said_finite);
    proof
        .writer
        .bounds_from(&crate::checker::hypothesis_lines(thm, rec));
    let Statement {
        binders,
        conclusion,
    } = match statement(&mut proof.writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    // A hypothesis Lean's types give, M ∈ ℕ₀ of a natural M, has no binder
    // and is no line in Lean: a step that uses it has the type.
    let bound: std::collections::BTreeSet<&str> =
        binders.iter().map(Binder::name).collect();
    for (label, said) in hypothesis_sentences(thm, rec) {
        let said: Vec<(Node, String)> = said
            .into_iter()
            .filter(|(_, n)| bound.contains(n.as_str()))
            .collect();
        let names: Vec<String> = said.iter().map(|(_, n)| n.clone()).collect();
        proof.named.insert(label.clone(), names);
        proof.trees.insert(label, said);
    }
    // A recursion or a function the statement lets is cited by its label,
    // as its hypothesis (`header_recursions`).
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let function = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(_)) => true,
            Route::Built(crate::corpus::DefineParts::One(one)) => {
                !one.params.is_empty()
            }
            _ => false,
        };
        if function {
            proof
                .named
                .insert(d.label.clone(), vec![line_name(&d.label)]);
        }
    }
    let props: Vec<String> = conclusion.iter().map(|c| c.prop.at(36)).collect();
    let binders: Vec<String> =
        super::statement::things_binder(&binders, &props.join(" "))
            .into_iter()
            .chain(binders.iter().map(Binder::lean))
            .collect();
    let space = if binders.is_empty() { "" } else { " " };
    // Lean's budget for one declaration, 200000 heartbeats, for each 10
    // steps of the proof: a long proof is many steps, each of the usual
    // cost, which the one default would cut off part way. A proof of 37
    // steps citing items over ℚ and ℝ took 16 seconds and more than one;
    // Ramsey's 26, citing "for all" statements over sets, between two and
    // four hundred thousand; the cubic formula's 42, whose algebra clears
    // divisions by terms of i and √3, between six and nine hundred
    // thousand.
    let budget = match thm.steps.len().div_ceil(10) {
        0 | 1 => String::new(),
        n => format!("set_option maxHeartbeats {} in\n", 200_000 * n),
    };
    proof.push(
        format!(
            "{budget}theorem {}{space}{} :\n    {} := by",
            snake(&thm.name),
            binders.join(" "),
            props.join(" ∧ ")
        ),
        thm.line,
        Spot::Statement,
    );
    // The names the statement wrote out, named again for the proof.
    // Only those the theorem's page writes: a file's other defines are its
    // other theorems'.
    let written: std::collections::BTreeSet<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.names())
        .collect();
    for (name, body) in statement_terms(rec) {
        if !written.contains(&name) {
            continue;
        }
        let own = thm.defines.iter().position(|d| {
            d.line < thm.conclusion_line
                && matches!(
                    crate::corpus::define_parts(&d.text),
                    Route::Built(crate::corpus::DefineParts::One(ref one)) if one.name == name
                )
        });
        let named = match own {
            Some(d) => proof.define(d, 1),
            None => proof.define_outside(&name, &body),
        };
        if let Route::Declined(d) = named {
            return Route::Declined(d);
        }
    }
    let top: Vec<usize> = (0..thm.steps.len())
        .filter(|&i| rec.places[i].is_none())
        .collect();
    if let Route::Declined(d) = proof.steps(&top, 1) {
        return Route::Declined(d);
    }
    // One term, one form: a square root or real power the lines in scope
    // put at least 0 in one place and not in another is reported, not
    // converted between.
    if let Some(root) = proof.writer.roots_written_both_ways() {
        return Route::no(format!(
            "{root} is written as Mathlib's real one in one place and the principal one in ℂ in another"
        ));
    }
    if conclusion.len() > 1 {
        let each = Printed::atom("by parley_side");
        proof.push_at(
            1,
            Tactic::Exact(super::expr::anonymous(vec![each; conclusion.len()])),
            thm.conclusion_line,
            Spot::Statement,
        );
    } else {
        let close = match conclusion.as_slice() {
            [one] => proof.closing(top.last().copied(), &one.says),
            _ => super::tactics::bridge(BridgeTactic::Side, vec![]),
        };
        proof.push_at(
            1,
            Tactic::AllGoals(Box::new(close)),
            thm.conclusion_line,
            Spot::Statement,
        );
    }
    let mut text = String::new();
    let mut origins = Vec::new();
    let mut at = 1;
    for line in &proof.lines {
        let written = line.text();
        for _ in written.lines() {
            origins.push(Origin {
                line: at,
                ..line.origin.clone()
            });
            at += 1;
        }
        text.push_str(&written);
        text.push('\n');
    }
    let forms = proof.forms.take();
    Route::Built(LeanFile {
        text,
        origins,
        forms,
    })
}

/// Indentation for a depth of nesting.
fn pad(depth: usize) -> String {
    "  ".repeat(depth)
}

/// What proves a claim: a justification, and what the checker read of the
/// item it cites. A step has one, and so does each of its requires lines
/// and each line of a calculation that gives a reason of its own.
#[derive(Clone, Copy)]
struct Reason<'r> {
    just: &'r Justification,
    cited: Option<&'r Cited>,
}

impl<'a> Proof<'a> {
    fn push(&mut self, line: String, page_line: usize, spot: Spot) {
        self.push_at(0, Tactic::Raw(line), page_line, spot);
    }

    /// `intro a b` as a line of the proof at a depth of its blocks.
    fn intro(
        &mut self,
        depth: usize,
        names: Vec<String>,
        page_line: usize,
        spot: &Spot,
    ) {
        self.push_at(depth, Tactic::Intro(names), page_line, spot.clone());
    }

    /// A tactic as a line of the proof at a depth of its blocks.
    fn push_at(&mut self, depth: usize, tactic: Tactic, page_line: usize, spot: Spot) {
        self.lines.push(ProofLine {
            depth,
            tactic,
            origin: Origin {
                line: 0,
                page_line,
                spot,
            },
        });
    }

    fn step_spot(step: &Step) -> Spot {
        Spot::Step(match step.number.number() {
            Some(n) => n.to_string(),
            None => "the theorem".to_string(),
        })
    }

    /// The steps, in order, each at the depth given.
    fn steps(&mut self, indices: &[usize], depth: usize) -> Route<()> {
        for &i in indices {
            if let Route::Declined(d) = self.step(i, depth) {
                // Named by the innermost step it comes from: a block's
                // decline already names the step inside it.
                let reason = d.reason();
                if reason.starts_with("step ") {
                    return Route::Declined(d);
                }
                let number = &self.thm.steps[i].number;
                return Route::no(format!("step {number}: {reason}"));
            }
        }
        Route::Built(())
    }

    /// A step's claim: each sentence, read, with its Lean text; a
    /// membership Lean's types already give is left out, since nothing
    /// needs saying.
    fn claim(&self, step: &Step) -> Route<Vec<(Node, Printed)>> {
        self.claimed(step).map(|c| {
            c.into_iter()
                .map(|(_, node, printed)| (node, printed))
                .collect()
        })
    }

    /// `claim`, each sentence with its place among the page's: a sentence
    /// Lean's types already give, √x ∈ ℝ, is left out, and a citation is
    /// read at the place the checker counted.
    fn claimed(&self, step: &Step) -> Route<Vec<(usize, Node, Printed)>> {
        let mut out = Vec::new();
        for (at, s) in step.claim.sentences().into_iter().enumerate() {
            let Some(node) = self.rec.page.get(&s) else {
                return Route::no(format!(
                    "{}, which the checker did not read",
                    s.text()
                ));
            };
            // A claim of numerals alone is written in the type of the lines
            // it is reached from, where any are cited.
            let printed = if node.names().is_empty() {
                let mut floor = super::templates::Num::Int;
                for c in self.cited_parts(&step.just.refs) {
                    for side in
                        c.node.children.iter().filter(|s| self.writer.is_number(s))
                    {
                        if let Route::Built(n) = self.writer.carrier(side) {
                            floor = floor.max(n);
                        }
                    }
                }
                self.writer.closed_formula(node, floor)
            } else {
                self.writer.formula(node)
            };
            let printed = match printed {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            if printed.text() != "True" {
                out.push((at, node.clone(), printed));
            }
        }
        Route::Built(out)
    }

    /// The Lean names of a step's sentences: `s2` for one, `s2a`, `s2b` for
    /// several.
    fn names_of(step: &Step, count: usize) -> Vec<String> {
        let base = match step.number.number() {
            Some(n) => line_name(&n.to_string()),
            None => "sThm".to_string(),
        };
        if count == 1 {
            return vec![base];
        }
        (0..count)
            .map(|i| format!("{base}{}", (b'a' + i as u8) as char))
            .collect()
    }

    /// The letters a step's claim introduces, `k ∈ ℤ`, added to those in
    /// scope. A claim of a letter already in scope introduces nothing: it
    /// says something of the letter, a fact a later step may use.
    fn introduce(&mut self, step: &Step) {
        for s in step.claim.sentences() {
            if let Some(node) = self.rec.page.get(&s) {
                let letter = introduces(node)
                    .map(|(l, _)| l)
                    .or_else(|| super::statement::range_letter(node));
                let known = letter
                    .is_some_and(|l| self.writer.letters.contains_key(l.as_str()));
                if known {
                    continue;
                }
                if let Some((letter, system)) = introduces(node) {
                    self.writer.introduce(&letter, system);
                } else if let Some(letter) = super::statement::range_letter(node) {
                    // In ℕ or ℕ₀ where the range starts at 1 or 0, as the
                    // page says once (`citing::range_system`).
                    let system = match node.children.get(1) {
                        Some(range) => super::expr::range_letter_system(range),
                        None => super::expr::System::Type(super::templates::Num::Int),
                    };
                    self.writer.introduce(&letter, system);
                } else if let Some((letter, members)) = self.set_member_said(node) {
                    self.writer.letters.insert(letter, members.letter());
                } else if let Some((letter, members)) = self.part_said(node) {
                    self.writer.letters.insert(letter, LetterType::Set(members));
                } else if let Some((letter, ty)) = self.function_said(node) {
                    self.writer.letters.insert(letter, ty);
                } else if let Some(letter) =
                    super::statement::introduces_polynomial(node)
                {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Function {
                            from: super::templates::Num::Complex,
                            to: super::templates::Num::Complex,
                        },
                    );
                }
            }
        }
    }

    /// The letter a line says is a function between sets, `g : {1, …, j} →
    /// ℕ`, where the letter is new, with the type `Writer::function_between`
    /// gives it.
    fn function_said(&self, node: &Node) -> Option<(String, LetterType)> {
        let [g, from, to] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == crate::notations::FUNCTION_TYPE
            && g.is_name()
            && !self.writer.letters.contains_key(g.text.as_str());
        new.then(|| self.writer.function_between(from, to))
            .flatten()
            .map(|ty| (g.text.to_string(), ty))
    }

    /// The letter a line says is a part of a set, `W ⊆ X`, where the letter
    /// is new and the writer has a type for X's members: a set of those.
    fn part_said(&self, node: &Node) -> Option<(String, super::expr::Members)> {
        let [w, set] = node.children.as_slice() else {
            return None;
        };
        let new = &*node.notation_name() == "subset"
            && w.is_name()
            && !self.writer.letters.contains_key(w.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (w.text.to_string(), m))
    }

    /// The letter a line says is a member of a set, `x ∈ A`, where the
    /// letter is new and the writer has a type for A's members.
    fn set_member_said(&self, node: &Node) -> Option<(String, super::expr::Members)> {
        let [x, set] = node.children.as_slice() else {
            return None;
        };
        let new = node.notation() == crate::notations::MEMBERSHIP
            && x.is_name()
            && !self.writer.letters.contains_key(x.text.as_str());
        new.then(|| self.writer.members_of(set))
            .flatten()
            .map(|m| (x.text.to_string(), m))
    }

    fn step(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        // A square root of y − 3 is Mathlib's real one once a line in scope
        // says y − 3 ≥ 0 (`Writer::principal_is_real`).
        self.writer
            .bounds_from(self.trees.values().flatten().map(|(n, _)| n));
        // The defines written above this step in its block, where the
        // checker opens them.
        let due: Vec<usize> = (0..self.thm.defines.len())
            .filter(|&d| {
                !self.defined.contains(&d)
                    && self.thm.defines[d].line < step.line
                    && self.thm.defines[d].line > self.thm.conclusion_line
                    && self.rec.defines.get(d).copied().flatten() == self.rec.places[i]
            })
            .collect();
        for d in due {
            if let Route::Declined(why) = self.define(d, depth) {
                return Route::Declined(why);
            }
        }
        let spot = Self::step_spot(step);
        self.push_at(
            depth,
            Tactic::Comment(format!("{}. {}", step.number, step.just.text.trim())),
            step.line,
            spot.clone(),
        );
        // The claim's first sentence as the page reads it, whose leading
        // "for all" binds letters its requires lines may speak of.
        let claimed = step
            .claim
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
            .cloned();
        for (k, r) in step.requires.iter().enumerate() {
            let node = match self.tree(&r.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A requires line of a letter the claim says "for all" of, x²
            // ≥ 0 of every x ∈ [0, 1], is said under the claim's binders and
            // proved with its letters given.
            let under = claimed
                .as_ref()
                .filter(|c| bound_in(c, &node))
                .map(|c| under_binders(c, &node));
            let stated = under.clone().unwrap_or_else(|| node.clone());
            let fact = match self.writer.formula(&stated) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if fact.text() == "True" {
                continue;
            }
            let Ok(just) = &r.by else {
                return Route::no("a requires line whose reason does not read");
            };
            let reason = Reason {
                just,
                cited: self.rec.cited_requires.get(&r.line),
            };
            let proof = match &under {
                // Its whole numbers named from the lines its own reason
                // cites, p^(a′ − a) ∈ ℤ from 3.3.
                None => {
                    let facts = self.cited_parts(&just.refs);
                    self.proof_named_from(reason, 0, &node, i, &facts)
                }
                Some(wrapped) => {
                    let (intros, _, inner) = self.peel(wrapped);
                    let outer = std::mem::replace(&mut self.writer, inner);
                    let proof = self.proof_of(reason, 0, &node);
                    self.writer = outer;
                    proof.map(|p| after_intros(&intros, &p))
                }
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("r{}_{}", step.line, k + 1);
            self.push_at(
                depth,
                Tactic::Have {
                    name,
                    says: fact.clone(),
                    proof,
                },
                r.line,
                spot.clone(),
            );
        }
        if let Head::Method(Method::Obtain) = step.just.head {
            return self.obtain(i, depth);
        }
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        if let Head::Method(m) = step.just.head {
            // A calculation's lines are its proof, written as Lean's calc;
            // every other block's steps stand in it.
            if m.takes_block() && m != Method::Calculation {
                // The lines inside a block are out of scope after it, and
                // the claim the block proves is no line in scope inside it.
                let own = step.number.number().map(|n| n.to_string());
                let claimed = own.as_ref().and_then(|n| self.trees.shift_remove(n));
                let visible: std::collections::BTreeSet<String> =
                    self.trees.keys().cloned().collect();
                let written = self.block(i, m, &claim, &names, depth);
                self.trees.retain(|k, _| visible.contains(k));
                if let (Some(n), Some(said)) = (own, claimed) {
                    self.trees.insert(n, said);
                }
                return written;
            }
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let places: Vec<usize> = match self.claimed(step) {
            Route::Built(c) => c.into_iter().map(|(at, _, _)| at).collect(),
            Route::Declined(d) => return Route::Declined(d),
        };
        for (k, (node, prop)) in claim.iter().enumerate() {
            // A citation for a claim said "for all k ∈ …" of an item said of
            // one k, its letters given values in the claim's k: the item
            // cited at that k, given as a method takes it (`peel`). An item
            // that says the "for all" itself is cited whole.
            let cites_for_all = matches!(reason.just.head, Head::Item { .. })
                && node.notation() == crate::notations::FOR_ALL
                && self.cited_at_bound_letter(reason.cited, node);
            let proof = if cites_for_all {
                let (intros, body, inner) = self.peel(node);
                let outer = std::mem::replace(&mut self.writer, inner);
                let proof = self.proof_of(reason, places[k], body);
                self.writer = outer;
                proof.map(|p| match intros.is_empty() {
                    true => p,
                    false => after_intros(&intros, &p),
                })
            } else {
                self.proof_with_named(reason, places[k], node, i)
            };
            let proof = match proof {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.push_at(
                depth,
                Tactic::Have {
                    name: names[k].clone(),
                    says: prop.clone(),
                    proof,
                },
                step.line,
                spot.clone(),
            );
        }
        if step.impossible {
            // A line of roots or of π, ln, exp, sin or cos, √2 − 1 = 0, is
            // shown false by real arithmetic; any other by `norm_num`.
            let real = claim.iter().any(|(node, _)| {
                node.walk().iter().any(|n| {
                    matches!(&*n.notation_name(), "square-root" | "pi")
                        || n.children.first().is_some_and(|f| {
                            matches!(&*f.text, "cos" | "sin" | "exp" | "ln" | "tan")
                        })
                })
            });
            let refute = if real { "parley_real" } else { "norm_num" };
            if let Some(last) = names.last() {
                use super::tactics as t;
                let refuted = Printed::atom(format!("(by {refute})"));
                let absurd = Printed::applied(
                    "absurd",
                    super::doc::Source::Core,
                    vec![t::hyp(last), refuted],
                    super::doc::LeanType::Prop,
                );
                self.push_at(depth, Tactic::Exact(absurd), step.line, spot.clone());
            }
        }
        Route::Built(())
    }

    /// A sentence of the page as the checker read it.
    fn tree(&self, written: &Written) -> Route<Node> {
        match written
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
        {
            Some(node) => Route::Built(node.clone()),
            None => Route::no(format!(
                "{}, which the checker did not read",
                written.text()
            )),
        }
    }

    /// The widest fixed type a hole of the claim takes, ℝ of ⌊A/B⌋, which
    /// a term in that hole is computed in; ℤ where there is none.
    fn held_in(&self, claim: &Node) -> super::templates::Num {
        claim
            .walk()
            .iter()
            .filter_map(|n| self.writer.template(n).built())
            .flat_map(|t| t.holes.iter())
            .filter_map(|s| match s {
                super::templates::Slot::Fixed(n) => Some(*n),
                _ => None,
            })
            .fold(super::templates::Num::Int, std::cmp::Ord::max)
    }

    /// The proof of sentence `k` of step `i`'s claim, where the claim puts
    /// a term Lean does not compute as a whole number in a slot for one,
    /// "2^p − 1 divides 2^(p − 1)·2", written `∃ m : ℤ, (m : ℚ) = … ∧ …`
    /// (`Writer::slot_witness`): the whole number it is, named from the
    /// lines the step names as Metamath proves its membership from them
    /// (`named_atoms`), given as the witness, and the reason proving the
    /// claim of it. Of any other claim, `proof_of`.
    fn proof_with_named(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
    ) -> Route<String> {
        let facts = self.step_facts(i);
        self.proof_named_from(reason, k, node, i, &facts)
    }

    /// `proof_with_named`, its numbers named from `facts`: a step's lines,
    /// or those a requires line's own reason cites.
    fn proof_named_from(
        &mut self,
        reason: Reason,
        k: usize,
        node: &Node,
        i: usize,
        facts: &[super::algebra::Cited],
    ) -> Route<String> {
        // A claim that a term Lean does not compute as a whole number is
        // one, p^(a′ − a) ∈ ℕ, written `∃ m : ℤ, 0 < m ∧ (m : ℚ) = …`
        // (`Writer::in_system`): the number the step's lines name is the
        // witness, and of ℕ or ℕ₀ its order the step's reason, said of it.
        if let Some((term, whole, ordered)) = self.wide_member(node) {
            let mut atoms = Vec::new();
            // Where the step's lines name no such number, the membership is
            // what the lines in scope give (`said_member`).
            if self
                .named_atoms(&term, i, whole, facts, &mut atoms)
                .built()
                .is_none()
            {
                return self.proof_of(reason, k, node);
            }
            let mut inner = self.writer.with_letters(self.writer.letters.clone());
            inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
            let int = match inner.number_fixed(&term, super::templates::Num::Int) {
                Route::Built(p) => p.at(super::expr::MAX),
                Route::Declined(d) => return Route::Declined(d),
            };
            let specs: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
            let equal = specs_equal(&specs);
            let haves: Vec<String> = atoms.iter().map(|a| a.have.clone()).collect();
            if !ordered {
                return Route::Built(with_haves(
                    &haves,
                    &format!("by exact ⟨{int}, {equal}⟩"),
                ));
            }
            let outer = std::mem::replace(&mut self.writer, inner);
            let proof = self.proof_of(reason, k, node);
            self.writer = outer;
            let proof = match proof {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let tactic =
                format!("by refine ⟨{int}, ?_, {equal}⟩\n{}", as_tactic(&proof));
            return Route::Built(with_haves(&haves, &tactic));
        }
        let claimed = self.writer.wide_in_slot(node);
        // The lines the step cites that say something of a whole number a
        // term is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) ∧ …`, or that none is,
        // `¬ ∃ m : ℤ, …`, by the name they stand under, which a
        // restatement of them takes.
        let cited: Vec<CitedWitness> = self
            .cited_parts(&step_cited_refs(&self.thm.steps[i], &self.thm.path))
            .into_iter()
            .filter(|c| c.proof.chars().all(|ch| ch.is_alphanumeric() || ch == '_'))
            .filter_map(|c| {
                let (said, negated) =
                    match (c.node.notation(), c.node.children.as_slice()) {
                        (crate::notations::LOGICAL_NOT, [inner]) => (inner, true),
                        _ => (&c.node, false),
                    };
                let (term, whole) = self.writer.wide_in_slot(said)?;
                Some(CitedWitness {
                    name: c.proof,
                    term,
                    whole,
                    negated,
                })
            })
            .collect();
        if claimed.is_none() && cited.is_empty() {
            return self.proof_of(reason, k, node);
        }
        let mut atoms = Vec::new();
        if let Some((term, whole)) = &claimed {
            if let Route::Declined(d) =
                self.named_atoms(term, i, *whole, facts, &mut atoms)
            {
                return Route::Declined(d);
            }
        }
        // A cited line whose term no line the step names makes whole is left
        // as it is: the step may not need it so.
        let cited: Vec<_> = cited
            .into_iter()
            .filter(|c| {
                let before = atoms.len();
                let named = self
                    .named_atoms(&c.term, i, c.whole, facts, &mut atoms)
                    .built()
                    .is_some();
                if !named {
                    atoms.truncate(before);
                }
                named
            })
            .collect();
        let mut inner = self.writer.with_letters(self.writer.letters.clone());
        inner.integers.extend(atoms.iter().map(|a| a.said.clone()));
        // Each named number's equation with its term: the one a step proves
        // of a power written out, the line's witness's for one it gives.
        let specs: Vec<String> = atoms
            .iter()
            .map(|a| match a.said.value {
                Some(_) => a.said.proof.clone(),
                None => format!("Classical.choose_spec {}", a.said.proof),
            })
            .collect();
        let spec_terms: Vec<Printed> = atoms.iter().map(|a| spec_of(&a.said)).collect();
        let equal = specs_equal(&spec_terms);
        let mut haves: Vec<String> = atoms.iter().map(|a| a.have.clone()).collect();
        // Each such cited line, said of the number the step names.
        for c in &cited {
            let int = match inner.number_fixed(&c.term, c.whole) {
                Route::Built(p) => p.at(super::expr::MAX),
                Route::Declined(d) => return Route::Declined(d),
            };
            let lemma = match (c.whole, c.negated) {
                (super::templates::Num::Nat, false) => "parley_witness_at_nat",
                (super::templates::Num::Nat, true) => "parley_witness_not_at_nat",
                (_, false) => "parley_witness_at",
                (_, true) => "parley_witness_not_at",
            };
            let name = &c.name;
            haves.push(format!("have {name} := {lemma} {name} {int} ({equal})"));
        }
        let int = match &claimed {
            Some((term, whole)) => match inner.number_fixed(term, *whole) {
                Route::Built(p) => Some(p.at(super::expr::MAX)),
                Route::Declined(d) => return Route::Declined(d),
            },
            None => None,
        };
        let outer = std::mem::replace(&mut self.writer, inner);
        self.named_specs = specs.clone();
        let proof = self.proof_of(reason, k, node);
        self.named_specs.clear();
        self.writer = outer;
        let proof = match proof {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let tactic = match int {
            Some(int) => {
                format!("by refine ⟨{int}, {equal}, ?_⟩\n{}", as_tactic(&proof))
            }
            None => proof,
        };
        Route::Built(with_haves(&haves, &tactic))
    }

    /// Of a claim that a term Lean computes in ℚ or wider is a whole number,
    /// p^(a′ − a) ∈ ℕ, the term, the type its parts are named in (ℤ, the
    /// page's ℕ being integers), and whether the claim orders it, 0 < m or
    /// 0 ≤ m beside the integer m it is; None for any other claim, one of a
    /// letter among them.
    fn wide_member(&self, node: &Node) -> Option<(Node, super::templates::Num, bool)> {
        use super::expr::System;
        use super::templates::Num;
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        if node.notation() != crate::notations::MEMBERSHIP || term.is_name() {
            return None;
        }
        let (whole, ordered) = match super::expr::system_of(set)? {
            System::Positive | System::NonNegative => (Num::Int, true),
            System::Type(Num::Int) => (Num::Int, false),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()? > Num::Int;
        wide.then(|| (term.clone(), whole, ordered))
    }

    /// The lines step `i` names, by which it names whole numbers: its
    /// requires lines and the lines it cites, each with its Lean name.
    fn step_facts(&self, i: usize) -> Vec<super::algebra::Cited> {
        let step = &self.thm.steps[i];
        let mut facts = Vec::new();
        for (k, r) in step.requires.iter().enumerate() {
            if let Route::Built(node) = self.tree(&r.fact) {
                facts.push(super::algebra::Cited {
                    node,
                    proof: format!("r{}_{}", step.line, k + 1),
                });
            }
        }
        facts.extend(self.cited_parts(&step.just.refs));
        facts
    }

    /// The whole numbers a term is made of that Lean does not compute as
    /// whole numbers, each named from a line step `i` names, by the said-once
    /// walk both backends read memberships with (`citing::reason_within`,
    /// over the checker's letters): 2^(p − 1) from the requires line `p − 1
    /// ∈ ℕ₀`, as `⟨2 ^ (p − 1).toNat, …⟩`; a term a line says is in ℤ, ℕ₀ or
    /// ℕ, from that line. A term made of such by +, − and · is written of
    /// them (`Writer::number`), so it keeps one form. Declined where no line
    /// the step names makes the term a whole number.
    fn named_atoms(
        &self,
        term: &Node,
        i: usize,
        whole: super::templates::Num,
        facts: &[super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> Route<()> {
        let system = match whole {
            super::templates::Num::Nat => crate::rules::System::N0,
            _ => crate::rules::System::Z,
        };
        let Some(letters) = self.rec.introduced.get(i) else {
            return Route::no("a step the checker's record has no letters for");
        };
        let said = |t: &Node, s: crate::rules::System| {
            stated_line(facts, t, s, self.sources.ctx)
                .map(|_| crate::citing::OnceReason::Stated)
        };
        let nonzero = |d: &Node| crate::citing::nonzero_said_once(d, letters);
        let Some(reason) =
            crate::citing::reason_within(term, system, letters, &nonzero, &said)
        else {
            return Route::no(format!(
                "{}, put where a whole number is asked, is one by no line the step names",
                self.writer.grammar.print(term)
            ));
        };
        let top = match self.writer.carrier(term) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        match self.atoms_of(term, &reason, whole, top, facts, out) {
            true => Route::Built(()),
            false => Route::no(format!(
                "{} is a whole number Lean is not shown, by the lines the step names",
                self.writer.grammar.print(term)
            )),
        }
    }

    /// `named_atoms` of one part, whose reason is `reason`, named in
    /// `whole`, ℤ or ℕ: false where a part is none the walk can name.
    fn atoms_of(
        &self,
        term: &Node,
        reason: &crate::citing::OnceReason,
        whole: super::templates::Num,
        top: super::templates::Num,
        facts: &[super::algebra::Cited],
        out: &mut Vec<NamedAtom>,
    ) -> bool {
        use super::templates::Num;
        use crate::citing::OnceReason;
        use crate::rules::System;
        let Some(own) = self.writer.carrier(term).built() else {
            return false;
        };
        // Each equation is stated in the type of the whole term the part is
        // in, ℚ of 2^(p − 1)·(2^p − 1), where it is put into that term's.
        let at = own.max(top);
        let already = match whole {
            Num::Nat => self.writer.natural(term) || self.writer.said_whole(term),
            _ => own <= Num::Int,
        };
        if already {
            return true;
        }
        let printed = self.writer.grammar.print(term);
        if out.iter().any(|a| a.said.term == printed) {
            return true;
        }
        let Some(value) = self.writer.number_fixed(term, at).built() else {
            return false;
        };
        let name = format!("whole{}", out.len() + 1);
        let ty = self.writer.type_name(at);
        let (have, written) = match (reason, term.notation(), term.children.as_slice())
        {
            // A term a line the step names puts in ℕ, ℕ₀ or ℤ: that line's
            // witness, of ℕ where a natural number is asked.
            (OnceReason::Stated, _, _) => {
                let asked = match whole {
                    Num::Nat => System::N0,
                    _ => System::Z,
                };
                let Some(StatedLine { name: line, system }) =
                    stated_line(facts, term, asked, self.sources.ctx)
                else {
                    return false;
                };
                // Of an integer, the line is an order, 0 < 2^p − 1 for ∈ ℕ:
                // the natural number is the integer's `toNat`, written out as
                // σ of an integer takes it, and its equation with the term.
                if own <= Num::Int {
                    let nonneg = match system {
                        System::N => format!("(le_of_lt {line})"),
                        _ => line,
                    };
                    let Some(int) = self.writer.number_fixed(term, Num::Int).built()
                    else {
                        return false;
                    };
                    let written = format!("({}).toNat", int.text());
                    let have = format!(
                        "have {name} : (({written} : ℕ) : {ty}) = {} := by exact_mod_cast Int.toNat_of_nonneg {nonneg}",
                        value.text()
                    );
                    out.push(NamedAtom {
                        have,
                        said: super::expr::SaidInteger {
                            term: printed,
                            proof: name,
                            ty: whole,
                            value: Some(written),
                            slot_only: true,
                        },
                    });
                    return true;
                }
                // Of a wider term, the line is a witness: `∃ m : ℤ, 0 ≤ m ∧
                // ↑m = t` for ℕ₀, `0 < m` for ℕ, `↑m = t` for ℤ. A natural
                // number asked is that integer's `toNat`, by its order.
                let have = match (system, whole) {
                    (System::N | System::N0, Num::Nat) => {
                        let nonneg = match system {
                            System::N => "(le_of_lt h0)",
                            _ => "h0",
                        };
                        format!(
                            "have {name} : ∃ m : ℕ, (m : {ty}) = {} := by obtain ⟨m, h0, hm⟩ := {line}; exact ⟨m.toNat, by rw [show ((m.toNat : ℕ) : {ty}) = ((m : ℤ) : {ty}) by exact_mod_cast Int.toNat_of_nonneg {nonneg}]; exact_mod_cast hm⟩",
                            value.text()
                        )
                    }
                    (System::N | System::N0, _) => format!(
                        "have {name} : ∃ m : ℤ, (m : {ty}) = {} := by obtain ⟨m, _, hm⟩ := {line}; exact ⟨m, by exact_mod_cast hm⟩",
                        value.text()
                    ),
                    _ => format!(
                        "have {name} : ∃ m : {}, (m : {ty}) = {} := by obtain ⟨m, hm⟩ := {line}; exact ⟨m, by exact_mod_cast hm⟩",
                        whole.lean(),
                        value.text()
                    ),
                };
                (have, None)
            }
            // A power to an exponent a line the step names puts in ℕ₀: the
            // base to that exponent's `toNat`, written out, and its equation
            // with the power, from that line.
            (OnceReason::Built(parts), crate::notations::POWER, [base, exponent]) => {
                let [base_reason] = parts.as_slice() else {
                    return false;
                };
                if self.writer.natural(exponent) || self.writer.said_whole(exponent) {
                    return self.atoms_of(base, base_reason, whole, top, facts, out);
                }
                let Some(StatedLine { name: line, system }) =
                    stated_line(facts, exponent, System::N0, self.sources.ctx)
                else {
                    return false;
                };
                let nonneg = match system {
                    System::N => format!("(le_of_lt {line})"),
                    _ => line,
                };
                let (Some(b), Some(e), Some(cast_base)) = (
                    self.writer.number_fixed(base, whole).built(),
                    self.writer.number_fixed(exponent, Num::Int).built(),
                    self.writer.number_fixed(base, at).built(),
                ) else {
                    return false;
                };
                let written = format!("{} ^ ({}).toNat", b.at(76), e.text());
                let have = format!(
                    "have {name} : ({} : {ty}) ^ ({}).toNat = {} := by rw [← zpow_natCast, Int.toNat_of_nonneg {nonneg}]",
                    cast_base.text(), e.text(), value.text()
                );
                (have, Some(written))
            }
            (OnceReason::Built(parts), _, kids) if parts.len() == kids.len() => {
                return kids.iter().zip(parts).all(|(kid, part)| {
                    self.atoms_of(kid, part, whole, top, facts, out)
                });
            }
            _ => return false,
        };
        out.push(NamedAtom {
            have,
            said: super::expr::SaidInteger {
                term: printed,
                proof: name,
                ty: whole,
                value: written,
                slot_only: true,
            },
        });
        true
    }

    /// The proof of sentence `k` of a claim, by its reason.
    fn proof_of(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        if let Some(witness) = self.said_member(node) {
            return Route::Built(format!("by {witness}"));
        }
        self.said_used.borrow_mut().clear();
        let proof = match self.proof_by_reason(reason, k, node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A citation given a line's number, ⌊m⌋ = m for the m of `A/B ∈
        // ℤ`, meets a goal that has the line's term, ⌊A/B⌋: the goal is put
        // in terms of the number first.
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let specs = self.specs_in(node, &used);
        Route::Built(match specs.is_empty() {
            true => proof,
            false => format!("by rw [{specs}]; {}", as_tactic(&proof)),
        })
    }

    /// Whether a citation gives its item's letters values in a letter the
    /// claim's leading "for all" binds: the item is cited at that letter.
    fn cited_at_bound_letter(
        &self,
        cited: Option<&crate::checker::record::Cited>,
        claim: &Node,
    ) -> bool {
        let Some(cited) = cited else {
            return false;
        };
        let mut bound = Vec::new();
        let mut body = claim;
        while let (crate::notations::FOR_ALL, [letter, _, inner]) =
            (body.notation(), body.children.as_slice())
        {
            bound.push(letter.text);
            body = inner;
        }
        // A letter free in a value: a value that binds it itself, Q := "for
        // all x, …", says the "for all" whole, and so does a function by its
        // values, t := k ↦ a(k)², whose k is its own.
        let binders = self.sources.checked.grammar.binders();
        cited.binding.values().any(|v| {
            let own = |n: &str| &*v.notation_name() == "property-of" && *v.text == *n;
            crate::matching::free_names(v, &binders)
                .iter()
                .any(|n| !own(n) && bound.iter().any(|b| **b == **n))
        })
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// which a step cites by its label; None for any other citation.
    fn header_function_cited(&self, just: &Justification) -> Option<String> {
        self.header_function_named(just.defined.as_deref()?)
    }

    /// The hypothesis of a function the theorem's header lets by its value,
    /// by its label; None for any other label.
    fn header_function_named(&self, label: &str) -> Option<String> {
        let d = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line < self.thm.conclusion_line)?;
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                Some(line_name(&d.label))
            }
            _ => None,
        }
    }

    /// The recursion a step cites by its label, the header's or one the
    /// proof lets, whose hypotheses are written alike; None for a citation
    /// of any other define.
    fn recursion_cited(&self, just: &Justification) -> Option<CitedRecursion> {
        let label = just.defined.as_deref()?;
        let d = self.thm.defines.iter().find(|d| d.label == label)?;
        let by_cases = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == d.line)
            .any(|(_, n)| n.walk().iter().any(|m| &*m.notation_name() == "by-cases"));
        match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(rule)) => {
                Some(CitedRecursion {
                    rule,
                    hypothesis: line_name(&d.label),
                    by_cases,
                })
            }
            _ => None,
        }
    }

    /// A step citing a recursion's rule, F(k + 1) = G(k): the first of the
    /// claim's applications of its functions, F(a), says which. At the
    /// numeral 0 it is F's start; at any other a it is F's step at a − 1,
    /// with a − 1 + 1 put back as a, and the arguments put in one form. A
    /// rule by cases is taken at the case the cited lines say: an equation
    /// its condition, `ite_eq_left`; one denied, `otherwise`, `ite_eq_right`.
    /// Its condition is put at a first, a − 1 + 1 inside it as a, for the
    /// cited line to match.
    fn recursion_clause(
        &self,
        cited: &CitedRecursion,
        cases: &[super::algebra::Cited],
        claim: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let (r, hyp) = (&cited.rule, &cited.hypothesis);
        let mut case_rewrites = String::new();
        if cited.by_cases {
            for c in cases {
                let lemma = match (c.node.notation(), c.node.children.as_slice()) {
                    (EQUALITY, _) => "ite_eq_left",
                    (crate::notations::LOGICAL_NOT, [inner])
                        if inner.notation() == EQUALITY =>
                    {
                        "ite_eq_right"
                    }
                    _ => continue,
                };
                case_rewrites.push_str(&format!(" rw [{lemma} {}] at h;", c.proof));
            }
        }
        let cancel = match case_rewrites.is_empty() {
            true => "sub_add_cancel",
            false => "sub_add_cancel, add_sub_cancel_right",
        };
        let applied = claim.walk().into_iter().find_map(|n| {
            let [f, a] = n.children.as_slice() else {
                return None;
            };
            let at = r.names.iter().position(|name| *name == *f.text)?;
            (n.notation() == crate::notations::APPLICATION).then(|| (at, a.clone()))
        });
        let Some((at, arg)) = applied else {
            return Route::no("a recursion cited for a claim of none of its functions");
        };
        let n = r.names.len();
        // The hypothesis is the starts and then the steps, joined by ∧.
        let start = projection(at, n + 1);
        let steps = projection(n, n + 1);
        let step = projection(at, n);
        // The rule in the type the recursion computes in, the claim in its
        // own, N(0) = 0 in ℤ for (N 0 : ℝ) = 0 of a theorem in ℝ: the rule
        // cast up first where the claim's type is wider.
        let closed = "first | linarith | (rify at h; (try push_cast at h ⊢); linarith) | (qify at h; (try push_cast at h ⊢); linarith)";
        if arg.notation() == crate::notations::NUMERAL && &*arg.text == "0" {
            return Route::Built(format!(
                "by have h := {hyp}{start}; (try ring_nf at h ⊢); {closed}"
            ));
        }
        let a = match writer.number_fixed(&arg, super::templates::Num::Int) {
            Route::Built(a) => a,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(format!(
            "by have h := ({hyp}{steps} ({} - 1) (by omega)){step}; simp only [{cancel}] at h;{case_rewrites} (try ring_nf at h ⊢); {closed}",
            a.at(66)
        ))
    }

    /// A claim that a term of a wider type is an integer, a rational or a
    /// real, (A + B) − B ∈ ℚ of reals or √b + 1 ∈ ℝ of a square root in ℂ,
    /// where some part of it a line says is in
    /// that type: the term written there, that part the number the line
    /// gives, as Lean's witness. A citation of an item over ℚ gives such a
    /// claim nothing, as of rationals it holds by their type.
    fn said_member(&self, node: &Node) -> Option<String> {
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        use super::templates::Num;
        // The type the term is said to be in, and the type its parts are
        // said to be in: ℕ₀ is said of an integer, its parts integers.
        let (claimed, ty) = match super::expr::system_of(set)? {
            super::expr::System::Type(t @ (Num::Int | Num::Rat | Num::Real)) => (t, t),
            super::expr::System::NonNegative => (Num::Nat, Num::Int),
            _ => return None,
        };
        let wide = self.writer.carrier(term).built()?;
        if node.notation() != crate::notations::MEMBERSHIP || wide <= ty {
            return None;
        }
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut lines = Vec::new();
        // The parts within the term: the term itself is what the step
        // claims, and a letter of the type said is in it already; a letter
        // of a wider type, A ∈ ℝ, may be said an integer.
        let whole = writer.grammar.print(term);
        for part in term.walk() {
            let typed = part.is_name()
                && writer.carrier(&part).built().is_some_and(|c| c <= ty);
            if typed
                || part.notation() == crate::notations::NUMERAL
                || writer.grammar.print(&part) == whole
            {
                continue;
            }
            if let Some(line) = self.said_integer(&part, ty) {
                let spec = format!("Classical.choose_spec {line}");
                if lines.contains(&spec) {
                    continue;
                }
                writer.integers.push(super::expr::SaidInteger {
                    term: writer.grammar.print(&part),
                    proof: line.clone(),
                    ty,
                    value: None,
                    slot_only: false,
                });
                lines.push(spec);
            }
        }
        if lines.is_empty() {
            return None;
        }
        let witness = writer.number_fixed(term, ty).built()?.text();
        let specs = lines.join(", ");
        Some(match claimed {
            // In ℕ₀: the integer, beside its being at least 0.
            Num::Nat => format!(
                "(exact ⟨{witness}, by parley_side, by push_cast; (try simp only [{specs}]); first | done | parley_ring⟩)"
            ),
            _ => format!(
                "(exact ⟨{witness}, by push_cast; (try simp only [{specs}]); first | done | parley_ring⟩)"
            ),
        })
    }

    fn proof_by_reason(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        match &reason.just.head {
            Head::Item { .. } => self.citation(reason, k, node),
            Head::Method(m) => {
                // A claim said of every member of a set is proved of one,
                // taken as the method's letter. Substitute rows each say
                // the whole claim, "for all" and all, and end on it.
                let rows = *m == Method::Substitute && !reason.just.rows.is_empty();
                let (intros, body, writer) = match rows {
                    true => (
                        Vec::new(),
                        node,
                        self.writer.with_letters(self.writer.letters.clone()),
                    ),
                    false => self.peel(node),
                };
                let tactic = match self.method_proof(reason, *m, body, &writer) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let tactic = match self.count_conversion(*m, body, reason.just) {
                    CountConversion::None => tactic,
                    CountConversion::Before => {
                        format!("by parley_count_int; {}", as_tactic(&tactic))
                    }
                    CountConversion::After => {
                        format!("by parley_count_after ({tactic})")
                    }
                };
                if intros.is_empty() {
                    return Route::Built(tactic);
                }
                if tactic.starts_with("by\n") {
                    return Route::Built(after_intros(&intros, &tactic));
                }
                let inner = tactic.strip_prefix("by ").unwrap_or(&tactic);
                Route::Built(format!("by intro {}; {inner}", intros.join(" ")))
            }
            // A step citing a define claims its equation, which Lean's `set`
            // put in scope under the define's label.
            Head::Define => match self.recursion_cited(reason.just) {
                // A rule said for every n, F(n + 1) = 2F(n): said of one n.
                Some(r) => {
                    let (intros, body, writer) = self.peel(node);
                    let cases = self.cited_parts(&reason.just.from);
                    self.recursion_clause(&r, &cases, body, &writer).map(|t| {
                        match intros.is_empty() {
                            true => t,
                            false => format!(
                                "by intro {}; {}",
                                intros.join(" "),
                                as_tactic(&t)
                            ),
                        }
                    })
                }
                // A function the header lets by its value: its equation
                // put in, f(a) its value at a, and the claim closed.
                None => match self.header_function_cited(reason.just) {
                    Some(hyp) => Route::Built(format!(
                        "by (try simp only [{hyp}]); first | done | parley_side"
                    )),
                    // A define of the proof's, its equation under the
                    // define's label: unfolded, as a calculation row
                    // citing it is, L(k) = N(k)/10^k of L's `set`.
                    None => {
                        let unfold: Vec<String> = reason
                            .just
                            .refs
                            .iter()
                            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
                            .filter_map(|r| self.named.get(r).and_then(|n| n.first()))
                            .cloned()
                            .collect();
                        Route::Built(match unfold.is_empty() {
                            true => side_proof(),
                            false => {
                                let mut ways = unfolded(&unfold);
                                ways.push(super::tactics::bridge(
                                    BridgeTactic::Side,
                                    vec![],
                                ));
                                by_ways(ways)
                            }
                        })
                    }
                },
            },
            // A requires line's lines, or one manipulation of one of them:
            // the fact is what they say, or follows from it by arithmetic.
            Head::Lines | Head::Manipulation(_) => Route::Built(side_proof()),
        }
    }

    /// Where a step takes the counts its claim or the lines it cites say
    /// in ℕ∞, |X| = |Y| + 1 (`Writer::said_in_extended`), to the integers
    /// they are, `parley_count_int`. A step that computes by a ring or an
    /// order does so first, wherever a count is in ℕ∞, which is neither.
    /// One that rewrites or reasons does so first only where its lines say
    /// counts both ways, as a rewrite in ℕ∞ meets ℕ∞ lines as they are. A
    /// calculation, and substitute rows, build their lines inside the step
    /// as they are written, so the step takes what they build and the goal
    /// to integers together, after; each row is taken as a step of its own
    /// (`substitute_rows`).
    fn count_conversion(
        &self,
        m: Method,
        claim: &Node,
        just: &Justification,
    ) -> CountConversion {
        let cited = self.cited_parts(&just.refs);
        let lines: Vec<&Node> = std::iter::once(claim)
            .chain(cited.iter().map(|c| &c.node))
            .collect();
        let forms = self.count_forms(&lines);
        match m {
            Method::Calculation if forms.extended => CountConversion::After,
            Method::Substitute if !just.rows.is_empty() && forms.extended => {
                CountConversion::After
            }
            Method::Algebra | Method::Arithmetic | Method::Inequalities
                if forms.extended =>
            {
                CountConversion::Before
            }
            Method::Substitute
            | Method::Transitivity
            | Method::Antisymmetry
            | Method::Restate
                if forms.mixed =>
            {
                CountConversion::Before
            }
            _ => CountConversion::None,
        }
    }

    /// How these lines say their counts: whether one says a count in ℕ∞,
    /// and whether one set's count is said both in ℕ∞ and as an integer,
    /// |A| = 0 beside |A| ∈ ℕ of a finite A.
    fn count_forms(&self, lines: &[&Node]) -> CountForms {
        let mut forms: std::collections::BTreeMap<String, CountSaid> =
            std::collections::BTreeMap::new();
        for line in lines {
            self.note_counts(line, None, &mut forms);
        }
        CountForms {
            extended: forms.values().any(|f| f.extended),
            mixed: forms.values().any(|f| f.extended && f.integer),
        }
    }

    /// Each set this node counts, with how the relation the count stands in
    /// says it: in ℕ∞ (`Writer::said_in_extended`) or as an integer.
    /// `extended` is that of the relation nearest above, if any.
    fn note_counts(
        &self,
        node: &Node,
        extended: Option<bool>,
        forms: &mut std::collections::BTreeMap<String, CountSaid>,
    ) {
        let counting = |n: &Node| {
            n.walk()
                .iter()
                .any(|c| &*c.notation_name() == "cardinality")
        };
        let relation = matches!(
            node.notation(),
            crate::notations::EQUALITY
                | crate::notations::ORDER
                | crate::notations::MEMBERSHIP
        );
        let extended = match relation && counting(node) {
            true => {
                Some(self.writer.said_in_extended(node) || self.writer.counts(node))
            }
            false => extended,
        };
        if let (Some(e), "cardinality", [set]) =
            (extended, &*node.notation_name(), node.children.as_slice())
        {
            let said = forms
                .entry(self.sources.checked.grammar.print(set))
                .or_default();
            match e {
                true => said.extended = true,
                false => said.integer = true,
            }
        }
        for c in &node.children {
            self.note_counts(c, extended, forms);
        }
    }

    /// A claim's leading "for all" taken off: the names its letters and
    /// their guards are introduced by, the body, and the letters in scope
    /// with the claim's own added.
    fn peel<'n>(&self, node: &'n Node) -> (Vec<String>, &'n Node, Writer<'a>) {
        let mut writer = self.writer.with_letters(self.writer.letters.clone());
        let mut intros = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let name = super::names::letter(&letter.text);
            // Over a range, a number system or another set of numbers, [0,
            // 1]: the letter of the numbers' type, and where the type does
            // not say it, the fact that it is in the set. Over a set of
            // things, sets or a group's elements, a member of their type,
            // and the fact.
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                writer.introduce(&letter.text, super::expr::range_letter_system(set));
                (None, true)
            } else {
                match (super::expr::system_of(set), self.writer.set_members(set)) {
                    (Some(s), _) => {
                        writer.introduce(&letter.text, s);
                        (None, !matches!(s, super::expr::System::Type(_)))
                    }
                    (None, Some(super::expr::Members::Numbers(n))) => {
                        (Some(LetterType::Number(n)), true)
                    }
                    (None, Some(m)) => (Some(LetterType::Member(m)), true),
                    (None, None) => break,
                }
            };
            if let Some(ty) = ty {
                writer.letters.insert(letter.text.to_string(), ty);
                writer.wholes.shift_remove(&*letter.text);
            }
            intros.push(name.clone());
            if guarded {
                intros.push(format!("h_{name}"));
            }
            body = inner;
        }
        (intros, body, writer)
    }

    /// The proof of a claim by a method that closes it, with the letters
    /// `writer` holds.
    fn method_proof(
        &self,
        reason: Reason,
        m: Method,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let just = reason.just;
        Route::Built(match m {
            Method::Algebra => {
                // A cited equation of a narrower type is combined as the
                // claim's type has it.
                let mut cited = self.cited_parts(&just.refs);
                for c in &mut cited {
                    if let Some(read) = self.read_at_claim(c, node) {
                        *c = read;
                    }
                }
                // A define the step cites is written out, in the claim and
                // in each line it cites, as the checker reads the step: in
                // Lean, its equation rewrites them all, and the casts it
                // leaves are pushed in. Lines are widened after, as they
                // then read.
                // A define's value may name another the step cites, v's of
                // ω₁, so they are written out until none is left.
                let defines = self.cited_defines(&just.refs);
                let mut claim = node.clone();
                for d in &defines {
                    cited.retain(|c| c.proof != d.proof);
                }
                let grammar = &self.sources.checked.grammar;
                let printed =
                    |claim: &Node, cited: &[super::algebra::Cited]| -> Vec<String> {
                        std::iter::once(claim)
                            .chain(cited.iter().map(|c| &c.node))
                            .map(|n| grammar.print(n))
                            .collect()
                    };
                for _ in 0..=defines.len() {
                    let before = printed(&claim, &cited);
                    for d in &defines {
                        claim = self.put_define(&claim, d);
                        for c in &mut cited {
                            c.node = self.put_define(&c.node, d);
                        }
                    }
                    if printed(&claim, &cited) == before {
                        break;
                    }
                }
                let mut haves = Vec::new();
                for c in &mut cited {
                    match self.widened(&c.node, &c.proof, &claim, writer) {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            c.proof = w.name;
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // Each read with its identity elements dropped, as the
                // checker decides it: F(0 + 1) and F(1) are one term.
                let ctx = self.sources.ctx;
                let claim = crate::matching::bare(&claim, ctx);
                for c in &mut cited {
                    c.node = crate::matching::bare(&c.node, ctx);
                }
                let proof = match super::algebra::algebra(
                    writer,
                    self.sources.targets,
                    &claim,
                    &cited,
                ) {
                    Route::Built(p) => p.text(),
                    Route::Declined(d) => return Route::Declined(d),
                };
                let mut lines = written_out(&defines);
                lines.extend(haves);
                return Route::Built(with_haves(&lines, &proof));
            }
            Method::Arithmetic => super::doc::Proof::By(super::tactics::bridge(
                BridgeTactic::Arith,
                vec![],
            ))
            .text(),
            // Arithmetic of real numbers, √8 = 2√2 or ln(2) ≠ 0: its own
            // tactic, which tries `parley_arith` first (`RealTactics`).
            Method::RealArithmetic => super::doc::Proof::By(super::tactics::bridge(
                BridgeTactic::Real,
                vec![],
            ))
            .text(),
            // Rows are linear moves on the line the first row cites, so the
            // claim follows from that line by linear arithmetic, as a step
            // with no rows does from the lines it cites.
            // An order is left to the ways of orders alone; a chain of
            // equations, A = B = C, to `parley_side`.
            Method::Inequalities | Method::Transitivity | Method::Antisymmetry => {
                // A cited "for all", a(n) = 1 − 1/2ⁿ for every n, is read
                // at the claim's letter, which linear arithmetic can use.
                let mut steps: Vec<Tactic> = self
                    .cited_parts(&just.refs)
                    .iter()
                    .filter_map(|c| self.read_at_claim(c, node))
                    .map(|at| Tactic::Fact(Printed::atom(at.proof)))
                    .collect();
                let close = match node.notation() == ORDER {
                    true => BridgeTactic::Order,
                    false => BridgeTactic::Side,
                };
                steps.push(super::tactics::bridge(close, vec![]));
                super::doc::Proof::By(Tactic::Seq(steps)).text()
            }
            Method::Inspection => side_proof(),
            Method::Substitute => return self.substitute(just, node, writer),
            Method::Calculation => return self.calculation(just, writer),
            Method::Exhibit => return self.exhibit(just, node),
            Method::Instantiate => return self.instantiate(just, node, writer),
            Method::Membership => return self.membership(just, node, writer),
            Method::Restate | Method::Join => side_proof(),
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        })
    }

    /// A recursion a proof lets, `let N(0) = 0, N(k + 1) = 10·N(k) + d(k +
    /// 1), for k ∈ ℕ₀`: its function, of ℤ into the type its rules compute
    /// in, obtained from `recursion_exists`, and its rules one hypothesis
    /// named by its label, as a recursion the header lets is written
    /// (`header_recursions`), which a step cites alike. A recursion of
    /// several functions, over other than ℕ₀, or whose step applies its
    /// function at other than k, is declined.
    fn define_recursion(
        &mut self,
        d: usize,
        r: &crate::corpus::Recursion,
        depth: usize,
    ) -> Route<()> {
        use super::templates::Num;
        let line = self.thm.defines[d].clone();
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(r, &line, self.rec) {
            Route::Built(rules) => rules,
            Route::Declined(why) => return Route::Declined(why),
        };
        let [rule] = rules.as_slice() else {
            return Route::no("a recursion of several functions a proof lets");
        };
        let saved = self.writer.letters.clone();
        self.writer
            .letters
            .insert(r.index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for n in [&rule.start, &rule.step] {
            self.writer.letters.insert(
                rule.name.clone(),
                LetterType::Function { from: Num::Int, to },
            );
            match self.writer.carrier(n) {
                Route::Built(c) => to = to.max(c),
                Route::Declined(why) => {
                    self.writer.letters = saved;
                    return Route::Declined(why);
                }
            }
        }
        let ty = LetterType::Function { from: Num::Int, to };
        self.writer.letters.insert(rule.name.clone(), ty.clone());
        // The step as `recursion_exists` takes it: of k and the value at k,
        // N(k) in it a letter for that value.
        let previous = fresh_letter(&self.writer, &r.index);
        let at_index = rule
            .step
            .walk()
            .into_iter()
            .find(|n| applied_at(n, rule.name, &r.index));
        let stepped = match &at_index {
            Some(at) => super::expr::put_for(
                &rule.step,
                at,
                &Node::name(crate::formula::Sort::none(), &previous),
            ),
            None => rule.step.clone(),
        };
        let still_applied = stepped
            .walk()
            .iter()
            .any(|n| n.is_name() && &*n.text == rule.name.as_str());
        self.writer
            .letters
            .insert(previous.clone(), LetterType::Number(to));
        let written = (
            self.writer.number_fixed(&rule.start, to),
            self.writer.number_fixed(&rule.step, to),
            self.writer.number_fixed(&stepped, to),
        );
        self.writer.letters = saved;
        self.writer.letters.insert(rule.name.clone(), ty);
        if still_applied {
            return Route::no(
                "a recursion whose step applies its function at other than k",
            );
        }
        let (start, step, by_previous) = match written {
            (Route::Built(s), Route::Built(t), Route::Built(g)) => (s, t, g),
            (Route::Declined(why), _, _)
            | (_, Route::Declined(why), _)
            | (_, _, Route::Declined(why)) => return Route::Declined(why),
        };
        let f = super::names::letter(rule.name);
        let k = super::names::letter(&r.index);
        let v = super::names::letter(&previous);
        let label = line_name(&line.label);
        use super::doc::Piece;
        let rules = Printed::notation(
            vec![
                Piece::text(format!("∃ {f} : ℤ → {}, {f} 0 = ", to.lean())),
                Piece::term(start, 51),
                Piece::text(format!(" ∧ ∀ {k} : ℤ, 0 ≤ {k} → {f} ({k} + 1) = ")),
                Piece::term(step, 51),
            ],
            0,
            super::doc::LeanType::Prop,
        );
        let exists = Printed::notation(
            vec![
                Piece::term(
                    super::tactics::bridge_lemma(
                        "LeanBridges.Functions.recursion_exists",
                        BridgeModule::Functions,
                    ),
                    0,
                ),
                Piece::text(format!(" _ (fun {k} {v} => ")),
                Piece::term(by_previous, 0),
                Piece::text(")"),
            ],
            super::expr::APP,
            super::doc::LeanType::Prop,
        );
        self.push_at(
            depth,
            Tactic::Obtain {
                names: vec![f, label.clone()],
                says: Some(rules),
                from: exists,
            },
            line.line,
            Spot::Statement,
        );
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define in a proof, `let t = 1/j, a real number`: Lean's `set`, of
    /// the type the line names, or else of the least that holds its value,
    /// whose hypothesis is the define's equation, named by its label.
    fn define(&mut self, d: usize, depth: usize) -> Route<()> {
        self.defined.insert(d);
        let line = &self.thm.defines[d];
        let def = match crate::corpus::define_parts(&line.text) {
            Route::Built(crate::corpus::DefineParts::One(def)) => def,
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => {
                return self.define_recursion(d, &r, depth)
            }
            _ => return Route::no("a define of a phrase"),
        };
        if !def.params.is_empty() {
            return self.define_function(d, &def, depth);
        }
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        let body = (*body).clone();
        // A name for an element or a set, `let b = a⁻¹`: of the type its
        // value has, written as the writer writes such terms.
        let set_like = self
            .writer
            .member_kind(&body)
            .map(|m| m.letter())
            .or_else(|| self.writer.members_of(&body).map(LetterType::Set));
        if let Some(ty) = set_like.filter(|_| def.kind.is_none()) {
            let value = match self.writer.set_term(&body) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.name_value(d, &def.name, ty, &value.text(), body, depth);
            return Route::Built(());
        }
        use super::templates::Num;
        // A positive or nonnegative whole number is a natural number named
        // from its kind's fact, whatever its value's type, as `let m ∈ ℕ`
        // names one and as the elaborator puts the name among ℕ's members
        // once the kind is shown (`GOALS.md` decision 20).
        if matches!(
            def.kind.as_deref(),
            Some("a positive integer" | "a natural number" | "a nonnegative integer")
        ) {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let ty = match def.kind.as_deref() {
            Some("a real number") => Num::Real,
            Some("a rational number") => Num::Rat,
            Some("an integer") => Num::Int,
            Some("a complex number") => Num::Complex,
            Some(other) => return Route::no(format!("a define of {other}")),
            None => match self.writer.carrier(&body) {
                Route::Built(n) => n,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        // An integer whose value is wider, `let e = p/d, an integer`: Lean's
        // ℤ division would round, so the name is the number its reason
        // shows the value to be.
        let wider = match self.writer.carrier(&body) {
            Route::Built(n) => n > ty,
            Route::Declined(why) => return Route::Declined(why),
        };
        if def.kind.is_some() && wider {
            return self.kinded_witness(d, &def.name, body, depth);
        }
        let value = match self.writer.number_fixed(&body, ty) {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        self.name_value(
            d,
            &def.name,
            LetterType::Number(ty),
            &value.text(),
            body,
            depth,
        );
        // A define of a kind whose value is already of the type, `let n =
        // a·b, an integer`: the kind's fact is still a line, proved by the
        // define's reason.
        if def.kind.is_some() {
            let KindShown { says, proof, .. } = match self.kind_shown(d) {
                Route::Built(s) => s,
                Route::Declined(why) => return Route::Declined(why),
            };
            let line = &self.thm.defines[d];
            let label = line_name(&line.label);
            self.push_at(
                depth,
                Tactic::Have {
                    name: format!("{label}_kind"),
                    says,
                    proof,
                },
                line.line,
                Spot::Statement,
            );
        }
        Route::Built(())
    }

    /// What closes a block or a theorem once its steps are written: its last
    /// step by name, `exact s3`, where that step says what is owed as Lean
    /// writes both, and otherwise `parley_side`, which finds the line. What
    /// is owed is the claim, or of a "for all" whose letter the block lets,
    /// what it says at that letter.
    fn closing(&self, last: Option<usize>, owed: &Node) -> Tactic {
        let side = super::tactics::bridge(BridgeTactic::Side, vec![]);
        let owed = match owed.children.as_slice() {
            [letter, _, body]
                if owed.notation() == crate::notations::FOR_ALL
                    && self.writer.letters.contains_key(letter.text.as_str()) =>
            {
                body
            }
            _ => owed,
        };
        let Some(number) = last.and_then(|i| self.thm.steps[i].number.number()) else {
            return side;
        };
        let Some([(said, name)]) =
            self.trees.get(&number.to_string()).map(Vec::as_slice)
        else {
            return side;
        };
        match (self.writer.formula(said), self.writer.formula(owed)) {
            (Route::Built(a), Route::Built(b)) if a.text() == b.text() => {
                Tactic::Exact(super::tactics::hyp(name))
            }
            _ => side,
        }
    }

    /// A define's name given its value, `set b : G := a⁻¹ with hD1`: the
    /// letter of its type, and the line's equation, b = a⁻¹, by its label.
    fn name_value(
        &mut self,
        d: usize,
        name: &str,
        ty: LetterType,
        value: &str,
        body: Node,
        depth: usize,
    ) {
        let line = &self.thm.defines[d];
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        self.push_at(
            depth,
            Tactic::Set {
                name: super::names::letter(name),
                ty: ty.lean_type(),
                value: Printed::atom(value),
                with: label.clone(),
            },
            at,
            Spot::Statement,
        );
        self.writer.letters.insert(name.to_string(), ty);
        let letter = Node::name(body.sort.clone(), name);
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![letter, body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.trees.insert(page_label, vec![(equation, label)]);
    }

    /// The fact a define of a kind says of its value, `gcd(t, w) ∈ ℕ` of
    /// `let n = gcd(t, w), a positive integer`, as Lean writes it, and its
    /// proof by the define's reason.
    fn kind_shown(&self, d: usize) -> Route<KindShown> {
        let line = &self.thm.defines[d];
        let members = &self.sources.checked.grammar.members;
        let kinded = match line.kinded(&self.thm.path, members) {
            Ok(Some(k)) => k,
            Ok(None) => return Route::no("a define of a kind with no reason"),
            Err(p) => return Route::no(p.to_string()),
        };
        let fact = match self.tree(&kinded.shown.fact) {
            Route::Built(n) => n,
            Route::Declined(why) => return Route::Declined(why),
        };
        let says = match self.writer.formula(&fact) {
            Route::Built(f) => f,
            Route::Declined(why) => return Route::Declined(why),
        };
        let Ok(just) = &kinded.shown.by else {
            return Route::no("a define whose reason does not read");
        };
        let reason = Reason {
            just,
            cited: self.rec.cited_requires.get(&kinded.shown.line),
        };
        let proof = match self.proof_of(reason, 0, &fact) {
            Route::Built(p) => p,
            Route::Declined(why) => return Route::Declined(why),
        };
        Route::Built(KindShown { fact, says, proof })
    }

    /// A define naming a whole number its value is shown to be, `let e =
    /// p/d, a positive integer` with `p/d ∈ ℕ` its reason's fact: that
    /// fact proved by the reason, as a requires line is, and the name taken
    /// from it, `obtain ⟨e, hD1_pos, hD1⟩`, so that the define's equation
    /// e = p/d is said in the value's type.
    fn kinded_witness(
        &mut self,
        d: usize,
        name: &str,
        body: Node,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let shown = match self.kind_shown(d) {
            Route::Built(s) => s,
            Route::Declined(why) => return Route::Declined(why),
        };
        let KindShown { fact, says, proof } = shown;
        let kind_line = Tactic::Have {
            name: format!("{}_kind", line_name(&line.label)),
            says,
            proof,
        };
        let [_, set] = fact.children.as_slice() else {
            return Route::no("a kind's fact that is no membership");
        };
        // The letter is an integer whatever its kind; ℕ and ℕ₀ say its order
        // beside it, 0 < e or 0 ≤ e, as `let e ∈ ℕ` does.
        let system = match super::expr::system_of(set) {
            Some(
                s @ (super::expr::System::Positive | super::expr::System::NonNegative),
            ) => s,
            Some(s @ super::expr::System::Type(super::templates::Num::Int)) => s,
            _ => return Route::no("a define of a kind other than ℕ, ℕ₀ or ℤ"),
        };
        let ordered = !matches!(system, super::expr::System::Type(_));
        let ty = super::templates::Num::Int;
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter = super::names::letter(name);
        // A value of integers, k + 1, is the letter as any define's value
        // is: Lean's `set` of it, which a step citing the define unfolds
        // (`cited_defines`); its kind said as an order of the value, 0 < k +
        // 1, which the `set` makes an order of the letter.
        let integer = self
            .writer
            .carrier(&body)
            .built()
            .is_some_and(|n| n <= super::templates::Num::Int);
        if integer {
            let value = match self.writer.number_fixed(&body, ty) {
                Route::Built(v) => v.text(),
                Route::Declined(why) => return Route::Declined(why),
            };
            self.push_at(depth, kind_line, at, Spot::Statement);
            self.name_value(d, name, LetterType::Number(ty), &value, body, depth);
            self.writer.introduce(name, system);
            if ordered {
                self.push_at(
                    depth,
                    Tactic::Name {
                        name: format!("{label}_pos"),
                        term: super::tactics::hyp(&format!("{label}_kind")),
                    },
                    at,
                    Spot::Statement,
                );
            }
            return Route::Built(());
        }
        // A value of a wider type, p/d: its kind's fact is a witness, `∃ m :
        // ℤ, 0 < m ∧ (m : ℚ) = p/d`, and the letter is that m.
        let names = match ordered {
            true => vec![letter.clone(), format!("{label}_pos"), label.clone()],
            false => vec![letter.clone(), label.clone()],
        };
        self.push_at(depth, kind_line, at, Spot::Statement);
        self.push_at(
            depth,
            Tactic::Obtain {
                names,
                says: None,
                from: super::tactics::hyp(&format!("{label}_kind")),
            },
            at,
            Spot::Statement,
        );
        self.writer.introduce(name, system);
        self.witness_letters.push(WitnessLetter {
            value: body.clone(),
            letter: Node::name(body.sort.clone(), name),
        });
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![Node::name(body.sort.clone(), name), body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.witnessed.insert(page_label.clone());
        self.trees.insert(page_label, vec![(equation, label)]);
        Route::Built(())
    }

    /// A define of a function of one number in a proof, `let S(m) =
    /// Σ(j = 1 to m) 3^j, for m ∈ ℕ`: Lean's `set` of a function from the
    /// type of the set its argument runs over to the least type holding its
    /// value, whose hypothesis, named by the label, a step citing the define
    /// unfolds it by (`written_out`).
    fn define_function(
        &mut self,
        d: usize,
        def: &crate::corpus::Define,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let [param] = def.params.as_slice() else {
            return Route::no("a define of a function of more than one argument");
        };
        if set_valued(self.rec, &def.name) {
            return Route::no(SET_VALUED);
        }
        // The checker reads the line's argument, the set it runs over and
        // the value apart.
        let read: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let over = |n: &&&Node| {
            matches!(
                n.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            )
        };
        // Over a number system, a range, or a set of numbers, X of X ⊆ ℤ.
        let of_numbers = |n: &&&Node| {
            !(n.is_name() && *n.text == *param.name)
                && matches!(
                    self.writer.set_members(n),
                    Some(super::expr::Members::Numbers(_))
                )
        };
        let Some(domain) = read
            .iter()
            .find(over)
            .or_else(|| read.iter().find(of_numbers))
        else {
            return Route::no("a define of a function on other than a number system");
        };
        // The value is what the line reads besides the domain and the
        // argument; a value that is itself a set of numbers, {|x| : x ∈
        // 𝒫{1, …, k}}, is not the domain.
        let bodies: Vec<&&Node> = read
            .iter()
            .filter(|n| !std::ptr::eq(**n, *domain))
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        // A function on ℕ, ℕ₀ or a range {0, …, m} takes integers, as the
        // writer's sequences do, so that q(j) of a sum's index is written
        // as it stands; its values off the range are none of the page's.
        let from = match (
            super::expr::system_of(domain),
            self.writer.set_members(domain),
        ) {
            (Some(system), _) => {
                super::expr::letter_type(system).max(super::templates::Num::Int)
            }
            (None, _) if domain.notation() == crate::notations::INTEGER_RANGE => {
                super::templates::Num::Int
            }
            (None, Some(super::expr::Members::Numbers(n))) => {
                n.max(super::templates::Num::Int)
            }
            (None, _) => {
                return Route::no(
                    "a define of a function on a set Lean has no type for",
                )
            }
        };
        // The value is read with the argument a number of that type, in ℕ
        // or ℕ₀ where the domain or range puts it, 10^k of k ∈ ℕ₀ written as
        // the steps write it; the argument is no letter of the proof's
        // after it.
        let system = match super::expr::system_of(domain) {
            Some(s) => Some(s),
            None if domain.notation() == crate::notations::INTEGER_RANGE => {
                Some(super::expr::range_letter_system(domain))
            }
            None => None,
        };
        let whole_before = self.writer.wholes.get(&param.name).copied();
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), LetterType::Number(from));
        if let Some(s) = system {
            self.writer.introduce(&param.name, s);
        }
        // Of a real or complex argument, values of that type at least, as a
        // header function's are (`header_function`).
        let value = match self.writer.carrier(body) {
            Route::Built(to) => {
                let to = match from >= super::templates::Num::Real {
                    true => to.max(from),
                    false => to,
                };
                self.writer.number_fixed(body, to).map(|v| (to, v))
            }
            Route::Declined(why) => Route::Declined(why),
        };
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        match whole_before {
            Some(s) => self.writer.wholes.insert(param.name.clone(), s),
            None => self.writer.wholes.shift_remove(&param.name),
        };
        let (to, value) = match value {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        let name = super::names::letter(&def.name);
        let label = line_name(&line.label);
        let function = LetterType::Function { from, to }.lean_type();
        let lambda = Printed::notation(
            vec![
                super::doc::Piece::text(format!(
                    "fun {} => ",
                    super::names::letter(&param.name)
                )),
                super::doc::Piece::term(value, 0),
            ],
            0,
            function.clone(),
        );
        self.push_at(
            depth,
            Tactic::Set {
                name: name.clone(),
                ty: function,
                value: lambda,
                with: label.clone(),
            },
            line.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Function { from, to });
        // Of real or complex numbers on a set, [0, 1]: its domain, within
        // which its limits and derivatives are taken (`domain_of`), as a
        // header function's is.
        let whole = matches!(
            super::expr::system_of(domain),
            Some(super::expr::System::Type(_))
        );
        if !whole && from >= super::templates::Num::Real {
            match self.writer.numbers_at(domain, from) {
                Route::Built(p) => {
                    self.writer.domains.insert(def.name.clone(), p);
                }
                Route::Declined(why) => return Route::Declined(why),
            }
        }
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define of the theorem's file, outside the theorem, that its
    /// statement is read with: Lean's `set`, of the least type holding the
    /// term it names, its equation named by the name.
    fn define_outside(&mut self, name: &str, body: &Node) -> Route<()> {
        let ty = match self.writer.carrier(body) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let value = match self.writer.number_fixed(body, ty) {
            Route::Built(v) => v,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lean = super::names::letter(name);
        let line = self.thm.line;
        self.push_at(
            1,
            Tactic::Set {
                name: lean.clone(),
                ty: self.writer.num_type(ty),
                value,
                with: format!("h_{lean}"),
            },
            line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(name.to_string(), LetterType::Number(ty));
        Route::Built(())
    }

    /// `exhibit`: the claim's "there is", with the values the checker read
    /// for its letters, and what it says of them left to `parley_side`.
    fn exhibit(&self, just: &Justification, node: &Node) -> Route<String> {
        let Some(step) = self.thm.steps.iter().find(|s| s.just.line == just.line)
        else {
            return Route::no("an exhibit that is no step's");
        };
        let Some(binding) = self
            .rec
            .exhibited
            .get(&step.line)
            .and_then(|all| all.iter().flatten().next())
        else {
            return Route::no("an exhibit the checker read no values for");
        };
        // there is a ∈ X with nothing said of a, `∃ a ∈ X, True`: the
        // member, that it is in X, and nothing.
        if let ("there-is-some", [letter, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let Some(members) = self.writer.set_members(set) else {
                return Route::no("there is some member of a set with no Lean type");
            };
            return self
                .writer
                .element_term(value, &members)
                .map(|v| format!("⟨{}, by parley_set_side, trivial⟩", v.text()));
        }
        let mut parts = Vec::new();
        let mut known = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            // A member of a set: the value as the writer writes a member,
            // and its membership left to `parley_side`.
            if let Some(members) = self.writer.members_of(set) {
                match self.writer.element_term(value, &members) {
                    Route::Built(p) => parts.push(p.text()),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            }
            // A polynomial: the function, and that it is one.
            if &*set.notation_name() == "polynomials" {
                match self.writer.set_term(value) {
                    Route::Built(p) => parts.push(p.text()),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            }
            // A function between sets of numbers: the function, of the
            // types the quantifier gives it, and that it maps the one set
            // into the other.
            if let ("functions-from", [from, to]) =
                (&*set.notation_name(), set.children.as_slice())
            {
                let wanted = match self.writer.function_between(from, to) {
                    Some(LetterType::Function { from, to }) => (from, to),
                    _ => {
                        return Route::no("a function given between sets of no numbers")
                    }
                };
                match self.writer.function_type(value) {
                    Route::Built(t) if t == wanted => {
                        parts.push(self.writer.function_printed(value).text())
                    }
                    Route::Built(_) => {
                        return Route::no("a function given for one of other types")
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        !matches!(s, super::expr::System::Type(_)),
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match self.witness(value, ty) {
                Route::Built(w) => {
                    parts.push(w.term);
                    known.extend(w.known);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            if guarded {
                parts.push(format!("by {}parley_side", known.concat()));
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::no("an exhibit of no \"there is\"");
        }
        parts.push(facts_shaped(body, &known.concat()));
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// `instantiate`: the "for all" line at the values given, each guard
    /// left to `parley_side`, and an "if" in it applied where the claim is
    /// what it gives.
    fn instantiate(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let Some(target) = just
            .target
            .as_deref()
            .or(just.refs.first().map(String::as_str))
        else {
            return Route::no("an instantiate of no line");
        };
        // The sentence, or the part of one, of the line that says "for all".
        let parts = self.cited_parts(&[target.to_string()]);
        // Of several, the one that asks the fewest conditions of the values.
        let conditions = |n: &Node| -> usize {
            let mut body = n;
            let mut asked = 0;
            while let [_, set, inner] = body.children.as_slice() {
                if body.notation() != crate::notations::FOR_ALL {
                    break;
                }
                let guarded = set.notation() == crate::notations::INTEGER_RANGE
                    || super::expr::system_of(set)
                        == Some(super::expr::System::Positive);
                asked += usize::from(guarded);
                body = inner;
            }
            asked + usize::from(matches!(body.notation(), CONDITIONAL | IMPLICATION))
        };
        // The sentences that bind every letter the step gives a value, u
        // of `u := b`, where any does; a line may say "for all" of several.
        let binds_given = |n: &Node| {
            let mut bound = Vec::new();
            let mut body = n;
            while let [letter, _, inner] = body.children.as_slice() {
                if body.notation() != crate::notations::FOR_ALL {
                    break;
                }
                bound.push(letter.text.to_string());
                body = inner;
            }
            just.values.names().all(|v| bound.iter().any(|b| b == v))
        };
        let quantified: Vec<&super::algebra::Cited> = parts
            .iter()
            .filter(|c| c.node.notation() == crate::notations::FOR_ALL)
            .collect();
        let binding: Vec<&super::algebra::Cited> = quantified
            .iter()
            .copied()
            .filter(|c| binds_given(&c.node))
            .collect();
        let chosen = match binding.is_empty() {
            true => quantified,
            false => binding,
        };
        let Some(part) = chosen.into_iter().min_by_key(|c| conditions(&c.node)) else {
            return Route::no(format!(
                "instantiate in {target}, which says no \"for all\""
            ));
        };
        // With no values given, the line is read at the block's letter, as
        // the checker reads it.
        if just.values.is_empty() {
            if let Some(read) = self.read_at_claim(part, node) {
                return Route::Built(close(&self.writer, node, &read.proof));
            }
        }
        let (line, name) = (&part.node, &part.proof);
        let mut args = vec![name.clone()];
        let mut body = line;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            // A letter given no value is read at the block's letter of its
            // type the claim writes and the line does not, as the checker
            // reads it.
            let value = match just.values.pairs().find(|(n, _)| *n == &*letter.text) {
                Some((_, given)) => match self.tree(given) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                },
                None => {
                    // The names the line writes free: a letter it binds
                    // itself, as the block's may be named, is not one.
                    let own = crate::matching::free_names(
                        line,
                        &self.sources.checked.grammar.binders(),
                    );
                    // A range's letter is an integer.
                    let ty = if set.notation() == crate::notations::INTEGER_RANGE {
                        Some(super::templates::Num::Int)
                    } else {
                        super::expr::system_of(set).map(super::expr::letter_type)
                    };
                    // A set's letter is a member of its kind.
                    let member = writer.members_of(set).map(|m| m.letter());
                    // Where several fit, a letter given to another of the
                    // line's letters, the N of `m := N`, is that one's value
                    // and not this one's.
                    let given: Vec<String> = just
                        .values
                        .pairs()
                        .filter_map(|(_, v)| self.tree(v).built())
                        .flat_map(|v| v.names())
                        .collect();
                    let fits = |n: &String| {
                        let has = writer.letters.get(n.as_str());
                        !own.contains(n)
                            && (ty.is_some_and(|t| has == Some(&LetterType::Number(t)))
                                || (member.is_some() && has == member.as_ref()))
                    };
                    let mut at: Vec<String> =
                        node.names().into_iter().filter(|n| fits(n)).collect();
                    if at.len() > 1 {
                        at.retain(|n| !given.contains(n));
                    }
                    // A claim that is itself a "for all" keeps the letters
                    // given no value: the line is read at those given.
                    let [at] = at.as_slice() else {
                        if node.notation() == crate::notations::FOR_ALL {
                            break;
                        }
                        return Route::no(format!("no value for {}", letter.text));
                    };
                    Node::name(letter.sort.clone(), at)
                }
            };
            // A member of a set: the value, and that it is in the set.
            if let Some(members) = writer.members_of(set) {
                match writer.element_term(&value, &members) {
                    Route::Built(p) => args.push(p.at(super::expr::MAX)),
                    Route::Declined(d) => return Route::Declined(d),
                }
                args.push("(by parley_side)".to_string());
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        !matches!(s, super::expr::System::Type(_)),
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match writer.number_fixed(&value, ty) {
                Route::Built(p) => {
                    args.push(p.at(super::expr::MAX));
                    if guarded {
                        args.push("(by parley_side)".to_string());
                    }
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            body = inner;
        }
        let gives = matches!(body.notation(), CONDITIONAL | IMPLICATION)
            && !matches!(node.notation(), CONDITIONAL | IMPLICATION);
        if gives {
            args.push("(by parley_side)".to_string());
        }
        let term = format!("({})", args.join(" "));
        Route::Built(close(&self.writer, node, &term))
    }

    /// The defines among the lines a step cites, each as its equation says
    /// it: the checker reads such a step with them written out.
    fn cited_defines(&self, refs: &[String]) -> Vec<CitedDefine> {
        let mut out: Vec<CitedDefine> = refs
            .iter()
            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
            .filter(|r| !self.witnessed.contains(*r))
            .flat_map(|r| self.trees.get(r).into_iter().flatten())
            .filter_map(|(n, proof)| match n.children.as_slice() {
                [name, value] if n.notation() == EQUALITY && name.is_name() => {
                    Some(CitedDefine {
                        name: name.clone(),
                        value: value.clone(),
                        proof: proof.clone(),
                        param: None,
                    })
                }
                _ => None,
            })
            .collect();
        out.extend(refs.iter().filter_map(|r| self.cited_function_define(r)));
        out
    }

    /// A define of a function of one argument a step cites by its label,
    /// q(j) = F(j)²: its name, its body, its argument and the name of the
    /// line Lean's `set` gives it; None for any other reference.
    fn cited_function_define(&self, label: &str) -> Option<CitedDefine> {
        let line = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line > self.thm.conclusion_line)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .filter(|n| n.notation() != crate::notations::NUMBER_SYSTEMS)
            .filter(|n| !(n.is_name() && *n.text == *param.name))
            .collect();
        let [body] = bodies.as_slice() else {
            return None;
        };
        let proof = self.named.get(label)?.first()?.clone();
        Some(CitedDefine {
            name: Node::name(crate::formula::Sort::none(), &def.name),
            value: (*body).clone(),
            proof,
            param: Some(param.name.clone()),
        })
    }

    /// A line with a cited define put in: its name for its value, or each
    /// application q(a) of a function's for its body at a.
    fn put_define(&self, node: &Node, d: &CitedDefine) -> Node {
        let Some(param) = &d.param else {
            return put_for(node, &d.name, &d.value);
        };
        if let (crate::notations::APPLICATION, [f, a]) =
            (node.notation(), node.children.as_slice())
        {
            if f.is_name() && f.text == d.name.text {
                let a = self.put_define(a, d);
                let put = crate::matching::Binding::from([(
                    crate::formula::symbol::Symbol::of(param),
                    a,
                )]);
                return crate::matching::substitute_apart_by(
                    &d.value,
                    &put,
                    &self.sources.checked.grammar.binders(),
                );
            }
        }
        if node.children.is_empty() {
            return node.clone();
        }
        node.with_children(
            node.children
                .iter()
                .map(|c| self.put_define(c, d))
                .collect(),
        )
    }

    /// `substitute`: the claim is a line, or the left side of a calculation's
    /// link, with a term put for another by an equation, which a line says
    /// or arithmetic works out.
    fn substitute(
        &self,
        just: &Justification,
        claim: &Node,
        writer: &Writer,
    ) -> Route<String> {
        if !just.rows.is_empty() {
            return self.substitute_rows(just, writer);
        }
        // Substituting from a function the header lets by its value: its
        // equation for every x, put in where f is applied.
        if let Some(crate::corpus::skeleton::Source::At(place)) = &just.source {
            if let Some(hyp) = self.header_function_named(place.named()) {
                return Route::Built(format!(
                    "by (try simp only [{hyp}] at *); first | done | parley_side"
                ));
            }
        }
        let mut haves = Vec::new();
        // The equation's own name, where it is widened to the claim's type.
        let mut stated: Option<String> = None;
        // The equation put in, as a tree.
        let mut put: Option<Node> = None;
        let equation = match (&just.source, &just.equation) {
            (Some(crate::corpus::skeleton::Source::At(place)), written) => {
                // Of a line saying several things, the equation the step
                // writes, as Lean writes both; else the one that turns the
                // claim's left side into its right, as a calculation's row
                // "= 0² + 0²  substitute D1" puts B = 0 of "A = 0 and B = 0";
                // else its first equation.
                let wanted = written
                    .as_ref()
                    .and_then(|w| self.tree(w).built())
                    .and_then(|n| self.writer.formula(&n).built())
                    .map(|p| p.text());
                let parts = self.cited_parts(&[place.named().to_string()]);
                let grammar = &self.sources.checked.grammar;
                let chosen = parts
                    .iter()
                    .find(|c| {
                        wanted.is_some()
                            && self.writer.formula(&c.node).built().map(|p| p.text())
                                == wanted
                    })
                    .or_else(|| {
                        (claim.notation() == crate::notations::EQUALITY)
                            .then(|| {
                                parts.iter().find(|c| {
                                    c.node.notation() == crate::notations::EQUALITY
                                        && makes_claim(&c.node, claim, grammar)
                                })
                            })
                            .flatten()
                    })
                    .or_else(|| {
                        parts
                            .iter()
                            .find(|c| c.node.notation() == crate::notations::EQUALITY)
                    })
                    .or(parts.first())
                    .map(|c| (c.node.clone(), c.proof.clone()));
                // Put into a line Lean's types give, `⌊A⌋ ∈ ℤ`, the claim is
                // a membership the equation shows.
                if let Some((line, name)) = &chosen {
                    if let Some(proof) = member_by_equation(
                        &self.writer,
                        line,
                        name,
                        claim,
                        self.sources.ctx,
                    ) {
                        return Route::Built(proof);
                    }
                }
                match chosen.as_ref().map(|(n, p)| (n, p)) {
                    Some((line, name)) => match self.widened(line, name, claim, writer)
                    {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            stated = Some(name.clone());
                            put = Some(line.clone());
                            w.name
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    None => {
                        return Route::no(format!(
                            "substitute from {}, which has no Lean name",
                            place.named()
                        ))
                    }
                }
            }
            (_, Some(written)) => {
                let node = match self.tree(written) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // An equation shown by real arithmetic where it is put, ln(8)
                // = 3·ln(2) (real arithmetic), is the real arithmetic's.
                let real = matches!(
                    just.source,
                    Some(crate::corpus::skeleton::Source::RealArithmetic)
                );
                let tactic = if real { "parley_real" } else { "parley_side" };
                // Of numerals alone, cos(0) = 1, it is said in the type the
                // claim is computed in, where it is put: `Complex.cos 0` in
                // a line of complex numbers.
                let at = claim
                    .children
                    .iter()
                    .filter_map(|c| self.writer.carrier(c).built())
                    .fold(super::templates::Num::Int, |a, b| a.max(b));
                // Of no letter of the proof's, cos(0) = 1, whose names are
                // the library's functions only.
                let lettered = node
                    .names()
                    .iter()
                    .any(|n| self.writer.letters.contains_key(n.as_str()));
                let said = match !lettered {
                    true => self.writer.closed_formula(&node, at),
                    false => self.writer.formula(&node),
                };
                match said {
                    Route::Built(p) => format!("(show {} by {tactic})", p.text()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::Built(side_proof()),
        };
        // The line put into, cast up to the claim's type where it is
        // narrower. Of a line saying several things, the one the equation
        // turns into the claim; else the one that says what the claim does,
        // divides where the claim divides; else the first.
        let grammar = &self.sources.checked.grammar;
        let turns = |part: &Node| -> bool {
            let Some([left, right]) = put.as_ref().map(|e| e.children.as_slice())
            else {
                return false;
            };
            let want = grammar.print(claim);
            [(left, right), (right, left)].iter().any(|(from, to)| {
                grammar.print(&put_term(part, from, to, grammar)) == want
            })
        };
        // Where no part turns into the claim with the equation put for every
        // place, the equation is put for some places only, gcd(a, b) ∣ b
        // from b ∣ b, and each part that says what the claim does is offered.
        // A "for all" of the line is judged by what it says at the block's
        // letter, p(x) = (x − a)·q(x) + p(a) of "… for all x ∈ ℂ" at x, and
        // put into by its own name, which the tactic rewrites under the
        // quantifier.
        let at_claim = |node: &Node| -> Node {
            let cited = super::algebra::Cited {
                node: node.clone(),
                proof: String::new(),
            };
            self.read_at_claim(&cited, claim)
                .map_or_else(|| node.clone(), |at| at.node)
        };
        let candidates: Vec<&(Node, String)> = just
            .into
            .as_ref()
            .and_then(|place| self.trees.get(place.named()))
            .map(|t| {
                let turned: Vec<_> = t
                    .iter()
                    .filter(|(n, _)| turns(&at_claim(n)))
                    .take(1)
                    .collect();
                if !turned.is_empty() {
                    return turned;
                }
                let alike: Vec<_> = t
                    .iter()
                    .filter(|(n, _)| at_claim(n).notation() == claim.notation())
                    .collect();
                if !alike.is_empty() {
                    return alike;
                }
                t.iter().take(1).collect()
            })
            .unwrap_or_default();
        let mut into = Vec::new();
        // A line put into that says something of the whole number a term
        // is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) * 2 ∧ 2 ^ p − 1 ∣ m`, whose
        // term the equation turns into the claim's whole number, 2^p: the
        // line said of that number, the equation showing it is the term.
        let mut witnessed: Vec<String> = Vec::new();
        for (line, name) in &candidates {
            let Some((term, whole)) = self.writer.wide_in_slot(line) else {
                continue;
            };
            let Some(at) = path_to(line, &term).and_then(|p| at_path(claim, &p)) else {
                continue;
            };
            let Route::Built(w) = self.writer.number_fixed(at, whole) else {
                continue;
            };
            let lemma = match whole {
                super::templates::Num::Nat => "parley_witness_at_nat",
                _ => "parley_witness_at",
            };
            for sign in ["", "-"] {
                witnessed.push(format!(
                    "exact {lemma} {name} ({}) (by push_cast; linear_combination (norm := parley_norm) {sign}{equation})",
                    w.text()
                ));
            }
        }
        for (i, (line, name)) in candidates.into_iter().enumerate() {
            // A "for all" line read at the block's letter, the part of it
            // the equation turns into the claim: line 2's "e(n) ≠ D(f(n),
            // n)" at the block's n, the equation being of that n, which no
            // rewriting under the line's own binder reaches.
            let read = self.read_at_claim(
                &super::algebra::Cited {
                    node: line.clone(),
                    proof: name.clone(),
                },
                claim,
            );
            let mut parts = Vec::new();
            if let Some(at) =
                read.filter(|_| line.notation() == crate::notations::FOR_ALL)
            {
                conjuncts(&at.node, at.proof, &mut parts);
            }
            if let Some(part) = parts.iter().find(|p| turns(&p.node)) {
                let at_name = format!("at{i}");
                haves.push(format!("have {at_name} := {}", part.proof));
                match self.widened(&part.node, &at_name, claim, writer) {
                    Route::Built(w) => {
                        haves.extend(w.have);
                        into.push(w.name);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                continue;
            }
            match self.widened(line, name, claim, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    into.push(w.name);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The equation is put in at the type its term has where it stands:
        // widened to the claim's, or as stated, where the term sits in a
        // part of a fixed type, (4 − 2)! of a claim in ℚ.
        // Of several lines, each is rewritten into before any is simplified,
        // since a simplification that loops ends the search (`parley_put_at`).
        let own = stated.clone().filter(|s| *s != equation);
        // An equation of natural numbers, A = (n + 1)!, put where its term
        // stands as a natural number, the exponent of 2^A: Lean's exponent
        // is of ℕ, so the equation is put there in ℕ.
        let in_nat = match (&put, &stated) {
            (Some(e), Some(name))
                if e.notation() == EQUALITY
                    && e.children.iter().all(|c| self.writer.natural(c)) =>
            {
                let sides: Vec<Route<Printed>> = e
                    .children
                    .iter()
                    .map(|c| self.writer.number(c, super::templates::Num::Nat))
                    .collect();
                match sides.as_slice() {
                    [Route::Built(l), Route::Built(r)] => Some(format!(
                        "have e_nat : {} = {} := by exact_mod_cast {name}",
                        l.at(51),
                        r.at(51)
                    )),
                    _ => None,
                }
            }
            _ => None,
        };
        let mut ways: Vec<Tactic> = Vec::new();
        let tactics: &[BridgeTactic] = if into.len() > 1 {
            &[BridgeTactic::PutAt, BridgeTactic::SubstAt]
        } else {
            &[BridgeTactic::SubstAt]
        };
        for tactic in tactics {
            for line in &into {
                ways.push(put_into(*tactic, &equation, line));
                if let Some(own) = &own {
                    ways.push(put_into(*tactic, own, line));
                }
                if let Some(in_nat) = &in_nat {
                    ways.push(super::tactics::steps(vec![
                        Tactic::Raw(in_nat.clone()),
                        put_into(*tactic, "e_nat", line),
                    ]));
                }
            }
        }
        if into.is_empty() {
            ways.push(subst_by(&equation));
            if let Some(own) = &own {
                ways.push(subst_by(own));
            }
        }
        ways.extend(witnessed.into_iter().map(Tactic::Raw));
        let tactic = by_ways(ways);
        Route::Built(with_haves(&haves, &tactic))
    }

    /// A cited "for all" of one letter, read where a closure method reads
    /// it: at the one letter of the claim of its type that it does not
    /// itself name, the letter of the block the step stands in. None where
    /// the line says no such "for all", or the claim has no one such letter.
    fn read_at_claim(
        &self,
        cited: &super::algebra::Cited,
        claim: &Node,
    ) -> Option<super::algebra::Cited> {
        self.read_at_letters(cited, &claim.names())
    }

    /// `read_at_claim`, at the one letter among `names` of the type the
    /// "for all" ranges over that it does not itself name.
    fn read_at_letters(
        &self,
        cited: &super::algebra::Cited,
        names: &std::collections::BTreeSet<String>,
    ) -> Option<super::algebra::Cited> {
        let [letter, set, body] = cited.node.children.as_slice() else {
            return None;
        };
        if cited.node.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return None;
        }
        // A guarded "for all", over ℕ or ℕ₀, asks a proof besides the
        // letter, that it is above 0 or at least 0, which the lines in scope
        // give; one over any other set, ℝ ∖ {5} or B, that the letter is in
        // it.
        let (ty, guard) = match super::expr::system_of(set) {
            Some(system) => (
                LetterType::Number(super::expr::letter_type(system)),
                match system {
                    super::expr::System::Type(_) => "",
                    _ => " (by parley_side)",
                },
            ),
            None => (
                self.writer.set_members(set)?.letter(),
                " (by parley_set_side)",
            ),
        };
        // The names the line writes free: the letter it binds may be named
        // as the block's is.
        let own = crate::matching::free_names(
            &cited.node,
            &self.sources.checked.grammar.binders(),
        );
        let mut candidates: Vec<&String> = names
            .iter()
            .filter(|n| !own.contains(*n))
            .filter(|n| self.writer.letters.get(n.as_str()) == Some(&ty))
            .collect();
        // Of several, the one named as the line's own letter, s of "for all
        // s ∈ S" read in the block that lets s.
        if candidates.len() > 1 {
            candidates.retain(|n| **n == *letter.text);
        }
        let [at] = candidates.as_slice() else {
            return None;
        };
        let put = crate::matching::Binding::from([(
            letter.text,
            Node::name(letter.sort.clone(), at),
        )]);
        let read = crate::matching::substitute_apart_by(
            body,
            &put,
            &self.sources.checked.grammar.binders(),
        );
        Some(super::algebra::Cited {
            node: read,
            proof: format!("({} {}{guard})", cited.proof, super::names::letter(at)),
        })
    }

    /// `membership`. A term of a wider type said to be in a number system,
    /// an integer or a real, is one by a cited equation (`member_by_equation`).
    /// Any other membership is what the lines and the letters' types give.
    fn membership(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        for cited in self.cited_parts(&just.refs) {
            if let Some(proof) = member_by_equation(
                writer,
                &cited.node,
                &cited.proof,
                node,
                self.sources.ctx,
            ) {
                return Route::Built(proof);
            }
        }
        Route::Built(side_proof())
    }

    /// `substitute` in rows: each row the row above with the change its
    /// reason proves put in, the first row the line it cites, and the last
    /// the claim.
    fn substitute_rows(&self, just: &Justification, writer: &Writer) -> Route<String> {
        let Some(Ok(rows)) =
            crate::corpus::proof::substitute_rows(just, &self.thm.path)
        else {
            return Route::no("substitute rows that do not cut");
        };
        let Some(first) = rows.first() else {
            return Route::no("substitute rows with no row");
        };
        let Some(mut above) = self
            .named
            .get(first.cite.trim())
            .and_then(|n| n.first())
            .cloned()
        else {
            return Route::no(format!(
                "a first row citing {}, which has no Lean name",
                first.cite
            ));
        };
        let mut above_node: Option<Node> = self
            .trees
            .get(first.cite.trim())
            .and_then(|t| t.first())
            .map(|(n, _)| n.clone());
        let mut haves = Vec::new();
        for (k, row) in rows.iter().enumerate().skip(1) {
            let row_node = match self.tree(&row.formula) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_text = match writer.formula(&row_node) {
                Route::Built(p) => p.text(),
                Route::Declined(d) => return Route::Declined(d),
            };
            let Some(reason) = &row.reason else {
                return Route::no("a row after the first with no reason");
            };
            let Ok(by) = &reason.by else {
                return Route::no("a row whose reason does not read");
            };
            let change = match self.tree(&reason.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_text = match writer.formula(&change) {
                Route::Built(p) => p.text(),
                Route::Declined(d) => return Route::Declined(d),
            };
            let proof = match self.proof_of(
                Reason {
                    just: by,
                    cited: self.rec.cited_requires.get(&reason.line),
                },
                0,
                &change,
            ) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_name = format!("c{k}");
            haves.push(format!("have {change_name} : {change_text} := {proof}"));
            let used = match self.widened(&change, &change_name, &row_node, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    w.name
                }
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_name = format!("row{k}");
            // At the type the term has where it stands, as `substitute`
            // puts its equation in; each equation put by rewriting before
            // either by `simp`, which loops where one side stands in the
            // other, k in k + 1 − 1, and `first` goes on past no loop.
            let put = if used == change_name {
                put_into(BridgeTactic::SubstAt, &used, &above)
            } else {
                Tactic::First(vec![
                    put_into(BridgeTactic::PutAt, &used, &above),
                    put_into(BridgeTactic::PutAt, &change_name, &above),
                    put_into(BridgeTactic::SubstAt, &used, &above),
                    put_into(BridgeTactic::SubstAt, &change_name, &above),
                ])
            }
            .text();
            // A row whose lines say counts both ways takes them to
            // integers first, as a step does (`count_conversion`).
            let lines: Vec<&Node> = std::iter::once(&change)
                .chain(above_node.as_ref())
                .chain(std::iter::once(&row_node))
                .collect();
            let forms = self.count_forms(&lines);
            let put = match forms.mixed {
                true => format!("parley_count_int; {put}"),
                false => put,
            };
            haves.push(format!("have {row_name} : {row_text} := by {put}"));
            above = row_name;
            above_node = Some(row_node);
        }
        Route::Built(with_haves(&haves, &format!("by exact {above}")))
    }

    /// An equation a line says, as a term to rewrite the claim with: the
    /// line itself, or, where the line is computed in a narrower type than
    /// the claim, the line cast up to the claim's type, since Lean rewrites
    /// a term only with an equation of its own type.
    fn widened(
        &self,
        line: &Node,
        name: &str,
        claim: &Node,
        writer: &Writer,
    ) -> Route<Widened> {
        let same = || {
            Route::Built(Widened {
                have: None,
                name: name.to_string(),
            })
        };
        let numbers = |n: &Node| -> Vec<Node> {
            n.children
                .iter()
                .filter(|c| writer.is_number(c))
                .cloned()
                .collect()
        };
        let sides = numbers(line);
        if line.notation() != crate::notations::EQUALITY || sides.len() != 2 {
            return same();
        }
        // The line's type as it was written: the least that holds its sides.
        let mut own = super::templates::Num::Int;
        for s in &sides {
            match writer.carrier(s) {
                Route::Built(n) => own = own.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The claim's type, or the calculation's where the claim is a row.
        let mut wanted = self.worked_in.get().map_or(own, |w| w.max(own));
        for s in numbers(claim) {
            match writer.carrier(&s) {
                Route::Built(n) => wanted = wanted.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        if wanted == own {
            return same();
        }
        let mut printed = Vec::new();
        for s in &sides {
            match writer.number(s, wanted) {
                Route::Built(p) => printed.push(p.at(51)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // Numerals alone are told their type.
        if !sides.iter().any(|s| writer.pinned(s)) {
            printed[0] = format!("({} : {})", printed[0], writer.type_name(wanted));
        }
        // The equation mapped into the wider type, its casts pushed in, and
        // compared with what is wanted up to the ring's laws.
        let wide = format!("{}_w", name.replace('.', "_"));
        Route::Built(Widened {
            have: Some(format!(
                "have {wide} : {} = {} := by have h := congrArg (fun x : {} => (x : {})) {name}; push_cast at h; linear_combination (norm := parley_norm) h",
                printed[0],
                printed[1],
                writer.type_name(own),
                writer.type_name(wanted)
            )),
            name: wide,
        })
    }

    /// `calculation`: the chain as Lean's `calc`, every term in one type,
    /// each link proved by its reason.
    fn calculation(&self, just: &Justification, writer: &Writer) -> Route<String> {
        let Some(Ok(chain)) = crate::corpus::proof::chain(just, &self.thm.path) else {
            return Route::no("a calculation whose lines do not cut");
        };
        let mut terms = vec![match self.tree(&chain.start) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        }];
        for line in &chain.lines {
            match self.tree(&line.term) {
                Route::Built(n) => terms.push(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A chain that counts ∅ beside a set, |S| = |∅|: ∅ is a set of what
        // S holds (`expr::counted_beside_empty`).
        let hinted;
        let writer = match terms
            .iter()
            .find_map(|a| terms.iter().find_map(|b| writer.counted_beside_empty(a, b)))
        {
            Some(m) if writer.empty_of.is_none() => {
                let mut w = writer.with_letters(writer.letters.clone());
                w.empty_of = Some(m);
                hinted = w;
                &hinted
            }
            _ => writer,
        };
        // A chain of sets or of their members, A ∩ B = B ∩ A = ∅ or
        // F(F⁻¹(C)) = F(x), is written as sets are, and has no number type
        // to work in.
        let of_sets = terms
            .iter()
            .any(|t| writer.members_of(t).is_some() || writer.member_kind(t).is_some());
        // A chain of counts, |A| = |∅| = 0, is in ℕ∞ (`sets::count_term`).
        let of_counts = terms.iter().any(|t| writer.counts(t));
        // From ℤ, as the claim it proves is written.
        let mut at = super::templates::Num::Int;
        let mut printed = Vec::new();
        if of_counts {
            for t in &terms {
                match writer.count_term(t) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else if of_sets {
            for t in &terms {
                match writer.set_term(t) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        } else {
            for t in &terms {
                match writer.carrier(t) {
                    Route::Built(n) => at = at.max(n),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            for t in &terms {
                match writer.number(t, at) {
                    Route::Built(p) => printed.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // A first term whose type nothing in it fixes, numerals alone or
            // a power whose letters are only in its exponent, is told its
            // type, bracketed inside as it stands in the chain.
            if !writer.pinned(&terms[0]) {
                let first = printed[0].clone();
                let first = match first.prec() < 51 {
                    true => super::tactics::bracket(first),
                    false => first,
                };
                printed[0] = Printed::cast(first, writer.num_type(at));
            }
        }
        // The claim, the first term and the last, is stated in its own
        // least type; a chain worked out in a wider one moves the goal there
        // first, as `qify` or `rify` does.
        let of_numbers = !of_sets && !of_counts;
        let mut own = super::templates::Num::Int;
        for t in [terms.first(), terms.last()].into_iter().flatten() {
            if !of_numbers {
                break;
            }
            if let Route::Built(n) = writer.carrier(t) {
                own = own.max(n);
            }
        }
        // The chain is worked in `at`, its first term told the type where
        // nothing in it fixes one; a claim in a narrower type, 3^q = 2^p in
        // ℤ beside ln and exp in ℝ, is moved up to it first.
        // A claim of numerals alone may be written in the chain's type
        // already, from the line it is reached from (`claimed`), and then
        // has nowhere to move.
        let mut block: Vec<Tactic> = match (of_numbers && own < at, at) {
            (true, super::templates::Num::Rat) => {
                vec![Tactic::Try(Box::new(super::tactics::call("qify", vec![])))]
            }
            (true, super::templates::Num::Real) => {
                vec![Tactic::Try(Box::new(super::tactics::call("rify", vec![])))]
            }
            _ => Vec::new(),
        };
        let mut links: Vec<super::doc::tactic::CalcLink> = Vec::new();
        let single = chain.lines.len() == 1;
        for (k, line) in chain.lines.iter().enumerate() {
            let (relation, modulus) = match line.relation.as_str() {
                r @ ("=" | "<" | ">" | "≤" | "≥") => (r.to_string(), None),
                "≡" => {
                    let Some(modulus) = &line.modulus else {
                        return Route::no("a congruence with no modulus");
                    };
                    let modulus = match self.tree(modulus) {
                        Route::Built(m) => m,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    match writer.number_fixed(&modulus, super::templates::Num::Int) {
                        Route::Built(m) => ("≡".to_string(), Some(m)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                other => return Route::no(format!("a calculation joined by {other}")),
            };
            let proof = match &line.reason {
                Some(r) => {
                    let Ok(by) = &r.by else {
                        return Route::no(
                            "a calculation line whose reason does not read",
                        );
                    };
                    let fact = match self.tree(&r.fact) {
                        Route::Built(n) => n,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let reason = Reason {
                        just: by,
                        cited: self.rec.cited_requires.get(&r.line),
                    };
                    self.worked_in.set(Some(at));
                    let proof = self.proof_of(reason, 0, &fact);
                    self.worked_in.set(None);
                    match proof {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A row citing a define, S(1) = Σ(j = 1 to 1) j(j + 1) by
                // D1, unfolds it and pushes in the casts that leaves; a
                // header's function, its equation guarded by its domain, at
                // an argument linear arithmetic shows is in it.
                None if let Some(cite) = line.cited() => {
                    let define = self
                        .thm
                        .defines
                        .iter()
                        .any(|d| d.label == cite)
                        .then(|| self.named.get(cite).and_then(|n| n.first()))
                        .flatten();
                    // A row of a step that names whole numbers, citing a line
                    // in the page's forms: both taken to ℚ, each named number
                    // put as its term, and the line used.
                    let named = self.named.get(cite).and_then(|n| n.first());
                    let in_named = match (named, self.named_specs.is_empty()) {
                        (Some(line), false) => Some(Tactic::Raw(format!(
                            "(qify; push_cast; simp only [{s}]; first | (linear_combination (norm := parley_norm) {line}; done) | (linear_combination (norm := parley_norm) -{line}; done))",
                            s = self.named_specs.join(", ")
                        ))),
                        _ => None,
                    };
                    // A row of integer powers citing a line of natural powers
                    // to an integer's `toNat`, an item's 2^(d·e).toNat: the
                    // row's powers taken to natural ones (`parley_line_toNat`).
                    let line_to_nat = self
                        .trees
                        .get(cite)
                        .and_then(|t| t.first())
                        .and_then(|(node, _)| self.writer.formula(node).built())
                        .is_some_and(|p| p.has_to_nat());
                    let to_nat = [&printed[k], &printed[k + 1]]
                        .iter()
                        .any(|p| p.has_to_nat())
                        || line_to_nat;
                    // Each part of the line, 4.8 obtained as s4_8a, s4_8b, …
                    let parts: Vec<Tactic> = match to_nat {
                        true => self
                            .named
                            .get(cite)
                            .into_iter()
                            .flatten()
                            .map(|part| {
                                super::tactics::bridge(
                                    BridgeTactic::LineToNat,
                                    vec![TacticArg::Term(super::tactics::hyp(part))],
                                )
                            })
                            .collect(),
                        false => Vec::new(),
                    };
                    let mut ways: Vec<Tactic> = match define {
                        Some(h) => unfolded(std::slice::from_ref(h)),
                        None => Vec::new(),
                    };
                    ways.push(super::tactics::bridge(BridgeTactic::Side, vec![]));
                    ways.extend(in_named);
                    ways.extend(parts);
                    by_ways(ways)
                }
                // A row the page works out by real arithmetic, = 3·ln(2).
                None if line.cite == crate::corpus::Method::RealArithmetic.as_str() => {
                    super::doc::Proof::By(super::tactics::bridge(
                        BridgeTactic::Real,
                        vec![],
                    ))
                    .text()
                }
                None => super::doc::Proof::By(super::tactics::call("norm_num", vec![]))
                    .text(),
            };
            // A chain of one link is that link, and its proof the step's:
            // Lean's calc would read the line after a lone link as another.
            if single {
                return Route::Built(proof);
            }
            links.push(super::doc::tactic::CalcLink {
                relation,
                term: printed[k + 1].clone(),
                modulus,
                proof,
            });
        }
        block.push(Tactic::Calc {
            first: printed[0].clone(),
            links,
        });
        Route::Built(super::doc::Proof::Block(block).text())
    }

    /// Each sentence of the lines `refs` names, each conjunction taken apart
    /// into its parts, with the Lean term that proves each part.
    fn cited_parts(&self, refs: &[String]) -> Vec<super::algebra::Cited> {
        let mut out = Vec::new();
        for r in refs {
            for (node, name) in self.trees.get(r).into_iter().flatten() {
                conjuncts(node, name.clone(), &mut out);
            }
        }
        out
    }

    /// Where the item's set letter `name` is the domain of one of its maps,
    /// the domain of the map the citation gives for it, as Lean writes it;
    /// None where the letter is no map's domain.
    fn given_domain(
        &self,
        sentence: &Sentence,
        name: &str,
        binding: &crate::matching::Binding,
    ) -> Option<Route<super::expr::Printed>> {
        let (map, _) = sentence.domains.iter().find(|(_, d)| {
            matches!(&d.kind, super::doc::TermKind::Letter(l) if *l == super::names::letter(name))
        })?;
        let given = binding.get(&crate::formula::symbol::Symbol::of(map));
        Some(match given {
            // The domain stands bracketed as an argument does.
            Some(g) if g.is_name() => match self.writer.domain_of(&g.text) {
                Some(d) if d.prec() < super::expr::MAX => {
                    let ty = d.ty.clone();
                    Route::Built(super::expr::Printed {
                        kind: super::doc::TermKind::Paren(Box::new(d)),
                        ty,
                    })
                }
                Some(d) => Route::Built(d),
                None => Route::no(format!("{}, whose domain no line gives", g.text)),
            },
            _ => Route::no(format!(
                "a map's domain where its map {map} is given no letter"
            )),
        })
    }

    /// Of what a reading gives, an "and" of several parts, the part that
    /// says the claim, as Lean writes both at the citation's values, by its
    /// place among the parts (`and_parts`). None where no one part does.
    fn part_saying(
        &self,
        read: &Node,
        cited: &crate::checker::record::Cited,
        claim: &Node,
    ) -> Option<usize> {
        let parts = and_parts(read);
        if parts.len() < 2 {
            return None;
        }
        let wanted = self.writer.formula(claim).built()?.text();
        let binders = self.sources.checked.grammar.binders();
        let saying: Vec<usize> = parts
            .iter()
            .enumerate()
            .filter(|(_, part)| {
                let at = crate::matching::substitute_apart_by(
                    part,
                    &cited.binding,
                    &binders,
                );
                self.writer
                    .formula(&at)
                    .built()
                    .is_some_and(|p| p.text() == wanted)
            })
            .map(|(i, _)| i)
            .collect();
        match saying.as_slice() {
            [one] => Some(*one),
            _ => None,
        }
    }

    /// The name of the cited line that says an item's hypothesis at the
    /// citation's values, where its Lean text and the hypothesis's are one;
    /// None where no line does, or the hypothesis does not write. `asked` is
    /// the hypothesis as the item states it.
    /// Whether a citation gives one of the letters an item's hypothesis
    /// uses, as Lean states it, all of a number system or a range, D := ℝ:
    /// the item asks `∀ x ∈ Set.univ, …` or `i ∈ Set.Icc a b` where the
    /// citing proof's line says `∀ x : ℝ, …` or `i ∈ Finset.Icc a b`, which
    /// `parley_whole_side` takes the one to the other. The Lean statement
    /// shows the letters a function's domain adds to the page's, D of
    /// `D ∈ nhds x`.
    fn given_whole(&self, asked: &str, binding: &crate::matching::Binding) -> bool {
        let used: Vec<&str> = asked
            .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '\''))
            .collect();
        binding.iter().any(|(letter, v)| {
            matches!(
                v.notation(),
                crate::notations::NUMBER_SYSTEMS | crate::notations::INTEGER_RANGE
            ) && used.contains(&super::names::letter(letter.as_ref()).as_str())
        })
    }

    fn line_saying(
        &self,
        hypothesis: &Node,
        asked: &str,
        binding: &crate::matching::Binding,
        cited_lines: &[super::algebra::Cited],
        binders: &[Binder],
    ) -> Option<String> {
        // The item asks its hypothesis in its own letters' types: a number
        // given a letter of another type, or of the general one, is cast,
        // and the line, written in its own types, says something else in
        // Lean. Each number letter of the hypothesis must take its value
        // with no cast.
        let uncast = hypothesis.names().iter().all(|page| {
            let Some(Binder::Letter { ty, general, .. }) = binders
                .iter()
                .find(|b| matches!(b, Binder::Letter { page: p, .. } if p == page))
            else {
                return true;
            };
            let LetterType::Number(n) = ty else {
                return true;
            };
            let value = binding.get(&crate::formula::symbol::Symbol::of(page));
            !general
                && value.is_some_and(|v| {
                    self.writer.carrier(v).built()
                        == Some((*n).max(super::templates::Num::Int))
                        && *n != super::templates::Num::Nat
                })
        });
        if !uncast {
            return None;
        }
        let at = crate::matching::substitute_apart_by(
            hypothesis,
            binding,
            &self.sources.checked.grammar.binders(),
        );
        let wanted = self.writer.formula(&at).built()?.text();
        // An item that counts a set in ℕ∞, |X| = 0 of card-zero, given a
        // set this proof counts as a natural number: the line says
        // `A.ncard`, the item asks `X.encard`, and the set tactics take
        // the one to the other.
        if asked.contains(".encard") && wanted.contains(".ncard") {
            return None;
        }
        // The other way: a line counting in ℕ∞, |A| ≠ 0 as `¬A.encard = 0`,
        // given where the item asks an integer, m ≠ 0 at m := |A|.
        if wanted.contains(".encard") && !asked.contains(".encard") {
            return None;
        }
        cited_lines
            .iter()
            .find(|c| {
                self.writer
                    .formula(&c.node)
                    .built()
                    .is_some_and(|p| p.text() == wanted)
            })
            .map(|c| c.proof.clone())
    }

    /// The type each of an item's type variables is taken at where a
    /// citation gives its things numbers, x ∈ {u, w} cited of 1 and 2: the
    /// least that holds every number given them. From ℕ: a set of naturals
    /// given for a set of things, S ⊆ ℕ, is of naturals, and a number given
    /// raises it to ℤ at least.
    fn things_given(
        &self,
        binders: &[Binder],
        binding: &crate::matching::Binding,
    ) -> ThingsGiven {
        use super::expr::Members;
        let mut given = ThingsGiven::default();
        for b in binders {
            let Binder::Letter { page, ty, .. } = b else {
                continue;
            };
            let Some(value) = binding.get(&crate::formula::symbol::Symbol::of(page))
            else {
                continue;
            };
            match ty {
                // A term of natural letters, b·d, is a natural; any other
                // number is an integer at least.
                LetterType::Member(Members::Things(var))
                    if self.writer.is_number(value) =>
                {
                    let of_letters = value.walk().iter().any(|m| m.is_name());
                    if of_letters && self.writer.natural(value) {
                        continue;
                    }
                    if let Route::Built(c) = self.writer.carrier(value) {
                        given.raise(*var, c);
                    }
                }
                // A set of things given a set of numbers, X := ℝ, sets the
                // things' type at least to that set's.
                LetterType::Set(Members::Things(var)) => {
                    match self.writer.set_members(value) {
                        Some(Members::Numbers(n)) => {
                            given.raise(*var, n);
                            given.numbers.insert(*var);
                        }
                        Some(m @ Members::Sets(_)) => {
                            given.others.insert(*var, m);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        // A map given by its values, n ↦ 9ⁿ, gives what its body is with
        // n of the type its domain's things are taken at, ℚ of n in ℤ.
        for b in binders {
            let Binder::Letter {
                page,
                ty:
                    LetterType::Map {
                        from: Members::Things(from),
                        to: Members::Things(to),
                    },
                ..
            } = b
            else {
                continue;
            };
            let value = binding.get(&crate::formula::symbol::Symbol::of(page));
            let Some(value) = value.filter(|v| &*v.notation_name() == "property-of")
            else {
                continue;
            };
            let [body] = value.children.as_slice() else {
                continue;
            };
            let takes = given
                .at
                .get(from)
                .copied()
                .unwrap_or(super::templates::Num::Nat);
            let mut letters = self.writer.letters.clone();
            letters.insert(value.text.to_string(), LetterType::Number(takes));
            if let Route::Built(c) = self.writer.with_letters(letters).carrier(body) {
                given.raise(*to, c);
            }
        }
        given
    }

    /// The Lean term an item's sentence is at a citation: the theorem with
    /// each letter given its value, and each hypothesis given by the line
    /// cited that says it as Lean writes both, or else left to
    /// `parley_side`.
    fn instance(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
        claim: Option<&Node>,
        cited_lines: &[super::algebra::Cited],
    ) -> Route<String> {
        self.instance_of(sentence, binding, claim, cited_lines)
            .map(|i| i.term.text())
    }

    /// The item applied to what the citation gives it (`instance`), and
    /// what it then says.
    fn instance_of(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
        claim: Option<&Node>,
        cited_lines: &[super::algebra::Cited],
    ) -> Route<Instance> {
        let mut given: std::collections::BTreeMap<String, super::expr::Printed> =
            std::collections::BTreeMap::new();
        let things = self.things_given(&sentence.binders, binding);
        // The type an item's general letters take: the least that holds the
        // claim and every value given them, a field's at least where the
        // item divides.
        let general = match sentence.general {
            Some(g) => {
                let least = if g.field {
                    super::templates::Num::Rat
                } else {
                    super::templates::Num::Int
                };
                let mut at = self.worked_in.get().map_or(least, |w| w.max(least));
                let numbers: Vec<&Node> = claim
                    .into_iter()
                    .flat_map(|c| c.children.iter())
                    .filter(|c| self.writer.is_number(c))
                    .collect();
                for n in numbers {
                    match self.writer.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A term the claim puts in a hole of a fixed type, ⌊A/B⌋ in
                // ℝ's, is of that type.
                if let Some(c) = claim {
                    at = at.max(self.held_in(c));
                }
                for b in &sentence.binders {
                    let Binder::Letter {
                        page,
                        ty,
                        general: true,
                        ..
                    } = b
                    else {
                        continue;
                    };
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        continue;
                    };
                    match self.given_type(value, ty, &things) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Some(at)
            }
            None => None,
        };
        let things_at = |var: &usize| {
            let least = self.worked_in.get().unwrap_or(super::templates::Num::Nat);
            things.at.get(var).map_or(least, |n| least.max(*n))
        };
        let mut args = Vec::new();
        for b in &sentence.binders {
            match b {
                Binder::Letter {
                    name,
                    page,
                    ty,
                    general: in_general,
                } => {
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        // A set the citation gives no value: a map's domain,
                        // the X of `f : X → W`, is the domain of what f is
                        // given, within which its images are taken; the Z a
                        // map goes into is all of its type, which every map
                        // goes into; anything else is left to Lean.
                        let fill =
                            match (ty, self.given_domain(sentence, name, binding)) {
                                (LetterType::Set(_), Some(Route::Built(d))) => d,
                                (LetterType::Set(_), Some(Route::Declined(d))) => {
                                    return Route::Declined(d)
                                }
                                (LetterType::Set(_), None) => {
                                    super::expr::Printed::head(
                                        "Set.univ",
                                        super::doc::Source::Mathlib,
                                    )
                                }
                                // A function of a recursion the file lets, F of
                                // D1, is the citing theorem's F, which the same
                                // define lets.
                                (LetterType::Function { .. }, _)
                                    if self.writer.letters.get(page.as_str())
                                        == Some(ty) =>
                                {
                                    super::expr::Printed::letter(
                                        super::names::letter(page),
                                        ty.lean_type(),
                                    )
                                }
                                _ => super::expr::Printed::of(
                                    super::doc::TermKind::Elided,
                                    ty.lean_type(),
                                ),
                            };
                        given.insert(name.clone(), fill.clone());
                        args.push(super::doc::Arg::Named {
                            name: name.clone(),
                            value: fill,
                        });
                        continue;
                    };
                    // The value of a define that names its number, m/p of
                    // `let r = m/p, a positive integer`, is that number, r.
                    let value = self
                        .witness_letters
                        .iter()
                        .find(|w| {
                            crate::matching::alike_top(
                                &w.value,
                                value,
                                self.sources.ctx,
                            )
                        })
                        .map_or(value, |w| &w.letter);
                    let printed = match (ty, general.filter(|_| *in_general)) {
                        (LetterType::Number(_), Some(at)) => {
                            self.writer.number_fixed(value, at)
                        }
                        // A value of a wider type that a line says is in the
                        // letter's, A + B ∈ ℚ of reals: the number that line
                        // gives.
                        (LetterType::Number(n), None) => {
                            match self.writer.number_fixed(value, *n) {
                                Route::Declined(d) => {
                                    match self.said_integer(value, *n) {
                                        Some(line) => {
                                            let printed = super::expr::Printed::atom(
                                                format!("(Classical.choose {line})"),
                                            );
                                            self.said_used.borrow_mut().push(
                                                SaidUsed {
                                                    line,
                                                    term: self
                                                        .writer
                                                        .grammar
                                                        .print(value),
                                                },
                                            );
                                            Route::Built(printed)
                                        }
                                        None => Route::Declined(d),
                                    }
                                }
                                built => built,
                            }
                        }
                        // A property given by what it says of t, `fun t : α
                        // => …`, t a member of what the property is of.
                        (LetterType::Property(members), _) => {
                            // Of things the citation gives numbers, the
                            // numbers at the type the things are taken at.
                            // Of things given sets, a set of them; of sets of
                            // things, sets of what is given for those.
                            let put = things.put(members, &things_at);
                            let (of, lean) = (put.letter(), put.lean());
                            match (&*value.notation_name(), value.children.as_slice()) {
                                ("property-of", [body]) => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(value.text.to_string(), of);
                                    let inner = self.writer.with_letters(letters);
                                    inner.formula(body).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            lean,
                                            b.text()
                                        ))
                                    })
                                }
                                _ if value.is_name() => {
                                    Route::Built(super::expr::Printed::atom(
                                        super::names::letter(&value.text),
                                    ))
                                }
                                _ => Route::no(
                                    "a property given by other than what it says",
                                ),
                            }
                        }
                        // A function given for a function letter, of the
                        // same types.
                        // A function given by its values, k ↦ t, a sum's
                        // term: `fun k : ℤ => t`, t in what it gives.
                        (LetterType::Function { from, to }, given)
                            if &*value.notation_name() == "property-of" =>
                        {
                            // A function into the general type gives the
                            // type chosen for it.
                            let gives = given.unwrap_or(*to);
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(*from),
                                    );
                                    let mut inner = self.writer.with_letters(letters);
                                    inner.wholes.shift_remove(&*value.text);
                                    // k ↦ 2^k given for a sum's term stands for
                                    // the sum's index the claim runs it over,
                                    // in ℕ₀ from 0, so 2^k is written as the
                                    // claim's sum writes it.
                                    let index = claim.and_then(|c| {
                                        super::expr::index_letter_system(c, &value.text)
                                    });
                                    if let (super::templates::Num::Int, Some(system)) =
                                        (*from, index)
                                    {
                                        inner.introduce(&value.text, system);
                                    }
                                    inner.number_fixed(body, gives).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            from.lean(),
                                            b.text()
                                        ))
                                    })
                                }
                                _ => Route::no(
                                    "a function by its values of other than one body",
                                ),
                            }
                        }
                        (LetterType::Function { from, to }, given) => {
                            match self.writer.function_type(value) {
                                Route::Built(t)
                                    if t == (*from, given.unwrap_or(*to)) =>
                                {
                                    Route::Built(self.writer.function_printed(value))
                                }
                                // A function that takes the letter's numbers
                                // and gives numbers within its type, t of ℤ
                                // into ℤ for f of ℕ into ℝ: t between casts.
                                Route::Built((takes, gives))
                                    if *from <= takes
                                        && gives <= given.unwrap_or(*to) =>
                                {
                                    let wanted = given.unwrap_or(*to);
                                    Route::Built(super::expr::Printed::atom(format!(
                                        "(fun x : {} => (({} (x : {}) : {}) : {}))",
                                        from.lean(),
                                        self.writer.function_printed(value).text(),
                                        takes.lean(),
                                        gives.lean(),
                                        wanted.lean()
                                    )))
                                }
                                Route::Built(_) => Route::no(
                                    "a function given for a letter of other types",
                                ),
                                Route::Declined(d) => Route::Declined(d),
                            }
                        }
                        (LetterType::Statement, _) => self.writer.formula(value),
                        // A thing given a number: the number, at the type
                        // the things are taken at here.
                        (LetterType::Member(super::expr::Members::Things(var)), _)
                            if self.writer.is_number(value) =>
                        {
                            self.writer.number_fixed(value, things_at(var))
                        }
                        // A set of things given a set of numbers: the set at
                        // the type the things are taken at here.
                        (LetterType::Set(super::expr::Members::Things(var)), _)
                            if matches!(
                                self.writer.set_members(value),
                                Some(super::expr::Members::Numbers(_))
                            ) =>
                        {
                            self.writer.numbers_at(value, things_at(var))
                        }
                        // A map of things given by its values on numbers,
                        // n ↦ 9ⁿ: `fun n : ℤ => 9 ^ n`, taking and giving
                        // numbers at the types its two sides' things are
                        // taken at here.
                        (
                            LetterType::Map {
                                from: super::expr::Members::Things(from),
                                to: super::expr::Members::Things(to),
                            },
                            _,
                        ) if &*value.notation_name() == "property-of" => {
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters.insert(
                                        value.text.to_string(),
                                        LetterType::Number(things_at(from)),
                                    );
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, things_at(to)).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            things_at(from).lean(),
                                            b.text()
                                        ))
                                    })
                                }
                                _ => Route::no(
                                    "a map by its values of other than one body",
                                ),
                            }
                        }
                        // A map from things into numbers given by its
                        // values, x ↦ x·c for t : X → ℤ: `fun x : ℤ => x *
                        // c`, x a member of what the things are taken at
                        // here, its value a number of t's type.
                        (
                            LetterType::Map {
                                from: from @ super::expr::Members::Things(_),
                                to: super::expr::Members::Numbers(to),
                            },
                            given,
                        ) if &*value.notation_name() == "property-of" => {
                            let put = things.put(from, &things_at);
                            let gives = given.unwrap_or(*to);
                            match value.children.as_slice() {
                                [body] => {
                                    let mut letters = self.writer.letters.clone();
                                    letters
                                        .insert(value.text.to_string(), put.letter());
                                    let inner = self.writer.with_letters(letters);
                                    inner.number_fixed(body, gives).map(|b| {
                                        super::expr::Printed::atom(format!(
                                            "(fun {} : {} => {})",
                                            super::names::letter(&value.text),
                                            put.lean(),
                                            b.text()
                                        ))
                                    })
                                }
                                _ => Route::no(
                                    "a map by its values of other than one body",
                                ),
                            }
                        }
                        // A function of numbers given for a map of things
                        // into numbers, f for u : X → K: f itself where it
                        // gives the numbers asked, else f's value cast up.
                        (
                            LetterType::Map {
                                from: from @ super::expr::Members::Things(_),
                                to: super::expr::Members::Numbers(to),
                            },
                            given,
                        ) if self.writer.function_type(value).built().is_some() => {
                            let wanted = given.unwrap_or(*to);
                            let put = things.put(from, &things_at);
                            match self.writer.function_type(value) {
                                Route::Built((_, gives)) if gives == wanted => {
                                    Route::Built(self.writer.function_printed(value))
                                }
                                Route::Built((takes, gives)) if gives < wanted => {
                                    Route::Built(super::expr::Printed::atom(format!(
                                        "(fun x : {} => (({} (x : {}) : {}) : {}))",
                                        put.lean(),
                                        self.writer.function_printed(value).text(),
                                        takes.lean(),
                                        gives.lean(),
                                        wanted.lean()
                                    )))
                                }
                                Route::Built(_) => Route::no(
                                    "a function given for a map into a narrower type",
                                ),
                                Route::Declined(d) => Route::Declined(d),
                            }
                        }
                        // A listed set whose members give no type, {∅},
                        // given for a set of things that another letter
                        // gives sets: a set of those.
                        (LetterType::Set(super::expr::Members::Things(var)), _)
                            if things.others.contains_key(var)
                                && self.writer.members_of(value).is_none() =>
                        {
                            self.writer.listed_as(value, &things.others[var])
                        }
                        // ∅ given for a member, the x := ∅ of |{x}| = 1 for
                        // |{∅}|: with the type the writer gives ∅ inside
                        // {∅} (`Writer::sets_of_nothing`), which ∅ alone
                        // does not give Lean.
                        (LetterType::Member(super::expr::Members::Things(_)), _)
                            if &*value.notation_name() == "empty-set" =>
                        {
                            match self
                                .writer
                                .sets_of_nothing(std::slice::from_ref(value))
                            {
                                Some(set) => Route::Built(super::expr::Printed::atom(
                                    format!("(∅ : {})", set.lean()),
                                )),
                                None => self.writer.set_term(value),
                            }
                        }
                        // A set, a member or a map given for one: the term
                        // as the writer writes a set's.
                        (
                            LetterType::Set(_)
                            | LetterType::Member(_)
                            | LetterType::Map { .. },
                            _,
                        ) => self.writer.set_term(value),
                        // A group given for a group, or a subgroup for a
                        // subgroup: its Lean name, the type or the
                        // `Subgroup G` itself, not the set it stands for.
                        (LetterType::Group | LetterType::Subgroup(_), _) => {
                            Route::Built(super::expr::Printed::atom(
                                super::names::letter(&value.text),
                            ))
                        }
                        // The identity is no binder: `1` of the group.
                        (LetterType::Identity(_), _) => {
                            Route::no("an identity given as a letter of an item")
                        }
                    };
                    match printed {
                        Route::Built(p) => {
                            given.insert(name.clone(), p.clone());
                            args.push(super::doc::Arg::Named {
                                name: name.clone(),
                                value: p,
                            });
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A hypothesis of a set the citation gives all of ℝ or a
                // range: what the lines say, read as the item asks it.
                Binder::Fact { says, .. }
                    if self.given_whole(&says.text(), binding) =>
                {
                    args.push(proof_arg("(by parley_whole_side)"))
                }
                // A hypothesis a cited line says, as Lean writes both: the
                // line by its name.
                Binder::Fact {
                    line: Some(line),
                    says,
                    ..
                } => match self.line_saying(
                    line,
                    &says.text(),
                    binding,
                    cited_lines,
                    &sentence.binders,
                ) {
                    Some(name) => args.push(proof_arg(&name)),
                    None => args.push(proof_arg("(by parley_side)")),
                },
                Binder::Fact { .. } => args.push(proof_arg("(by parley_side)")),
            }
        }
        let decl = super::expr::Printed::head(
            &sentence.decl,
            super::doc::Source::Item(module_of_decl(&sentence.decl)),
        );
        let head = if args.is_empty() {
            decl
        } else {
            super::expr::Printed {
                kind: super::doc::TermKind::Paren(Box::new(super::expr::Printed {
                    kind: super::doc::TermKind::App {
                        head: Box::new(decl),
                        args,
                        explicit: false,
                    },
                    ty: Some(super::doc::LeanType::Prop),
                })),
                ty: Some(super::doc::LeanType::Prop),
            }
        };
        let term = match sentence.part.is_empty() {
            true => head,
            false => super::expr::Printed::notation(
                vec![
                    super::doc::Piece::term(head, 0),
                    super::doc::Piece::text(sentence.part.clone()),
                ],
                super::expr::MAX,
                super::doc::LeanType::Prop,
            ),
        };
        let statement = sentence.prop.substituted(&given);
        let statement = match general {
            Some(at) => statement.with_general(super::doc::LeanType::Num(at)),
            None => statement,
        };
        Route::Built(Instance { term, statement })
    }

    /// The type a value given a general letter is in: a number's own, a
    /// function by its values k ↦ t the type of t with k of the type the
    /// function takes, and a function letter's what it gives.
    fn given_type(
        &self,
        value: &Node,
        ty: &LetterType,
        things: &ThingsGiven,
    ) -> Route<super::templates::Num> {
        match (ty, value.children.as_slice()) {
            (LetterType::Function { from, .. }, [body])
                if &*value.notation_name() == "property-of" =>
            {
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), LetterType::Number(*from));
                self.writer.with_letters(letters).carrier(body)
            }
            (LetterType::Function { .. }, _) => {
                self.writer.function_type(value).map(|(_, to)| to)
            }
            // A map of things into numbers given by its values, x ↦ x·c: the
            // type of x·c with x a number of the type the things are given;
            // given a function, what the function gives.
            (
                LetterType::Map {
                    from: super::expr::Members::Things(var),
                    ..
                },
                [body],
            ) if &*value.notation_name() == "property-of" => {
                let Some(takes) = things.at.get(var) else {
                    return Route::no("a map by its values on things given no numbers");
                };
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), LetterType::Number(*takes));
                self.writer.with_letters(letters).carrier(body)
            }
            (LetterType::Map { .. }, _) => {
                self.writer.function_type(value).map(|(_, to)| to)
            }
            // A set given for a `Set K` letter: the type of its numbers.
            (LetterType::Set(_), _) => match self.writer.set_members(value) {
                Some(super::expr::Members::Numbers(n)) => Route::Built(n),
                _ => Route::no(format!(
                    "{} is no set of numbers",
                    self.writer.grammar.print(value)
                )),
            },
            _ => self.writer.carrier(value),
        }
    }

    /// The item a reason cites, in Lean.
    fn cited_item<'r>(&self, reason: Reason<'r>) -> Route<(&Item, &'r Cited)>
    where
        'a: 'r,
    {
        let Some(cited) = reason.cited else {
            return Route::no("a citation the checker did not read");
        };
        match self.sources.items.get(&cited.item) {
            Some(item) => Route::Built((item, cited)),
            None => Route::no(format!("{} has no Lean form", cited.item)),
        }
    }

    /// Sentence `k` of a claim, by the item its reason cites.
    fn citation(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A phrase's define cited, `D1 n := 6, from 2`: the phrase is
        // written out as its meaning in the claim and in the lines alike, so
        // the claim is what the lines it cites say, in the claim's own
        // words, and the definition, whose two sides are one, adds nothing.
        let phrase = super::items::record_of(self.sources.checked, &cited.item)
            .is_some_and(|r| {
                r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
            });
        if phrase {
            return Route::Built(side_proof());
        }
        let Some(concluded) = cited.concluded.get(k) else {
            return Route::no("a claim sentence no conclusion of the item gives");
        };
        let Some(sentence) = item.sentences.get(concluded.sentence) else {
            return Route::no("a conclusion the item does not have in Lean");
        };
        let lines = self.cited_parts(&reason.just.refs);
        let instance =
            match self.instance_of(sentence, &cited.binding, Some(node), &lines) {
                Route::Built(i) => i,
                Route::Declined(d) => return Route::Declined(d),
            };
        // An item read as written says what the claim says: where the two
        // write one term in different forms, the build reports it.
        if concluded.way == Way::AsWritten {
            if let Route::Built(claim) = self.writer.formula(node) {
                for d in super::doc::forms::differences(&instance.statement, &claim) {
                    self.forms.borrow_mut().push(FormNote {
                        page_line: reason.just.line,
                        item: cited.item.clone(),
                        difference: d,
                    });
                }
            }
        }
        let inst = instance.term.text();
        let iff = sentence.says.notation() == BICONDITIONAL;
        let implication = matches!(sentence.says.notation(), CONDITIONAL | IMPLICATION);
        let term = match concluded.way {
            Way::AsWritten => inst,
            Way::Forward if iff => format!("({inst}).mp (by parley_side)"),
            Way::Forward if implication => format!("{inst} (by parley_side)"),
            Way::Forward => {
                return Route::no("a forward reading of a sentence that is no ↔ or if")
            }
            Way::Backward => {
                let witness = match self.witnesses(sentence, cited, &reason.just.refs) {
                    Route::Built(w) => w,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // What the definition's left side says, read in the claim's
                // own words where the two say one thing otherwise: an item
                // over any ring says "∈ ℕ₀" `∃ m : ℕ, ↑m = x`, a claim of
                // integers `0 ≤ x` (`parley_side`).
                // A claim a requires line above already states, "0 ≤ b − c"
                // for "b − c ∈ ℕ₀", is that line: tried first, as it is
                // quick and the others may search long.
                // A natural given as an integer's `toNat`, put back by `▸`,
                // which the goal guides in an `exact`; where the claim is in
                // a wider type than the item, the term stated by a `have`
                // and cast to it.
                use super::tactics as t;
                let by_to_nat = inst.contains("Int.toNat_of_nonneg");
                let mpr = Printed {
                    kind: super::doc::TermKind::App {
                        head: Box::new(Printed {
                            kind: super::doc::TermKind::Field {
                                inner: Box::new(t::bracket(Printed::atom(
                                    inst.clone(),
                                ))),
                                field: "mpr".to_string(),
                            },
                            ty: None,
                        }),
                        args: vec![super::doc::Arg::Explicit(Printed::atom(witness))],
                        explicit: false,
                    },
                    ty: None,
                };
                let mut ways = vec![
                    t::steps(vec![
                        t::call("assumption", vec![]),
                        t::call("done", vec![]),
                    ]),
                    Tactic::Exact(mpr.clone()),
                ];
                if by_to_nat {
                    ways.push(t::on_h(&mpr, vec![t::exact_mod_cast(t::hyp("h"))]));
                    ways.push(t::on_h(
                        &mpr,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            t::exact_mod_cast(t::hyp("h")),
                        ],
                    ));
                }
                ways.push(t::on_h(&mpr, vec![t::bridge(BridgeTactic::Side, vec![])]));
                return Route::Built(by_ways(ways));
            }
        };
        // Several sentences of the claim taken by one reading are its "and"
        // set apart, each the projection of its place among them.
        let same: Vec<usize> = cited
            .concluded
            .iter()
            .enumerate()
            .filter(|(_, c)| **c == *concluded)
            .map(|(i, _)| i)
            .collect();
        // A claim that is itself the "and", read as its parts, is the whole.
        let whole = matches!(
            node.notation(),
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
        );
        // What the reading gives: a definition's right side, a theorem's
        // sentence; its "and" is taken apart as its tree nests it.
        let read = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right,
            _ => &sentence.says,
        };
        let term = match same.iter().position(|&i| i == k) {
            Some(at) if same.len() > 1 && !whole => {
                match leaf_path(read, at) {
                    Some(path) => format!("({term}){path}"),
                    None => return Route::no(
                        "a reading whose \"and\" has fewer parts than its sentences",
                    ),
                }
            }
            // One sentence of the claim that is one part of the "and" the
            // reading gives, "for all d …" of "p > 1 and for all d …": that
            // part, found by its Lean text at the citation's values.
            _ if !whole && same.len() == 1 && concluded.way == Way::Forward && iff => {
                match self
                    .part_saying(read, cited, node)
                    .and_then(|at| leaf_path(read, at))
                {
                    Some(path) => format!("({term}){path}"),
                    None => term,
                }
            }
            _ => term,
        };
        // A define the step cites is written out first, as for algebra.
        let defines = self.cited_defines(&reason.just.refs);
        // An item that says a natural power of an integer is one gives the
        // claim nothing to read where the claim's exponent is an integer
        // the page shows not negative, 2^(n − 1); the writer gives the
        // witness.
        let closed = match self.writer.integer_power_witness(node) {
            Some(witness) => by_ways(vec![
                Tactic::Exact(Printed::atom(witness)),
                Tactic::Exact(super::tactics::bracket(Printed::atom(close(
                    &self.writer,
                    node,
                    &term,
                )))),
            ]),
            None => close(&self.writer, node, &term),
        };
        Route::Built(with_haves(&written_out(&defines), &closed))
    }

    /// The proof of the right side of a definition a step folds: its
    /// witnesses, where it is a "there is", and its body left to
    /// `parley_side`.
    fn witnesses(
        &self,
        sentence: &Sentence,
        cited: &crate::checker::record::Cited,
        refs: &[String],
    ) -> Route<String> {
        let [_, right] = sentence.says.children.as_slice() else {
            return Route::no("a definition of other than two sides");
        };
        // A witness that is a letter bound by the line cited, the k of its
        // "there is k", is no value in scope: the line says the right side
        // whole.
        let bound_here: std::collections::BTreeSet<String> = self
            .cited_parts(refs)
            .iter()
            .filter(|c| c.node.notation() == crate::notations::THERE_IS)
            .filter_map(|c| c.node.children.first())
            .filter(|l| l.is_name())
            .map(|l| l.text.to_string())
            .collect();
        let bound_by_line = cited
            .bound
            .values()
            .any(|v| v.is_name() && bound_here.contains(v.text.as_str()));
        if bound_by_line {
            return Route::Built("(by parley_side)".to_string());
        }
        let mut parts = Vec::new();
        // What a line said of a witness the page wrote as a fraction that
        // is an integer, put in scope where the witness's facts are proved.
        let mut known = Vec::new();
        let mut body = right;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = cited.bound.get(&letter.text) else {
                return Route::no(format!("no witness for {}", letter.text));
            };
            let system = super::expr::system_of(set);
            let Some(s) = system else {
                // A witness in a set: the value, a number at its own type
                // or a member as the writer writes one, and that it is in
                // the set.
                let term = match self.writer.carrier(value) {
                    Route::Built(at) if self.writer.is_number(value) => {
                        self.writer.number_fixed(value, at)
                    }
                    _ => self.writer.set_term(value),
                };
                match term {
                    Route::Built(p) => parts.push(p.text()),
                    Route::Declined(d) => return Route::Declined(d),
                }
                parts.push(format!("by {}parley_side", known.concat()));
                body = inner;
                continue;
            };
            let ty = super::expr::letter_type(s);
            match self.witness(value, ty) {
                Route::Built(w) => {
                    parts.push(w.term);
                    known.extend(w.known);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            if system == Some(super::expr::System::Positive) {
                parts.push(format!("by {}parley_side", known.concat()));
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::Built("(by parley_side)".to_string());
        }
        parts.push(format!("by {}parley_side", known.concat()));
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// A witness of a "there is" over `ty`: the value as Lean computes it
    /// there, or, for a value the page writes as a fraction that a line
    /// says is an integer, the integer that line gives, with what it says
    /// of it put in scope where the witness's facts are proved.
    fn witness(&self, value: &Node, ty: super::templates::Num) -> Route<Witness> {
        match self.writer.number_fixed(value, ty) {
            Route::Built(p) => Route::Built(Witness {
                term: p.text(),
                known: None,
            }),
            Route::Declined(d) => match self.said_integer(value, ty) {
                Some(line) => Route::Built(Witness {
                    term: format!("Classical.choose {line}"),
                    known: Some(format!("have := Classical.choose_spec {line}; ")),
                }),
                None => Route::Declined(d),
            },
        }
    }

    /// The Lean name of a line in scope saying a term is an integer, `(N −
    /// 1)/2 ∈ ℤ`, where `value` is that term as Lean writes it; None where
    /// no line says so. Lean states that line as `∃ m : ℤ, (m : ℚ) = …`, so
    /// the integer is the witness it gives.
    fn said_integer(&self, value: &Node, ty: super::templates::Num) -> Option<String> {
        // Lean states each as `∃ m : T, ↑m = x` of a term wider than T, of ℤ,
        // ℚ and ℝ; ℕ and ℕ₀ add an order beside m, and are not among them.
        let at = self.writer.carrier(value).built()?;
        let system = match ty {
            super::templates::Num::Int
            | super::templates::Num::Rat
            | super::templates::Num::Real => super::expr::System::Type(ty),
            _ => return None,
        };
        let wanted = self.writer.number(value, at).built()?.text();
        // The latest such line, or part of an "and": an earlier one may
        // stand in a block the step is not in.
        let mut parts = Vec::new();
        for (node, name) in self.trees.values().flatten() {
            conjuncts(node, name.clone(), &mut parts);
        }
        parts.iter().rev().find_map(|c| {
            let [term, set] = c.node.children.as_slice() else {
                return None;
            };
            let integer = c.node.notation() == crate::notations::MEMBERSHIP
                && super::expr::system_of(set) == Some(system);
            let same = self.writer.number(term, at).built().map(|p| p.text())
                == Some(wanted.clone());
            (integer && same).then(|| c.proof.clone())
        })
    }

    /// `obtain`: the witnesses of a "there is" an item gives, named as the
    /// claim names them.
    /// The "there is" an `obtain` takes its witnesses from: a line of the
    /// page it names, or a sentence of the item it cites.
    fn obtained_from(&self, i: usize) -> Route<Obtained> {
        let step = &self.thm.steps[i];
        if self.rec.cited[i].is_none() && step.just.obtained_from.is_none() {
            // The sentence, or the part of one, of the lines named that
            // says "there is".
            // A "for all" line is read at the block's letter, as the checker
            // reads it.
            let mut names = std::collections::BTreeSet::new();
            for s in step.claim.sentences() {
                if let Some(n) = self.rec.page.get(&s) {
                    names.extend(n.names());
                }
            }
            names.retain(|n| !step.just.obtained.contains(n));
            return match self
                .cited_parts(&step.just.from)
                .into_iter()
                .map(|c| self.read_at_letters(&c, &names).unwrap_or(c))
                .find(|c| {
                    c.node.notation() == crate::notations::THERE_IS
                        || &*c.node.notation_name() == "there-is-some"
                }) {
                Some(c) => Route::Built(Obtained {
                    term: c.proof,
                    says: c.node,
                    binding: crate::matching::Binding::new(),
                }),
                None => Route::no("an obtain from no line that says \"there is\""),
            };
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(at) = cited.obtained else {
            return Route::no("an obtain that takes no sentence of its item");
        };
        let before: usize = match self.sources.checked.library.groups.get(&cited.item) {
            Some(Some(groups)) => {
                groups[..cited.group].iter().map(|g| g.gives.len()).sum()
            }
            _ => 0,
        };
        let Some(sentence) = item.sentences.get(before + at) else {
            return Route::no("an obtain of a sentence the item does not have in Lean");
        };
        let mut binding = cited.binding.clone();
        for (k, v) in &cited.written {
            binding.entry(*k).or_insert_with(|| v.clone());
        }
        let lines = self.cited_parts(&step.just.from);
        let inst = match self.instance(sentence, &binding, None, &lines) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A definition's right side is the "there is"; a theorem's sentence
        // is one.
        let iff = sentence.says.notation() == BICONDITIONAL;
        let says = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right.clone(),
            _ => sentence.says.clone(),
        };
        // At the citation's values, a property given applied where the
        // sentence applies it: P(d) of set-builder is "there are m, n with
        // d = a·m + b·n".
        let says =
            read_at_values(&says, &binding, &self.sources.checked.grammar.binders());
        Route::Built(Obtained {
            term: if iff {
                format!("({inst}).mp (by parley_side)")
            } else {
                inst
            },
            says,
            binding,
        })
    }

    fn obtain(&mut self, i: usize, depth: usize) -> Route<()> {
        self.said_used.borrow_mut().clear();
        let source = match self.obtained_from(i) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let used = std::mem::take(&mut *self.said_used.borrow_mut());
        let step = &self.thm.steps[i];
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        // Lean nests a "there is" as the page does: each letter, then the
        // fact its range gives where Lean's type does not, then what is said
        // of them all. The claim's sentence about each letter's range is
        // that fact; its other sentences are what is said.
        let mut guards: IndexMap<String, String> = IndexMap::new();
        let mut body: Vec<String> = Vec::new();
        for ((node, _), name) in claim.iter().zip(&names) {
            // A letter's fact of being in a set, x ∈ A, as of a range, or
            // of being a part of one, W ⊆ X.
            let in_set = match node.children.as_slice() {
                [x, set]
                    if (node.notation() == crate::notations::MEMBERSHIP
                        || &*node.notation_name() == "subset")
                        && x.is_name()
                        && self.writer.members_of(set).is_some() =>
                {
                    Some(x.text.to_string())
                }
                _ => None,
            };
            // A function's fact of mapping one set into another, g : A → B,
            // the `Set.MapsTo` a "there is g : A → B" gives beside g.
            let maps = match node.children.as_slice() {
                [g, _, _]
                    if node.notation() == crate::notations::FUNCTION_TYPE
                        && g.is_name() =>
                {
                    Some(g.text.to_string())
                }
                _ => None,
            };
            let letter = introduces(node)
                .map(|(l, _)| l)
                .or_else(|| super::statement::range_letter(node))
                .or(in_set)
                .or(maps)
                .or_else(|| super::statement::introduces_polynomial(node));
            match letter.filter(|l| step.just.obtained.contains(l)) {
                Some(l) => {
                    guards.insert(l, name.clone());
                }
                None => body.push(name.clone()),
            }
        }
        // there is a ∈ X with nothing said, `∃ a ∈ X, True`: the letter, the
        // fact that it is in X, and nothing.
        if let ("there-is-some", [obtained]) =
            (&*source.says.notation_name(), step.just.obtained.as_slice())
        {
            let guard = guards
                .get(obtained)
                .cloned()
                .unwrap_or_else(|| "_".to_string());
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: vec![super::names::letter(obtained), guard, "_".to_string()],
                    says: None,
                    from: Printed::atom(source.term.clone()),
                },
                step.line,
                Self::step_spot(step),
            );
            return Route::Built(());
        }
        let mut pattern = Vec::new();
        let mut said = &source.says;
        // A "there is" the sentence says after an "and", u ∈ X and (there
        // are m, n with …): what comes before it, unnamed, and then it.
        while let (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [_, right],
        ) = (said.notation(), said.children.as_slice())
        {
            if right.notation() != crate::notations::THERE_IS {
                break;
            }
            pattern.push("_".to_string());
            said = right;
        }
        for obtained in &step.just.obtained {
            let [_, set, inner] = said.children.as_slice() else {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            };
            if said.notation() != crate::notations::THERE_IS {
                return Route::no(
                    "an obtain of more letters than its \"there is\" binds",
                );
            }
            pattern.push(super::names::letter(obtained));
            // Lean writes "there is s ∈ S" with the membership beside s
            // for every S but a number system its type gives, ℤ, ℚ, ℝ or
            // ℂ; the page's ℕ and ℕ₀ add that the integer s is above 0 or
            // at least 0. The set as the citation gives it, Y := ℕ.
            let given = match set.is_name() {
                true => source.binding.get(&set.text).unwrap_or(set),
                false => set,
            };
            let whole = matches!(
                super::expr::system_of(given),
                Some(super::expr::System::Positive | super::expr::System::NonNegative)
            );
            let guarded = set.notation() == crate::notations::INTEGER_RANGE
                || whole
                || super::expr::system_of(set).is_none();
            if guarded {
                // A member of the page's ℕ or ℕ₀ keeps its fact named.
                let unnamed = match whole {
                    true => format!("{}_pos", super::names::letter(obtained)),
                    false => "_".to_string(),
                };
                let guard = guards.get(obtained).cloned().unwrap_or(unnamed);
                pattern.push(guard);
            }
            said = inner;
        }
        // What is said of the letters, taken apart as Lean nests its "and":
        // ((d > 1 ∧ d ∣ p) ∧ d ∣ q) is ⟨⟨a, b⟩, c⟩.
        if !body.is_empty() {
            let mut names = body.into_iter();
            let shaped = shaped_pattern(said, &mut names);
            if names.next().is_some() {
                return Route::no(
                    "an obtain whose sentences are not the parts of its \"there is\"",
                );
            }
            pattern.push(shaped);
        }
        self.push_at(
            depth,
            Tactic::Obtain {
                names: pattern,
                says: None,
                from: Printed::atom(source.term.clone()),
            },
            step.line,
            Self::step_spot(step),
        );
        // An item given a line's number, x := the rational of `√2 ∈ ℚ`,
        // gives its facts of that number; a sentence the page says of the
        // line's term, √2 = p/q, is that fact with the goal put in terms of
        // the number.
        for ((node, prop), name) in claim.iter().zip(&names) {
            let specs = self.specs_in(node, &used);
            if specs.is_empty() {
                continue;
            }
            self.push_at(
                depth,
                Tactic::Have {
                    name: name.clone(),
                    says: prop.clone(),
                    proof: format!("by rw [{specs}]; exact_mod_cast {name}"),
                },
                step.line,
                Self::step_spot(step),
            );
        }
        Route::Built(())
    }

    /// The rewrites that put a claim in terms of the numbers lines give,
    /// `← Classical.choose_spec hS` for each line used whose term the claim
    /// has, joined for `rw`; empty where it has none.
    fn specs_in(&self, claim: &Node, used: &[SaidUsed]) -> String {
        let parts: Vec<String> = claim
            .walk()
            .iter()
            .map(|n| self.writer.grammar.print(n))
            .collect();
        let mut specs: Vec<String> = Vec::new();
        for u in used {
            let spec = format!("← Classical.choose_spec {}", u.line);
            if parts.contains(&u.term) && !specs.contains(&spec) {
                specs.push(spec);
            }
        }
        specs.join(", ")
    }

    /// A step that owns a block: its claim proved by the block's steps,
    /// opened by its lines.
    fn block(
        &mut self,
        i: usize,
        method: Method,
        claim: &[(Node, Printed)],
        names: &[String],
        depth: usize,
    ) -> Route<()> {
        let step = &self.thm.steps[i];
        let spot = Self::step_spot(step);
        // A claim Lean's types already make true needs no proof, and what
        // the block shows inside it is cited nowhere outside it.
        if claim.is_empty() {
            self.push_at(
                depth,
                Tactic::Comment("what this block shows, Lean's types give".to_string()),
                step.line,
                spot,
            );
            return Route::Built(());
        }
        // A claim of several sentences is proved as their "and", and taken
        // apart after into each sentence's name.
        let Some((claimed, _)) = claim.first() else {
            return Route::no("a block with no claim");
        };
        if claim.len() > 1 && method == Method::Induction {
            return Route::no("an induction whose claim is several sentences");
        }
        let (whole, prop) = match claim {
            [(_, prop)] => (names[0].clone(), prop.clone()),
            _ => {
                let mut pieces = Vec::new();
                for (i, (_, p)) in claim.iter().enumerate() {
                    if i > 0 {
                        pieces.push(super::doc::Piece::text(" ∧ "));
                    }
                    pieces.push(super::doc::Piece::term(p.clone(), 36));
                }
                (
                    format!("{}_all", names[0]),
                    Printed::notation(pieces, 35, super::doc::LeanType::Prop),
                )
            }
        };
        let Some(block_at) = self.rec.blocks.iter().position(|b| b.owner == i) else {
            return Route::no("a block the checker did not record");
        };
        let block = self.rec.blocks[block_at].clone();
        self.push_at(
            depth,
            Tactic::Have {
                name: whole.clone(),
                says: prop,
                proof: "by".to_string(),
            },
            step.line,
            spot.clone(),
        );
        let kept = self.writer.letters.clone();
        let kept_wholes = self.writer.wholes.clone();
        // The lines in scope as the block opens: a line one case or
        // direction says is no line of the next.
        let kept_lines = self.trees.clone();
        let parts: Vec<Option<usize>> = if step.parts.is_empty() {
            vec![None]
        } else {
            (0..step.parts.len()).map(Some).collect()
        };
        match method {
            Method::Proof | Method::Contradiction => {
                if let Route::Declined(d) = self.open(step, None, depth + 1) {
                    return Route::Declined(d);
                }
                let children: Vec<usize> = block.children.clone();
                if let Route::Declined(d) = self.steps(&children, depth + 1) {
                    return Route::Declined(d);
                }
                // A block may end on a line shown impossible, which closes
                // it; what is left, if anything, its last line gives.
                let close = match method {
                    Method::Proof if claim.len() == 1 => {
                        self.closing(children.last().copied(), claimed)
                    }
                    _ => super::tactics::bridge(BridgeTactic::Side, vec![]),
                };
                self.push_at(
                    depth + 1,
                    Tactic::AllGoals(Box::new(close)),
                    step.line,
                    spot.clone(),
                );
            }
            Method::Cases => {
                // The sentence, or the part of one, of the lines named that
                // says "or".
                // A "for all" line is read at the letters the cases assume,
                // as the checker reads it.
                let mut letters = std::collections::BTreeSet::new();
                for o in &step.openers {
                    for s in o.body(&self.thm.path).sentences() {
                        if let Some(n) = self.rec.page.get(&s) {
                            letters.extend(n.names());
                        }
                    }
                }
                let Some(said) = self
                    .cited_parts(&step.just.from)
                    .into_iter()
                    .map(|c| self.read_at_letters(&c, &letters).unwrap_or(c))
                    .find(|c| c.node.notation() == crate::notations::DISJUNCTION)
                else {
                    return Route::no("cases from no line that says \"or\"");
                };
                let source = said.proof.clone();
                let labels: Vec<String> = parts
                    .iter()
                    .map(|part| {
                        step.openers
                            .iter()
                            .find(|o| o.part == *part)
                            .map(|o| line_name(&o.label))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                // The pattern follows the "or" as the page groups it: a ∨ b
                // ∨ c read from the left is (a ∨ b) ∨ c.
                // Cases that group the "or" otherwise, a ∨ b as one case of
                // a ∨ b ∨ c ∨ d, take it restated as the cases say it, each
                // case a part of an "or" read from the right.
                let mut names = labels.iter();
                let pattern = or_pattern(&said.node, &mut names);
                let line = if disjuncts(&said.node) == labels.len() {
                    format!("rcases {source} with {pattern}")
                } else {
                    let mut says = Vec::new();
                    for part in &parts {
                        let node =
                            step.openers.iter().find(|o| o.part == *part).and_then(
                                |o| {
                                    o.body(&self.thm.path)
                                        .sentences()
                                        .first()
                                        .and_then(|s| self.rec.page.get(s))
                                        .cloned()
                                },
                            );
                        let Some(node) = node else {
                            return Route::no("a case that assumes nothing");
                        };
                        match self.writer.formula(&node) {
                            Route::Built(p) => says.push(format!("({})", p.text())),
                            Route::Declined(d) => return Route::Declined(d),
                        }
                    }
                    format!(
                        "rcases (show {} by have := {source}; tauto) with {}",
                        says.join(" ∨ "),
                        labels.join(" | ")
                    )
                };
                self.push_at(depth + 1, Tactic::Raw(line), step.line, spot.clone());
                for (part, label) in parts.iter().zip(&labels) {
                    // Each case starts from the letters as the block found
                    // them: a letter one case lets is none of the next's.
                    self.writer.letters = kept.clone();
                    self.writer.wholes = kept_wholes.clone();
                    self.trees = kept_lines.clone();
                    self.named.insert(label.clone(), vec![label.clone()]);
                    // What the case assumes, for a step that cites it.
                    if let Some(o) = step.openers.iter().find(|o| o.part == *part) {
                        let nodes: Vec<Node> = o
                            .body(&self.thm.path)
                            .sentences()
                            .iter()
                            .filter_map(|s| self.rec.page.get(s).cloned())
                            .collect();
                        if let [node] = nodes.as_slice() {
                            self.trees.insert(
                                o.label.clone(),
                                vec![(node.clone(), label.clone())],
                            );
                        }
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::tactics::call("skip", vec![]))),
                        step.line,
                        spot.clone(),
                    );
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push_at(
                        depth + 2,
                        Tactic::AllGoals(Box::new(super::tactics::bridge(
                            BridgeTactic::Side,
                            vec![],
                        ))),
                        step.line,
                        spot.clone(),
                    );
                }
            }
            Method::Induction => {
                if let Route::Declined(d) =
                    self.induction(step, &block, claimed, &parts, depth + 1)
                {
                    return Route::Declined(d);
                }
            }
            Method::BothDirections => {
                self.push_at(
                    depth + 1,
                    super::tactics::call("constructor", vec![]),
                    step.line,
                    spot.clone(),
                );
                for part in &parts {
                    self.trees = kept_lines.clone();
                    self.push_at(
                        depth + 1,
                        Tactic::Bullet(Box::new(super::tactics::call("skip", vec![]))),
                        step.line,
                        spot.clone(),
                    );
                    if let Route::Declined(d) = self.open(step, *part, depth + 2) {
                        return Route::Declined(d);
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push_at(
                        depth + 2,
                        Tactic::AllGoals(Box::new(super::tactics::bridge(
                            BridgeTactic::Side,
                            vec![],
                        ))),
                        step.line,
                        spot.clone(),
                    );
                }
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        }
        self.writer.letters = kept;
        self.writer.wholes = kept_wholes;
        if claim.len() > 1 {
            self.push_at(
                depth,
                Tactic::Obtain {
                    names: names.to_vec(),
                    says: None,
                    from: super::tactics::hyp(&whole),
                },
                step.line,
                spot,
            );
        }
        Route::Built(())
    }

    /// `induction`: "for all k ∈ ℕ₀" from 0 and "for all k ∈ ℕ" from 1 are
    /// `LeanBridges.Functions.le_induction` from 0 or 1 of the integer k; the step part's
    /// induction hypothesis keeps the page's label.
    fn induction(
        &mut self,
        step: &Step,
        block: &crate::checker::record::Block,
        claimed: &Node,
        parts: &[Option<usize>],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        let [letter, set, body] = claimed.children.as_slice() else {
            return Route::no("an induction whose claim says no \"for all\"");
        };
        if claimed.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return Route::no("an induction whose claim says no \"for all\"");
        }
        let name = super::names::letter(&letter.text);
        let start = step.just.start.as_deref().unwrap_or("");
        let from_one = match (super::expr::system_of(set), start) {
            (Some(super::expr::System::NonNegative), "0") => false,
            (Some(super::expr::System::Positive), "1") => true,
            _ => return Route::no("an induction from other than the start of ℕ or ℕ₀"),
        };
        let system = match from_one {
            true => super::expr::System::Positive,
            false => super::expr::System::NonNegative,
        };
        self.writer.introduce(&letter.text, system);
        // The letter is an integer and its guard 0 < k or 0 ≤ k; the guard
        // put as `le_induction` reads it, 1 ≤ k or 0 ≤ k, in its place, so
        // that the induction hypothesis does not ask it again.
        let start = if from_one { 1 } else { 0 };
        let guard = format!("h_{name}");
        let int = super::doc::LeanType::Num(super::templates::Num::Int);
        let from = match super::expr::relation_of(
            "≤",
            Printed::numeral(start.to_string(), int.clone()),
            Printed::letter(name.clone(), int),
        ) {
            Route::Built(r) => r,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lines = [
            Tactic::Intro(vec![name.clone(), guard.clone()]),
            Tactic::Replace {
                name: guard.clone(),
                says: from,
                proof: "by omega".to_string(),
            },
            Tactic::Induction {
                on: vec![name.clone(), guard],
                using: super::tactics::bridge_lemma(
                    "LeanBridges.Functions.le_induction",
                    BridgeModule::Functions,
                ),
            },
        ];
        for line in lines {
            self.push_at(depth, line, step.line, spot.clone());
        }
        for part in parts {
            let marker = part
                .and_then(|k| step.parts.get(k))
                .map(|(m, _)| m.as_str())
                .unwrap_or("");
            let openers: Vec<&crate::corpus::Opener> =
                step.openers.iter().filter(|o| o.part == *part).collect();
            match marker {
                "base" => {
                    self.push_at(
                        depth,
                        Tactic::Alternative("base".to_string()),
                        step.line,
                        spot.clone(),
                    );
                }
                "step" => {
                    let hypothesis = openers
                        .iter()
                        .find(|o| o.is_hypothesis)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| "IH".to_string());
                    if let Some(o) = openers.iter().find(|o| o.is_hypothesis) {
                        self.named.insert(o.label.clone(), vec![hypothesis.clone()]);
                        self.trees.insert(
                            o.label.clone(),
                            vec![(body.clone(), hypothesis.clone())],
                        );
                    }
                    let guard = openers
                        .iter()
                        .find(|o| !o.is_hypothesis && o.kind == Intro::Let)
                        .map(|o| line_name(&o.label))
                        .unwrap_or_else(|| format!("h_{name}"));
                    let case = format!("succ {name} {guard} {hypothesis}");
                    self.push_at(
                        depth,
                        Tactic::Alternative(case),
                        step.line,
                        spot.clone(),
                    );
                }
                other => return Route::no(format!("an induction part {other:?}")),
            }
            // A case proved by its own `proof` block: its lines, other than
            // the induction's letter and hypothesis, are opened as a
            // `proof` block's are.
            let own: Vec<crate::corpus::Opener> = openers
                .iter()
                .filter(|o| !o.is_hypothesis)
                .filter(|o| !self.introduces_letter(o, &letter.text))
                .map(|o| (*o).clone())
                .collect();
            if let Route::Declined(d) = self.open_lines(step, &own, depth + 1) {
                return Route::Declined(d);
            }
            let children: Vec<usize> = block
                .children
                .iter()
                .copied()
                .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                .collect();
            if let Route::Declined(d) = self.steps(&children, depth + 1) {
                return Route::Declined(d);
            }
            self.push_at(
                depth + 1,
                Tactic::AllGoals(Box::new(super::tactics::bridge(
                    BridgeTactic::Side,
                    vec![],
                ))),
                step.line,
                spot.clone(),
            );
        }
        Route::Built(())
    }

    /// Whether an opening line is the `let` of a letter, the induction's.
    fn introduces_letter(&self, o: &crate::corpus::Opener, letter: &str) -> bool {
        o.kind == Intro::Let
            && o.body(&self.thm.path)
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s))
                .any(|n| introduces(n).is_some_and(|(l, _)| l == letter))
    }

    /// The lines that open a `proof` or `contradiction` block: each `let`
    /// introduces its letter, each `assume` its fact, and a `suppose` the
    /// opposite of the claim.
    fn open(&mut self, step: &Step, part: Option<usize>, depth: usize) -> Route<()> {
        let openers: Vec<crate::corpus::Opener> = step
            .openers
            .iter()
            .filter(|o| o.part == part)
            .cloned()
            .collect();
        self.open_lines(step, &openers, depth)
    }

    /// The opening lines given, each introduced as `open` introduces it.
    fn open_lines(
        &mut self,
        step: &Step,
        openers: &[crate::corpus::Opener],
        depth: usize,
    ) -> Route<()> {
        let spot = Self::step_spot(step);
        for o in openers {
            let label = line_name(&o.label);
            self.named.insert(o.label.clone(), vec![label.clone()]);
            let body = o.body(&self.thm.path);
            let mut nodes: Vec<Node> = body
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s).cloned())
                .collect();
            // A `let` the page does not read as a formula, `let X ⊆ A`, says
            // what the checker reads it to assert.
            if nodes.is_empty() {
                nodes = self
                    .rec
                    .opener_asserted
                    .get(&o.line)
                    .cloned()
                    .unwrap_or_default();
            }
            match o.kind {
                Intro::Let => {
                    for node in &nodes {
                        if let Some(letter) = super::statement::range_letter(node) {
                            // In ℕ or ℕ₀ where the range starts at 1 or 0.
                            let system = match node.children.get(1) {
                                Some(range) => super::expr::range_letter_system(range),
                                None => super::expr::System::Type(
                                    super::templates::Num::Int,
                                ),
                            };
                            self.writer.introduce(&letter, system);
                            let letter = super::names::letter(&letter);
                            self.trees.insert(
                                o.label.clone(),
                                vec![(node.clone(), label.clone())],
                            );
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                            // The range as the page writes it: an
                            // induction's step leaves its end `↑(N + 1)`,
                            // which the page writes N + 1 and an item is
                            // given so, and Lean matching the one with the
                            // other unfolds the range past its limit.
                            self.push_at(
                                depth,
                                Tactic::Try(Box::new(super::tactics::push_cast(Some(
                                    TacticArg::At(vec![
                                        super::doc::Location::Hypothesis(label.clone()),
                                    ]),
                                )))),
                                o.line,
                                spot.clone(),
                            );
                            // The range's bounds beside it, which linear
                            // arithmetic reads, the membership kept for the
                            // items given it; a claim may state the bounds
                            // already.
                            let bounds = Printed::applied(
                                "Finset.mem_Icc.mp",
                                super::doc::Source::Mathlib,
                                vec![super::tactics::hyp(&label)],
                                super::doc::LeanType::Prop,
                            );
                            self.push_at(
                                depth,
                                Tactic::Try(Box::new(Tactic::Name {
                                    name: format!("{label}_bounds"),
                                    term: bounds,
                                })),
                                o.line,
                                spot.clone(),
                            );
                            continue;
                        }
                        if let Some((letter, ty)) =
                            super::statement::introduces_function(node)
                        {
                            self.writer.letters.insert(letter.clone(), ty);
                            self.intro(
                                depth,
                                vec![super::names::letter(&letter)],
                                o.line,
                                &spot,
                            );
                            continue;
                        }
                        // `let t ∈ S` of a set S: the member and the fact
                        // that it is one, as "for all t ∈ S" gives them.
                        // `let X ⊆ A` likewise gives a set and the fact.
                        if let [t, set] = node.children.as_slice() {
                            let member = node.notation()
                                == crate::notations::MEMBERSHIP
                                && t.is_name();
                            let part =
                                &*node.notation_name() == "subset" && t.is_name();
                            let ty = match (member, part) {
                                (true, _) => {
                                    self.writer.members_of(set).map(|m| m.letter())
                                }
                                (_, true) => {
                                    self.writer.set_members(set).map(LetterType::Set)
                                }
                                _ => None,
                            };
                            if let Some(ty) = ty {
                                self.writer.letters.insert(t.text.to_string(), ty);
                                self.trees.insert(
                                    o.label.clone(),
                                    vec![(node.clone(), label.clone())],
                                );
                                self.intro(
                                    depth,
                                    vec![super::names::letter(&t.text), label.clone()],
                                    o.line,
                                    &spot,
                                );
                                continue;
                            }
                        }
                        let Some((letter, system)) = introduces(node) else {
                            return Route::no(
                                "a let that introduces no letter of a number system",
                            );
                        };
                        self.writer.introduce(&letter, system);
                        let letter = super::names::letter(&letter);
                        if !matches!(system, super::expr::System::Type(_)) {
                            self.intro(
                                depth,
                                vec![letter.clone(), label.clone()],
                                o.line,
                                &spot,
                            );
                        } else {
                            self.intro(depth, vec![letter.clone()], o.line, &spot);
                        }
                    }
                }
                Intro::Assume => {
                    // A line of several sentences is the "and" of them,
                    // each sentence taken by its projection.
                    let n = nodes.len();
                    let said = nodes
                        .iter()
                        .enumerate()
                        .map(|(k, node)| {
                            (node.clone(), format!("{label}{}", projection(k, n)))
                        })
                        .collect();
                    self.trees.insert(o.label.clone(), said);
                    self.intro(depth, vec![label.clone()], o.line, &spot);
                }
                Intro::Suppose => {
                    let Some(node) = nodes.first() else {
                        return Route::no("a suppose the checker did not read");
                    };
                    let says = match self.writer.formula(node) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.trees
                        .insert(o.label.clone(), vec![(node.clone(), label.clone())]);
                    // The block's claim denied, and the suppose line proved
                    // from that denial in the words the page chose for it.
                    self.push_at(
                        depth,
                        super::tactics::call(
                            "by_contra",
                            vec![TacticArg::Term(super::tactics::hyp(&format!(
                                "hc_{label}"
                            )))],
                        ),
                        o.line,
                        spot.clone(),
                    );
                    self.push_at(
                        depth,
                        Tactic::Have {
                            name: label.clone(),
                            says: says.clone(),
                            proof: format!("by parley_suppose hc_{label}"),
                        },
                        o.line,
                        spot.clone(),
                    );
                }
            }
        }
        Route::Built(())
    }
}

/// What an `obtain` takes its witnesses from: the Lean term that proves the
/// "there is", and the "there is" itself.
struct Obtained {
    term: String,
    says: Node,
    /// What the cited item's letters stand for, the Y of "there is s ∈ Y"
    /// given ℕ; empty for a line of the proof, which writes its own sets.
    binding: crate::matching::Binding,
}

/// A cited line as a step uses it: the name to use, and the `have` that
/// casts it up to the claim's type where it is narrower.
struct Widened {
    have: Option<String>,
    name: String,
}

/// A tactic proof with `have` lines written before it, inside its `by`.
fn with_haves(haves: &[String], tactic: &str) -> String {
    if haves.is_empty() {
        return tactic.to_string();
    }
    let body = tactic.strip_prefix("by ").unwrap_or(tactic);
    // Each line is indented, a `have` whose own proof runs over several
    // lines included, so that its proof stays under it.
    let mut out = String::from("by");
    for h in haves {
        out.push_str(&format!("\n  {}", h.replace('\n', "\n  ")));
    }
    out.push_str(&format!("\n  {}", body.replace('\n', "\n  ")));
    out
}

/// A claim `s ∈ S`, S ℤ, ℚ or ℝ and s of a wider type, shown by an
/// equation, `name`, one side of which is in S already: that side is the
/// witness, and the equation, with the casts pushed in, its proof. None
/// where the claim or the equation is not so.
fn member_by_equation(
    writer: &Writer,
    equation: &Node,
    name: &str,
    claim: &Node,
    ctx: &crate::matching::Context,
) -> Option<String> {
    let [term, set] = claim.children.as_slice() else {
        return None;
    };
    if claim.notation() != crate::notations::MEMBERSHIP
        || set.notation() != crate::notations::NUMBER_SYSTEMS
        || equation.notation() != EQUALITY
    {
        return None;
    }
    let super::expr::System::Type(n) = super::expr::system_of(set)? else {
        return None;
    };
    if writer.carrier(term).built()? <= n {
        return None;
    }
    // The equation is of the claim's term: a = 1 shows nothing of √b + 1.
    if !equation
        .children
        .iter()
        .any(|side| crate::matching::alike_top(side, term, ctx))
    {
        return None;
    }
    equation.children.iter().find_map(|side| {
        let fits = writer.carrier(side).built().is_some_and(|c| c <= n);
        if !fits || side.names().is_empty() && !writer.is_number(side) {
            return None;
        }
        let w = writer.number_fixed(side, n).built()?;
        let proof = by_ways(rewritten_by(name));
        Some(format!("⟨{}, {proof}⟩", w.text()))
    })
}

/// A witness as Lean writes it, and the tactic that puts what a line says
/// of it in scope, where it is an integer a line gives.
struct Witness {
    term: String,
    known: Option<String>,
}

/// A define a step cites: its letter, the term it names, and the Lean name
/// of its equation.
struct CitedDefine {
    name: Node,
    value: Node,
    proof: String,
    /// The argument of a function's define, the j of q(j) = F(j)², which
    /// each application q(a) puts a for; None for a define of a term.
    param: Option<String>,
}

/// The tactic lines that write the defines out wherever they stand, and
/// push in the casts that leaves; none where no define is cited.
fn written_out(defines: &[CitedDefine]) -> Vec<String> {
    if defines.is_empty() {
        return Vec::new();
    }
    let rewrites: Vec<&str> = defines.iter().map(|d| d.proof.as_str()).collect();
    vec![
        format!("try simp only [{}] at *", rewrites.join(", ")),
        "try push_cast at *".to_string(),
    ]
}

/// `node` with `to` put for each part that is `from`, the two compared as
/// the grammar prints them.
/// Whether putting one side of `equation` for the other in the left side of
/// `claim`, an equation, gives its right side.
fn makes_claim(
    equation: &Node,
    claim: &Node,
    grammar: &crate::formula::Grammar,
) -> bool {
    let (Some([from, to]), Some([left, right])) = (
        equation.children.as_slice().first_chunk::<2>(),
        claim.children.as_slice().first_chunk::<2>(),
    ) else {
        return false;
    };
    let want = grammar.print(right);
    [(from, to), (to, from)]
        .iter()
        .any(|(a, b)| grammar.print(&put_term(left, a, b, grammar)) == want)
}

fn put_term(
    node: &Node,
    from: &Node,
    to: &Node,
    grammar: &crate::formula::Grammar,
) -> Node {
    if grammar.print(node) == grammar.print(from) {
        return to.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_term(c, from, to, grammar))
            .collect(),
    )
}

/// `node` with `value` put for each place the letter `name` stands.
fn put_for(node: &Node, name: &Node, value: &Node) -> Node {
    if node.is_name() && node.text == name.text {
        return value.clone();
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| put_for(c, name, value))
            .collect(),
    )
}

/// How many statements an "or" joins, however it groups them.
fn disjuncts(node: &Node) -> usize {
    if node.notation() == crate::notations::DISJUNCTION {
        node.children.iter().map(disjuncts).sum()
    } else {
        1
    }
}

/// An `rcases` pattern for an "or" as its tree groups it, each disjunct
/// named in turn from `names`: `(C1 | C2) | C3` for (a ∨ b) ∨ c.
fn or_pattern(node: &Node, names: &mut std::slice::Iter<'_, String>) -> String {
    if let ([left, right], crate::notations::DISJUNCTION) =
        (node.children.as_slice(), node.notation())
    {
        let l = or_pattern(left, names);
        let r = or_pattern(right, names);
        let l = if left.notation() == crate::notations::DISJUNCTION {
            format!("({l})")
        } else {
            l
        };
        return format!("{l} | {r}");
    }
    names.next().cloned().unwrap_or_else(|| "_".to_string())
}

/// A line whose proof runs over several lines, each line after the first
/// indented by `pad` as the first is.
fn indented(text: &str, pad: &str) -> String {
    text.replace('\n', &format!("\n{pad}"))
}

/// The lines a step cites anywhere in its reason: its own references, the
/// line it substitutes into, and those its calculation's rows cite, by a
/// reason of their own or alone.
fn step_cited_refs(step: &crate::corpus::Step, path: &str) -> Vec<String> {
    let mut out: Vec<String> = step.just.refs.clone();
    let into = |j: &Justification| j.into.as_ref().map(|p| p.named().to_string());
    out.extend(into(&step.just));
    if let Some(Ok(chain)) = crate::corpus::proof::chain(&step.just, path) {
        for line in &chain.lines {
            match &line.reason {
                Some(r) => {
                    if let Ok(by) = &r.by {
                        out.extend(by.refs.iter().cloned());
                        out.extend(into(by));
                    }
                }
                None => {
                    if let Some(cited) = crate::corpus::proof::chain_cited(&line.cite) {
                        out.push(cited);
                    }
                }
            }
        }
    }
    let mut seen = std::collections::BTreeSet::new();
    out.retain(|r| seen.insert(r.clone()));
    out
}

/// The child indices that lead from `node` to a part of the shape of `part`,
/// the first in the tree's order; None where there is none.
fn path_to(node: &Node, part: &Node) -> Option<Vec<usize>> {
    if node.same_shape(part) {
        return Some(Vec::new());
    }
    node.children.iter().enumerate().find_map(|(i, c)| {
        let mut rest = path_to(c, part)?;
        rest.insert(0, i);
        Some(rest)
    })
}

/// The part of `node` the child indices lead to; None where they lead off
/// the tree.
fn at_path<'n>(node: &'n Node, path: &[usize]) -> Option<&'n Node> {
    match path.split_first() {
        None => Some(node),
        Some((i, rest)) => at_path(node.children.get(*i)?, rest),
    }
}

/// Whether the node is the function `f` applied at the letter `k`, N(k).
fn applied_at(node: &Node, f: &str, k: &str) -> bool {
    match node.children.as_slice() {
        [head, arg] => {
            node.notation() == crate::notations::APPLICATION
                && head.is_name()
                && &*head.text == f
                && arg.is_name()
                && &*arg.text == k
        }
        _ => false,
    }
}

/// A letter for a value no letter of the writer's or `taken` is: v, or w,
/// u, or v with a number.
fn fresh_letter(writer: &Writer, taken: &str) -> String {
    let free = |l: &str| l != taken && !writer.letters.contains_key(l);
    if let Some(l) = ["v", "w", "u"].into_iter().find(|l| free(l)) {
        return l.to_string();
    }
    let mut i = 1;
    loop {
        let l = format!("v{i}");
        if free(&l) {
            return l;
        }
        i += 1;
    }
}

/// Whether a claim has a power the writer writes as a natural power to an
/// integer's `toNat`, 2^(k + 1) of k ∈ ℕ₀: its exponent is no natural Lean
/// computes and is said once in ℕ₀ (`Writer::said_whole`).
fn has_natural_power(claim: &Node, writer: &Writer) -> bool {
    claim.walk().iter().any(|n| {
        n.notation() == crate::notations::POWER
            && n.children
                .get(1)
                .is_some_and(|e| !writer.natural(e) && writer.said_whole(e))
    })
}

/// Whether a claim has a power the writer writes as an integer power, its
/// exponent neither a natural Lean computes nor said once in ℕ₀, 2^(F + (i
/// − n)): a line it is read from may have the natural power there.
fn has_integer_power(claim: &Node, writer: &Writer) -> bool {
    claim.walk().iter().any(|n| {
        n.notation() == crate::notations::POWER
            && n.children
                .get(1)
                .is_some_and(|e| !writer.natural(e) && !writer.said_whole(e))
    })
}

/// The alternatives that close a goal from the item term `term` where one
/// has natural powers to an integer's `toNat` and the other integer powers,
/// 2^(k + 1).toNat beside 2^(k + 1): both read as integer powers, the
/// `toNat` cast back by the exponent's fact; or both read as natural
/// powers, each integer power whose exponent is at least 0 taken to one, in
/// the goal and the term alike, inside a sum by the index's range,
/// (k − 1) + 1 ≥ 0 of k ∈ {1, …, m + 1}.
fn to_natural_powers(term: &Printed) -> Vec<Tactic> {
    use super::tactics as t;
    let h = || t::hyp("h");
    // An exponent's fact found where the index's range says it.
    let range = t::steps(vec![
        t::simp_only(
            false,
            None,
            vec![t::forwards(t::lemma("Finset.mem_Icc"))],
            Some(TacticArg::At(vec![super::doc::Location::Everywhere])),
        ),
        Tactic::First(vec![
            t::call("omega", vec![]),
            t::call("positivity", vec![]),
            t::call("nlinarith", vec![]),
        ]),
    ]);
    vec![
        t::steps(vec![
            t::name_h(term),
            t::simp_only(
                false,
                Some(t::call("omega", vec![])),
                vec![
                    t::backwards(t::lemma("zpow_natCast")),
                    t::forwards(t::lemma("Int.toNat_of_nonneg")),
                ],
                Some(t::at_h(true)),
            ),
            Tactic::Exact(h()),
        ]),
        t::steps(vec![
            t::name_h(term),
            t::simp_only(
                true,
                Some(range),
                vec![t::forwards(t::bridge_lemma(
                    "parley_zpow_toNat",
                    BridgeModule::PowerTactics,
                ))],
                Some(t::at_h(true)),
            ),
            Tactic::First(vec![
                Tactic::Exact(h()),
                t::exact_mod_cast(h()),
                t::linear_combination(h()),
            ]),
        ]),
    ]
}

/// A sentence's parts, a conjunction taken apart by Lean's projections,
/// `H3.1` and `H3.2`, as the tree joins them.
fn conjuncts(node: &Node, proof: String, out: &mut Vec<super::algebra::Cited>) {
    let joined = matches!(
        node.notation(),
        crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
    );
    if let ([left, right], true) = (node.children.as_slice(), joined) {
        conjuncts(left, format!("{proof}.1"), out);
        conjuncts(right, format!("{proof}.2"), out);
        return;
    }
    out.push(super::algebra::Cited {
        node: node.clone(),
        proof,
    });
}

/// A claim proved from a term that gives it, as the claim's shape asks:
/// an equation by the ring identity between the two, an order by linear
/// arithmetic, anything else as it stands.
/// A sentence of an item with each property the citation gives by what it
/// says, P := t ↦ …, applied where the sentence applies it: P(u) its body
/// with u's value for t. The item's other letters stay as its statement
/// has them, as Lean's statement of it does.
fn read_at_values(
    node: &Node,
    binding: &crate::matching::Binding,
    binders: &crate::matching::FxIndexMap<
        crate::formula::notation_id::NotationId,
        crate::formula::notation::Binds,
    >,
) -> Node {
    if let ("holds-of", [p, arg]) = (&*node.notation_name(), node.children.as_slice()) {
        if let Some(stands) = binding.get(&p.text) {
            if let ("property-of", [body]) =
                (&*stands.notation_name(), stands.children.as_slice())
            {
                let arg = crate::matching::substitute_apart_by(arg, binding, binders);
                let put = crate::matching::Binding::from([(stands.text, arg)]);
                return crate::matching::substitute_apart_by(body, &put, binders);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| read_at_values(c, binding, binders))
            .collect(),
    )
}

/// Whether a fact speaks of a letter the claim's leading "for all" binds.
fn bound_in(claim: &Node, fact: &Node) -> bool {
    let mut body = claim;
    let mut bound = Vec::new();
    while let (crate::notations::FOR_ALL, [letter, _, inner]) =
        (body.notation(), body.children.as_slice())
    {
        bound.push(letter.text.to_string());
        body = inner;
    }
    let names = fact.names();
    bound.iter().any(|b| names.iter().any(|n| **n == **b))
}

/// The fact under the claim's leading "for all" binders, x² ≥ 0 as "for
/// all x ∈ [0, 1], x² ≥ 0".
fn under_binders(claim: &Node, fact: &Node) -> Node {
    match (claim.notation(), claim.children.as_slice()) {
        (crate::notations::FOR_ALL, [letter, set, inner]) => claim.with_children(vec![
            letter.clone(),
            set.clone(),
            under_binders(inner, fact),
        ]),
        _ => fact.clone(),
    }
}

/// What an exhibit says of its values, taken apart as Lean nests its "and",
/// each part left to `parley_side` with what the witnesses give known: a
/// part alone is a line in scope, where the whole "and" may send `simp`
/// past its depth.
fn facts_shaped(said: &Node, known: &str) -> String {
    match (said.notation(), said.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            format!("⟨{}, {}⟩", facts_shaped(l, known), facts_shaped(r, known))
        }
        _ => format!("by {known}parley_side"),
    }
}

/// An `obtain` pattern for a sentence, one name to each part of its "and"
/// as it nests, the names taken in order; a part left with no name is `_`.
fn shaped_pattern(said: &Node, names: &mut impl Iterator<Item = String>) -> String {
    match (said.notation(), said.children.as_slice()) {
        (
            crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION,
            [l, r],
        ) => {
            let left = shaped_pattern(l, names);
            let right = shaped_pattern(r, names);
            format!("⟨{left}, {right}⟩")
        }
        _ => names.next().unwrap_or_else(|| "_".to_string()),
    }
}

/// A proof as a tactic to stand among `first`'s alternatives: its own
/// tactics where it is a `by` block, as an error inside a nested `by`,
/// `exact (by …)`, is logged and does not fail the alternative, so `first`
/// would not go on to the next.
/// A proof of a claim said "for all", made of a proof of its body: the
/// letters introduced, then the body's proof. A body proved by a block of
/// tactics on lines of their own, `by` and a line break, takes the `intro`
/// as its first line, at the block's indentation, since a block cannot
/// follow `intro …;` on its line.
fn after_intros(intros: &[String], proof: &str) -> String {
    let names = intros.join(" ");
    match proof.strip_prefix("by\n") {
        Some(block) => {
            let indent: String = block.chars().take_while(|c| *c == ' ').collect();
            format!("by\n{indent}intro {names}\n{block}")
        }
        None => format!("by intro {names}; {}", as_tactic(proof)),
    }
}

fn as_tactic(proof: &str) -> String {
    match proof.strip_prefix("by ") {
        Some(t) => format!("({t})"),
        None => format!("exact ({proof})"),
    }
}

/// `by parley_side`: a claim left to the bridges' side tactic.
fn side_proof() -> String {
    super::doc::Proof::By(super::tactics::bridge(BridgeTactic::Side, vec![])).text()
}

/// `by` and the ways a step is closed, tried in order: `by t` of one way,
/// `by first | a | b` of several.
fn by_ways(ways: Vec<Tactic>) -> String {
    let tactic = match <[Tactic; 1]>::try_from(ways) {
        Ok([one]) => one,
        Err(ways) => Tactic::First(ways),
    };
    super::doc::Proof::By(tactic).text()
}

fn close(writer: &Writer, claim: &Node, term: &str) -> String {
    super::doc::Proof::By(Tactic::First(closers(writer, claim, term))).text()
}

/// The ways a claim is closed from a term that proves it, or something
/// near it, tried in order (`close`).
/// The ways a claim follows from an equation a line names, either way
/// round: by `linarith`, by rewriting with it, or as the line itself.
fn rewritten_by(name: &str) -> Vec<Tactic> {
    use super::tactics as t;
    let line = || t::hyp(name);
    vec![
        t::steps(vec![
            t::push_cast(None),
            t::call("linarith", vec![t::rules(vec![line()])]),
        ]),
        rewrite_then_ring(t::forwards(line())),
        rewrite_then_ring(t::backwards(line())),
        Tactic::Exact(line()),
        Tactic::Exact(t::symm(line())),
    ]
}

/// `(rw [rule]; push_cast; ring)`.
fn rewrite_then_ring(rule: super::doc::Rule) -> Tactic {
    use super::tactics as t;
    t::steps(vec![
        t::call("rw", vec![TacticArg::Rules(vec![rule])]),
        t::push_cast(None),
        t::call("ring", vec![]),
    ])
}

/// `parley_subst e`: the equation e put into the goal.
fn subst_by(equation: &str) -> Tactic {
    use super::tactics as t;
    t::bridge(BridgeTactic::Subst, vec![TacticArg::Term(t::hyp(equation))])
}

/// `parley_put_at e h` or `parley_subst_at e h`: the equation e put into
/// the line h.
fn put_into(tactic: BridgeTactic, equation: &str, into: &str) -> Tactic {
    use super::tactics as t;
    t::bridge(
        tactic,
        vec![
            TacticArg::Term(t::hyp(equation)),
            TacticArg::Term(t::hyp(into)),
        ],
    )
}

/// `(simp (disch := omega) only [h]; done)` and `(simp (disch := omega)
/// only [h]; push_cast; norm_num; done)`: a claim made true by the
/// equations of the defines cited, as they stand or once worked out.
fn unfolded(defines: &[String]) -> Vec<Tactic> {
    use super::tactics as t;
    let rules: Vec<super::doc::Rule> =
        defines.iter().map(|d| t::forwards(t::hyp(d))).collect();
    let simp =
        || t::simp_only(false, Some(t::call("omega", vec![])), rules.clone(), None);
    vec![
        t::steps(vec![simp(), t::call("done", vec![])]),
        t::steps(vec![
            simp(),
            t::push_cast(None),
            t::call("norm_num", vec![]),
            t::call("done", vec![]),
        ]),
    ]
}

/// A named number's equation with its term: the one a step proves, by its
/// name, or the line's witness's, `Classical.choose_spec h`.
fn spec_of(said: &super::expr::SaidInteger) -> Printed {
    let proof = Printed::atom(said.proof.clone());
    match said.value {
        Some(_) => proof,
        None => Printed {
            kind: super::doc::TermKind::App {
                head: Box::new(Printed::head(
                    "Classical.choose_spec",
                    super::doc::Source::Core,
                )),
                args: vec![super::doc::Arg::Explicit(proof)],
                explicit: false,
            },
            ty: None,
        },
    }
}

/// `by first | (push_cast; simp only [specs]; done) | (push_cast; simp only
/// [specs]; ring)`: a claim made true by the named numbers' equations, as
/// they stand or once worked out.
fn specs_equal(specs: &[Printed]) -> String {
    use super::tactics as t;
    let rules: Vec<super::doc::Rule> = specs.iter().cloned().map(t::forwards).collect();
    by_ways(vec![
        specs_then(&rules, t::call("done", vec![])),
        specs_then(&rules, t::call("ring", vec![])),
    ])
}

/// `(push_cast; simp only [specs]; last)`.
fn specs_then(rules: &[super::doc::Rule], last: Tactic) -> Tactic {
    use super::tactics as t;
    t::steps(vec![
        t::push_cast(None),
        t::simp_only(false, None, rules.to_vec(), None),
        last,
    ])
}

/// `(have h := t; (try push_cast at h); (try push_cast); linear_combination
/// (norm := parley_norm) e)`: the citation with its casts pushed in on both
/// sides, then the claim as a combination of it.
fn pushed_then(cited: &Printed, by: Printed) -> Tactic {
    use super::tactics as t;
    t::on_h(
        cited,
        vec![
            t::try_(t::push_cast(Some(t::at_h(false)))),
            t::try_(t::push_cast(None)),
            t::linear_combination(by),
        ],
    )
}

/// `simp (disch := parley_side) only [parley_cast_toNat] at h`: a natural
/// given as an integer's `toNat` put back as the integer, cast to ℚ or ℝ.
fn cast_to_nat_at_h() -> Tactic {
    use super::tactics as t;
    t::simp_only(
        false,
        Some(t::bridge(BridgeTactic::Side, vec![])),
        vec![t::forwards(t::bridge_lemma(
            "parley_cast_toNat",
            BridgeModule::PowerTactics,
        ))],
        Some(t::at_h(false)),
    )
}

fn closers(writer: &Writer, claim: &Node, term: &str) -> Vec<Tactic> {
    use super::tactics as t;
    let cited = Printed::atom(term);
    let h = || t::hyp("h");
    // An equation or order between sets, members or counts is closed as
    // any other claim: the closers for numbers work in a field or a ring.
    let of_numbers = claim
        .children
        .iter()
        .all(|c| c.sort.is("number") && !writer.counts(c));
    match claim.notation() {
        // An instance whose casts sit otherwise than the claim's, ↑(0 : ℕ)
        // for 0, is taken with them pushed in, and one whose equation the
        // claim turns round, as a cited rule written a + b = c claimed as
        // c = a + b, is taken negated. A corpus theorem stated in a
        // wider type than the claim, ℝ for a claim in ℚ, has the claim moved
        // up to it.
        EQUALITY if of_numbers => {
            // A remainder of integers written with `%`, beside an item of
            // set.mm's mod of real numbers: the item's put as `%` first.
            let of_mod = claim.walk().iter().any(|n| &*n.notation_name() == "mod");
            let as_remainder = of_mod.then(|| {
                let mod_lemma = |name| {
                    t::forwards(t::bridge_lemma(name, BridgeModule::Divisibility))
                };
                t::steps(vec![
                    t::name_h(&cited),
                    t::simp_only(
                        false,
                        Some(t::call("positivity", vec![])),
                        vec![
                            mod_lemma("LeanBridges.Divisibility.mod_natCast"),
                            mod_lemma("LeanBridges.Divisibility.mod_intCast"),
                        ],
                        Some(t::at_h(true)),
                    ),
                    t::exact_mod_cast(t::hyp("h")),
                ])
            });
            // A term given a natural as an integer's `toNat`, rewritten back
            // by `▸` (`instance`): an error elaborating it against the goal,
            // as `exact_mod_cast` does, is logged and does not fail the
            // alternative, so it is cast from a `have`, which fails.
            // An item stated over ℂ, given the claim's real numbers cast up,
            // `(P : ℂ)`, where the claim is in ℝ: the item read back in ℝ.
            let below_complex = claim
                .children
                .iter()
                .filter_map(|c| writer.carrier(c).built())
                .all(|n| n < super::templates::Num::Complex);
            let of_complex = (term.contains(" : ℂ)") && below_complex).then(|| {
                t::on_h(
                    &cited,
                    vec![t::bridge(
                        BridgeTactic::OfComplex,
                        vec![TacticArg::Term(h())],
                    )],
                )
            });
            // An item over ℝ given rationals, the geometric sum at a := 2,
            // where the claim is written in its own type, ℚ: cast down.
            let mut of_real: Vec<Tactic> = term
                .contains(": ℝ)")
                .then(|| {
                    t::on_h(
                        &cited,
                        vec![t::bridge(
                            BridgeTactic::RatOfReal,
                            vec![TacticArg::Term(h())],
                        )],
                    )
                })
                .into_iter()
                .collect();
            // Natural powers to an integer's `toNat` on one side, integer
            // powers on the other (`to_natural_powers`).
            if term.contains(".toNat") || has_natural_power(claim, writer) {
                of_real.extend(to_natural_powers(&cited));
            }
            // An item that counts in ℕ∞, |∅| = 0, met in ℤ: the goal's
            // counts of finite sets said in ℕ∞ (`parley_count_ext`), where
            // the item meets it as it stands, before the `exact_mod_cast`
            // below, whose error is logged as above.
            let counted = claim
                .walk()
                .iter()
                .any(|n| &*n.notation_name() == "cardinality");
            let counted = counted.then(|| {
                t::steps(vec![
                    t::bridge(BridgeTactic::CountExt, vec![]),
                    t::exact_mod_cast(cited.clone()),
                ])
            });
            let by_to_nat = term.contains("Int.toNat_of_nonneg");
            // The `▸` of a `toNat` rewrites its cast to ℤ only; one cast to
            // ℚ or ℝ, (1 − 2y).toNat in ℚ, is put back as the integer by
            // `parley_cast_toNat`.
            // The term itself, given to `linear_combination`: not one with a
            // `toNat` put back by `▸`, whose error is logged as above; the
            // `have` after it takes that one.
            let direct = (!by_to_nat).then(|| t::linear_combination(cited.clone()));
            let cast = match by_to_nat {
                true => vec![
                    t::on_h(&cited, vec![t::exact_mod_cast(h())]),
                    t::on_h(&cited, vec![t::exact_mod_cast(t::symm(h()))]),
                    t::on_h(
                        &cited,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            t::linear_combination(h()),
                        ],
                    ),
                ],
                false => vec![
                    t::exact_mod_cast(cited.clone()),
                    t::exact_mod_cast(t::symm(t::bracket(cited.clone()))),
                ],
            };
            let negated = Printed {
                kind: super::doc::TermKind::Neg(Box::new(h())),
                ty: None,
            };
            let mut out: Vec<Tactic> = direct.into_iter().collect();
            out.push(pushed_then(&cited, h()));
            out.push(pushed_then(&cited, negated));
            out.extend(counted);
            out.extend(cast);
            out.push(t::on_h(
                &cited,
                vec![t::call("rify", vec![]), t::linear_combination(h())],
            ));
            out.push(t::on_h(
                &cited,
                vec![t::call("qify", vec![]), t::linear_combination(h())],
            ));
            out.push(t::on_h(
                &cited,
                vec![t::bridge(
                    BridgeTactic::IntPower,
                    vec![TacticArg::Term(h())],
                )],
            ));
            out.extend(as_remainder);
            out.extend(of_complex);
            out.extend(of_real);
            out.push(t::on_h(&cited, vec![t::bridge(BridgeTactic::Side, vec![])]));
            out
        }
        // A numeral given to a letter of ℕ arrives cast, ((3 : ℕ) : ℤ),
        // which linarith reads only once the cast is pushed in.
        // An item over ℝ cited for a claim the page computes in ℚ gives
        // the claim cast up, which exact_mod_cast brings down.
        ORDER if of_numbers => {
            // An item's integer powers, 2^1 < 2^p of an item whose exponents
            // are any integers, cited for a claim of natural powers to an
            // integer's `toNat`: the item's taken to natural ones by the
            // exponents' facts, then cast as the claim is.
            // The other way, a "for all j ∈ ℕ₀" line read at j := i − n
            // beside the claim's integer power 2^(F + (i − n)): the same,
            // the claim's powers taken too. Tried first, where it applies:
            // `linarith` over such powers can run past Lean's time limit.
            let to_nat = (has_natural_power(claim, writer)
                || has_integer_power(claim, writer)
                || term.contains(".toNat"))
            .then(|| {
                t::on_h(
                    &cited,
                    vec![
                        t::simp_only(
                            false,
                            Some(Tactic::First(vec![
                                t::call("omega", vec![]),
                                t::call("positivity", vec![]),
                                t::call("nlinarith", vec![]),
                            ])),
                            vec![t::forwards(t::bridge_lemma(
                                "parley_zpow_toNat",
                                BridgeModule::PowerTactics,
                            ))],
                            Some(t::at_h(true)),
                        ),
                        Tactic::First(vec![
                            t::exact_mod_cast(h()),
                            t::call("linarith", vec![]),
                        ]),
                    ],
                )
            });
            let mut out: Vec<Tactic> = to_nat.into_iter().collect();
            out.push(t::call("linarith", vec![t::rules(vec![cited.clone()])]));
            out.push(t::on_h(
                &cited,
                vec![
                    t::push_cast(Some(t::at_h(false))),
                    t::call("linarith", vec![]),
                ],
            ));
            out.push(t::exact_mod_cast(cited.clone()));
            out.push(t::on_h(&cited, vec![t::bridge(BridgeTactic::Side, vec![])]));
            out
        }
        // A relation said either way round, a congruence or a ↔, as the
        // claim writes it. Here and above, the last way takes the
        // citation's "and" apart: a definition unfolded to "p > 1 and for
        // all d …" gives either half. A claim with a listed set in it, which
        // may be in another order than the item's, {w, u} for {u, w}, is put
        // in one order on both sides.
        _ => {
            let listed = claim.walk().iter().any(|n| {
                matches!(
                    &*n.notation_name(),
                    "listed-two" | "listed-three" | "listed-four"
                )
            });
            // An equation of sets, member by member, which takes a listed
            // set in any order and of any size; another relation, its pairs
            // turned round.
            let reorder = match (listed, claim.notation() == EQUALITY) {
                (true, true) => {
                    let x = t::hyp("x");
                    let applied = Printed {
                        kind: super::doc::TermKind::App {
                            head: Box::new(h()),
                            args: vec![super::doc::Arg::Explicit(x.clone())],
                            explicit: false,
                        },
                        ty: None,
                    };
                    Some(t::on_h(
                        &cited,
                        vec![
                            t::call("ext", vec![TacticArg::Term(x)]),
                            t::call(
                                "rw",
                                vec![
                                    t::rules(vec![t::lemma("Set.ext_iff")]),
                                    t::at_h(false),
                                ],
                            ),
                            t::call("specialize", vec![TacticArg::Term(applied)]),
                            t::simp_only(
                                false,
                                None,
                                vec![
                                    t::forwards(t::lemma("Set.mem_insert_iff")),
                                    t::forwards(t::lemma("Set.mem_singleton_iff")),
                                ],
                                Some(t::at_h(true)),
                            ),
                            t::call("tauto", vec![]),
                        ],
                    ))
                }
                (true, false) => Some(t::on_h(
                    &cited,
                    vec![
                        t::simp_only(
                            false,
                            None,
                            vec![
                                t::forwards(t::lemma("Set.pair_comm")),
                                t::forwards(t::lemma("Set.insert_comm")),
                            ],
                            Some(t::at_h(true)),
                        ),
                        Tactic::Exact(h()),
                    ],
                )),
                (false, _) => None,
            };
            // A natural given as an integer's `toNat`, put back by `▸`: an
            // error elaborating that against the goal is logged and does not
            // fail the alternative, so the term is stated by a `have`, which
            // fails. `▸` puts it back only where it is cast to ℤ; cast to ℚ
            // or ℝ, m/(2^p − 1).toNat inside a "there is", it is put back by
            // `parley_cast_toNat`.
            match term.contains("Int.toNat_of_nonneg") {
                true => {
                    let mut out = vec![
                        t::on_h(&cited, vec![Tactic::Exact(h())]),
                        t::on_h(&cited, vec![Tactic::Exact(t::symm(h()))]),
                        t::on_h(
                            &cited,
                            vec![t::call("simpa", vec![TacticArg::Using(h())])],
                        ),
                        t::on_h(&cited, vec![t::exact_mod_cast(h())]),
                    ];
                    out.extend(reorder);
                    out.push(t::on_h(
                        &cited,
                        vec![
                            cast_to_nat_at_h(),
                            t::try_(t::push_cast(Some(t::at_h(true)))),
                            Tactic::Exact(h()),
                        ],
                    ));
                    out.push(t::on_h(
                        &cited,
                        vec![t::bridge(BridgeTactic::Side, vec![])],
                    ));
                    out
                }
                false => {
                    // A natural power to an integer's `toNat` on one side and
                    // an integer power on the other, 2^(k + 1).toNat in the
                    // claim and 2^(k + 1) in an item whose exponent is any
                    // integer: both read as integer powers, the `toNat` cast
                    // back by 0 ≤ k + 1.
                    let int_power = match term.contains(".toNat")
                        || has_natural_power(claim, writer)
                    {
                        true => to_natural_powers(&cited),
                        false => Vec::new(),
                    };
                    // A line in ℝ taken at a value, ε := 1/2, whose claim of
                    // rationals is written in its own type, ℚ: cast down.
                    let of_real = term.contains(": ℝ)").then(|| {
                        t::on_h(
                            &cited,
                            vec![t::bridge(
                                BridgeTactic::RatOfReal,
                                vec![TacticArg::Term(h())],
                            )],
                        )
                    });
                    let mut out = vec![
                        Tactic::Exact(cited.clone()),
                        Tactic::Exact(t::symm(t::bracket(cited.clone()))),
                        t::call("simpa", vec![TacticArg::Using(cited.clone())]),
                        t::exact_mod_cast(cited.clone()),
                    ];
                    out.extend(reorder);
                    out.extend(int_power);
                    out.extend(of_real);
                    out.push(t::on_h(
                        &cited,
                        vec![t::bridge(BridgeTactic::Side, vec![])],
                    ));
                    out
                }
            }
        }
    }
}
