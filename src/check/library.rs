//! What each theorem's lines give the checks that read them.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::IndexMap;

use super::structure::{labels_in_scope, Declared};
use crate::citing::{claimed_member, finished, with_parts, Library, Parts};
use crate::corpus::{Step, StepNo, Theorem};
use crate::formula::{parse_here, Node, Sorts};
use crate::matching::{expand, instantiation, standard, Binding, Context, Definitions};
use crate::sorts::{cited_defines, file_definitions, said_by_line, sentences, Env};

type PartsKey = (StepNo, Vec<String>, Vec<String>);

/// Every line a step's citation may name, by the reference that names it.
pub type Statements = IndexMap<String, String>;

/// What a theorem's lines give every check of it, read once a run.
///
/// The sort of each name depends on the theorem alone, what each `define`
/// stands for on the lines a citation names, the lines a citation may name
/// on its step, and what a step's citation supplies on the step. Each is
/// read the first time a check asks and kept for the run; nothing that uses
/// them changes them.
///
/// What a step's citation supplies is kept by what it depends on — the
/// step, the lines it names and its requires lines — so that a step with a
/// line taken away, as `check_surplus` asks about, is read afresh.
pub struct Known<'a> {
    pub thm: &'a Theorem,
    pub env: Env<'a>,
    pub sorts: Sorts,
    /// What the notations are, read once for the corpus: which spelling of a
    /// relation is another turned around (`matching::standard`).
    ctx: &'a Context,
    /// What each definition from outside the theorem stands for, written
    /// out wherever it is used.
    outside: Definitions,
    cited: RefCell<IndexMap<Vec<String>, Rc<Definitions>>>,
    scopes: RefCell<IndexMap<(StepNo, usize), Rc<Statements>>>,
    parts: RefCell<IndexMap<PartsKey, Rc<Parts>>>,
}

impl<'a> Known<'a> {
    /// `sorts` is what the theorem's one reading settled (`check::run`).
    pub fn new(
        thm: &'a Theorem,
        env: Env<'a>,
        sorts: Sorts,
        ctx: &'a Context,
    ) -> Known<'a> {
        Known {
            thm,
            env,
            sorts,
            ctx,
            outside: file_definitions(thm, env),
            cited: RefCell::new(IndexMap::new()),
            scopes: RefCell::new(IndexMap::new()),
            parts: RefCell::new(IndexMap::new()),
        }
    }

    /// A sentence as the checks of `step` compare it: parsed with its sorts,
    /// each defined name the step's citation lets it write out written out
    /// (`citing`); None where it does not read, which `check_formulas`
    /// reports.
    pub fn read(&self, step: &Step, text: &str) -> Option<Node> {
        self.read_citing(text, &self.citing(&step.just.refs))
    }

    /// The text read with its defined names kept, as a message prints it.
    pub fn read_as_written(&self, text: &str) -> Option<Node> {
        parse_here(text, self.env.g, &self.sorts).ok()
    }

    /// What a defined name stands for in a citation naming `refs`: a
    /// definition from outside the theorem everywhere, and one of the
    /// theorem's `define` lines only where the citation names it. A defined
    /// name and the term it names are one formula in a step that cites the
    /// define (`SYNTAX.md`), and the elaborator reads a citation the same way.
    pub fn citing(&self, refs: &[String]) -> Rc<Definitions> {
        if let Some(found) = self.cited.borrow().get(refs) {
            return found.clone();
        }
        let mut made = self.outside.clone();
        made.extend(cited_defines(self.thm, self.env, &self.sorts, refs));
        let made = Rc::new(made);
        self.cited.borrow_mut().insert(refs.to_vec(), made.clone());
        made
    }

    /// A sentence read with what `defined` writes out (`citing`), in the
    /// standard order two trees are compared in (`matching::standard`);
    /// None where it does not read.
    pub fn read_citing(&self, text: &str, defined: &Definitions) -> Option<Node> {
        self.read_as_written(text)
            .map(|n| standard(&expand(&n, defined), self.ctx))
    }

    /// A tree as page text.
    pub fn print(&self, node: &Node) -> String {
        self.env.g.print(node)
    }

    /// What the lines `refs` name at `step` say, each sentence read, and
    /// each part of one that is a conjunction (`with_parts`).
    pub fn lines_say(
        &self,
        step: &Step,
        refs: &[&str],
        library: &Library,
    ) -> Vec<Node> {
        let scope = self.scope(step);
        let said: Vec<Node> = refs
            .iter()
            .filter_map(|r| scope.get(*r))
            .flat_map(|text| sentences(text))
            .filter_map(|s| self.read(step, &s))
            .collect();
        with_parts(&said, library)
    }

    /// Every line a step's citation may name, by the reference that names
    /// it.
    pub fn scope(&self, step: &Step) -> Rc<IndexMap<String, String>> {
        let key = (step.number.clone(), step.line);
        if let Some(found) = self.scopes.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(statements_in_scope(self.thm, step, self.env));
        self.scopes.borrow_mut().insert(key, made.clone());
        made
    }

    /// What a step's justification supplies and claims.
    pub fn parts(&self, step: &Step, library: &Library) -> Rc<Parts> {
        let key = (
            step.number.clone(),
            step.just.refs.clone(),
            step.requires.iter().map(|r| r.fact.clone()).collect(),
        );
        if let Some(found) = self.parts.borrow().get(&key) {
            return found.clone();
        }
        let made = Rc::new(citation_parts(step, library, self));
        self.parts.borrow_mut().insert(key, made.clone());
        made
    }
}

/// Every line a step's citation may name, by the reference that names it.
///
/// A block's label holds inside that block only, so two sibling blocks may
/// each fix a k under the same label, and what the label says is what the
/// block around the citing step says.
fn statements_in_scope(
    thm: &Theorem,
    step: &Step,
    env: Env,
) -> IndexMap<String, String> {
    let said = said_by_line;
    let mut out: IndexMap<String, String> = thm
        .steps
        .iter()
        .map(|s| (s.number.to_string(), s.claim_text()))
        .collect();
    for h in &thm.hypotheses {
        if let Some(label) = &h.label {
            out.insert(label.clone(), said(h.kind, &h.text));
        }
    }
    let visible = labels_in_scope(thm, step, env.scopes);
    for other in &thm.steps {
        for o in &other.openers {
            if visible.get(&o.label) == Some(&Declared::Block(o.line)) {
                out.insert(o.label.clone(), said(o.kind, &o.text));
            }
        }
    }
    out
}

/// What a citation supplies, what it claims, and what it says its variables
/// stand for.
///
/// A defined name and the term it names are one formula where the step cites
/// the define, so all three are expanded with what it cites
/// (`Known::citing`): the facts, the claim, and the written instantiation
/// alike.
fn citation_parts(step: &Step, library: &Library, known: &Known) -> Parts {
    let scope = known.scope(step);
    let defined = known.citing(&step.just.refs);
    let read = |s: &str| known.read_citing(s, &defined);
    let mut supplied: Vec<String> = Vec::new();
    for r in &step.just.refs {
        if let Some(text) = scope.get(r) {
            supplied.extend(sentences(text));
        }
    }
    supplied.extend(step.requires.iter().map(|r| r.fact.clone()));
    let facts: Vec<Node> = supplied.iter().filter_map(|s| read(s)).collect();
    let claims: Vec<Node> = sentences(&step.claim_text())
        .iter()
        .filter_map(|s| read(s))
        .collect();
    let mut seed = Binding::new();
    for (name, value) in instantiation(&step.just.text) {
        if let Some(got) = read(&value) {
            seed.insert(name, got);
        }
    }
    match at_a_member(step, &claims, library, &known.sorts) {
        Some((member, body)) => {
            let mut facts = facts;
            facts.push(member);
            finished(facts, vec![body], seed, library, &known.sorts)
        }
        None => finished(facts, claims, seed, library, &known.sorts),
    }
}

/// A claim "for all k ∈ X, P" read at a member: the membership k ∈ X, which
/// the step then has as a fact, and P, which it then claims (`SYNTAX.md`, a
/// step said of every member). Which reading a citation takes is read off the
/// item, not tried: an item whose conclusions say no "for all" anywhere is
/// applied at a member, and one whose conclusions say one, as `upper-bound`
/// unfolds to one, is read as written. A define says one equation, and is
/// read at a member.
fn at_a_member(
    step: &Step,
    claims: &[Node],
    library: &Library,
    sorts: &Sorts,
) -> Option<(Node, Node)> {
    let [claim] = claims else {
        return None;
    };
    let just = &step.just;
    // A define says what its name is equal to, never a "for all", so a
    // step citing one for a "for all" is read at a member.
    if just.head != crate::corpus::Head::Define {
        if !just.head.is_item() {
            return None;
        }
        let item = library.item(&just.item(&just.head.to_string()))?;
        if item.says_for_all() {
            return None;
        }
    }
    claimed_member(claim, library, sorts)
}
