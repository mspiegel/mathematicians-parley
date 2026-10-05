//! What each theorem's lines give the checks that read them.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::IndexMap;

use super::structure::{labels_in_scope, Declared};
use crate::citing::{claimed_member, finished, with_parts, Library, Parts};
use crate::corpus::{Intro, Step, StepNo, Theorem};
use crate::formula::{parse_here, Node, Sorts};
use crate::matching::{expand, instantiation, Binding, Definitions};
use crate::sorts::{definitions_in_scope, let_formula, sentences, unlabel, Env};

type PartsKey = (StepNo, Vec<String>, Vec<String>);

/// Every line a step's citation may name, by the reference that names it.
pub type Statements = IndexMap<String, String>;

/// What a theorem's lines give every check of it, read once a run.
///
/// The sort of each name and what each `define` stands for depend on the
/// theorem alone, the lines a citation may name on its step, and what a
/// step's citation supplies on the step. Each is read the first time a check
/// asks and kept for the run; nothing that uses them changes them.
///
/// What a step's citation supplies is kept by what it depends on — the
/// step, the lines it names and its requires lines — so that a step with a
/// line taken away, as `check_surplus` asks about, is read afresh.
pub struct Known<'a> {
    pub thm: &'a Theorem,
    pub env: Env<'a>,
    pub sorts: Sorts,
    pub defined: Definitions,
    scopes: RefCell<IndexMap<(StepNo, usize), Rc<Statements>>>,
    parts: RefCell<IndexMap<PartsKey, Rc<Parts>>>,
}

impl<'a> Known<'a> {
    /// `sorts` is what the theorem's one reading settled (`check::run`).
    pub fn new(thm: &'a Theorem, env: Env<'a>, sorts: Sorts) -> Known<'a> {
        let defined = definitions_in_scope(thm, env, &sorts);
        Known {
            thm,
            env,
            sorts,
            defined,
            scopes: RefCell::new(IndexMap::new()),
            parts: RefCell::new(IndexMap::new()),
        }
    }

    /// A sentence as the theorem's checks compare it: parsed with its sorts,
    /// each defined name written out; None where it does not read, which
    /// `check_formulas` reports.
    pub fn read(&self, text: &str) -> Option<Node> {
        self.read_as_written(text)
            .map(|n| expand(&n, &self.defined))
    }

    /// The text read with its defined names kept, as a message prints it.
    pub fn read_as_written(&self, text: &str) -> Option<Node> {
        parse_here(text, self.env.g, &self.sorts).ok()
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
            .filter_map(|s| self.read(&s))
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
    fn said(kind: Intro, text: &str) -> String {
        let body = str::trim(&unlabel(&text[kind.as_str().len()..])).to_string();
        if kind == Intro::Let {
            let_formula(&body)
        } else {
            body
        }
    }
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
/// A defined name and the term it names are one formula, so all three are
/// expanded: the facts, the claim, and the written instantiation alike.
fn citation_parts(step: &Step, library: &Library, known: &Known) -> Parts {
    let scope = known.scope(step);
    let mut supplied: Vec<String> = Vec::new();
    for r in &step.just.refs {
        if let Some(text) = scope.get(r) {
            supplied.extend(sentences(text));
        }
    }
    supplied.extend(step.requires.iter().map(|r| r.fact.clone()));
    let facts: Vec<Node> = supplied.iter().filter_map(|s| known.read(s)).collect();
    let claims: Vec<Node> = sentences(&step.claim_text())
        .iter()
        .filter_map(|s| known.read(s))
        .collect();
    let mut seed = Binding::new();
    for (name, value) in instantiation(&step.just.text) {
        if let Some(got) = known.read(&value) {
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
