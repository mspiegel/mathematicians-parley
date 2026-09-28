//! What each item asks a citation to supply, and what each theorem's lines
//! give the checks that read them.

use std::cell::RefCell;
use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::structure::{labels_in_scope, Declared};
use crate::corpus::{Intro, Record, RecordKind, Step, StepNo, Theorem};
use crate::formula::{parse_here, Node, Sort, Sorts};
use crate::matching::{
    expand, instantiation, substitute, Binding, Context, Definitions,
};
use crate::regex;
use crate::rules;
use crate::sorts::{
    definitions_in_scope, element_re, file_definitions, function_being_re, function_re,
    group_re, let_formula, part_re, sentences, set_or_point_re, unlabel, Env,
};

/// One `then` group of an item: its facts, each with the text it was read
/// from, and the sentences it concludes.
pub type Group = (Vec<(String, Node)>, Vec<Node>);

/// What each item asks a citation to supply.
///
/// Only the hypotheses that are facts. `let X be a set`, `let P be a point`
/// and a function type declare a variable and are filled by the
/// instantiation, which is what Metamath calls a floating hypothesis; a
/// membership and an `assume` are essential and a step citing the item has
/// to supply them.
///
/// A record with two `then` groups states each conclusion under the
/// hypotheses written above it, so the groups are kept apart and a citation
/// satisfies any one of them. Items are asked for by their full name.
pub struct Library<'a> {
    pub env: Env<'a>,
    records: &'a [Record],
    record_sorts: &'a IndexMap<usize, Sorts>,
    items: IndexMap<String, usize>,
    proved: IndexMap<String, &'a Known<'a>>,
    cache: RefCell<IndexMap<String, Option<Rc<Vec<Group>>>>>,
    /// Which notations are an existential, a membership, a conjunction, a
    /// biconditional and an implication, taken from what they target in the
    /// kernel rather than named here.
    pub exists: IndexSet<String>,
    pub members: IndexSet<String>,
    pub conj: IndexSet<String>,
    pub bicond: IndexSet<String>,
    pub implies: IndexSet<String>,
    pub ctx: Context,
}

regex!(FIRST_WORD, r"^[a-z0-9-]+");

impl<'a> Library<'a> {
    pub fn new(
        records: &'a [Record],
        record_sorts: &'a IndexMap<usize, Sorts>,
        known: &'a [Known<'a>],
        env: Env<'a>,
    ) -> Library<'a> {
        let mut items = IndexMap::new();
        for (i, r) in records.iter().enumerate() {
            if r.kind.is_item() {
                items.insert(r.qualified(), i);
            }
        }
        let mut proved = IndexMap::new();
        for k in known {
            proved.insert(k.thm.qualified(), k);
        }
        let mut lib = Library {
            env,
            records,
            record_sorts,
            items,
            proved,
            cache: RefCell::new(IndexMap::new()),
            exists: IndexSet::new(),
            members: IndexSet::new(),
            conj: IndexSet::new(),
            bicond: IndexSet::new(),
            implies: IndexSet::new(),
            ctx: Context::new(&env.g.notations, records),
        };
        // A metamath field may say more after the target, as "wrex, and wrex
        // under wn" does, so the target is its first word.
        for r in records {
            if r.kind != RecordKind::Notation {
                continue;
            }
            let Some(first) = FIRST_WORD.find(str::trim(r.field_or_empty("metamath")))
            else {
                continue;
            };
            let set = match first.as_str() {
                "wrex" => &mut lib.exists,
                "wcel" => &mut lib.members,
                "wa" => &mut lib.conj,
                "wb" => &mut lib.bicond,
                "wi" => &mut lib.implies,
                _ => continue,
            };
            set.insert(r.name.clone());
        }
        lib
    }

    /// The groups of the item of that full name, or None where no item has
    /// it.
    pub fn groups(&self, name: &str) -> Option<Rc<Vec<Group>>> {
        if let Some(found) = self.cache.borrow().get(name) {
            return found.clone();
        }
        let found = self.read(name).map(Rc::new);
        self.cache
            .borrow_mut()
            .insert(name.to_string(), found.clone());
        found
    }

    /// One (hypotheses, conclusion sentences) pair per `then` group.
    fn read(&self, name: &str) -> Option<Vec<Group>> {
        if let Some(k) = self.proved.get(name) {
            let thm = k.thm;
            let lines: Vec<(Intro, String)> = thm
                .hypotheses
                .iter()
                .map(|h| {
                    let rest = &h.text[h.kind.as_str().len()..];
                    (h.kind, str::trim(&unlabel(rest)).to_string())
                })
                .collect();
            // A theorem's statement means what it meant in its own file: a
            // definition it names is written out there, so what cites it is
            // compared with the rule and never with a name of its own.
            let own = file_definitions(thm, self.env);
            let facts = self
                .facts(&lines, &k.sorts)
                .into_iter()
                .map(|(text, tree)| (text, expand(&tree, &own)))
                .collect();
            let gives = self
                .trees(&sentences(&thm.conclusion), &k.sorts)
                .iter()
                .map(|t| expand(t, &own))
                .collect();
            return Some(vec![(facts, gives)]);
        }
        let &i = self.items.get(name)?;
        let item = &self.records[i];
        let sorts = &self.record_sorts[&i];
        let mut out = Vec::new();
        for (text, at) in &item.conclusions {
            let lines: Vec<(Intro, String)> = item
                .hypotheses
                .iter()
                .filter(|h| h.line < *at)
                .map(|h| (h.kind, str::trim(&unlabel(&h.text)).to_string()))
                .collect();
            out.push((
                self.facts(&lines, sorts),
                self.trees(&sentences(text), sorts),
            ));
        }
        if out.is_empty() {
            out.push((Vec::new(), Vec::new()));
        }
        Some(out)
    }

    fn trees(&self, texts: &[String], sorts: &Sorts) -> Vec<Node> {
        texts
            .iter()
            .filter_map(|t| parse_here(t, self.env.g, sorts).ok())
            .collect()
    }

    fn facts(&self, lines: &[(Intro, String)], sorts: &Sorts) -> Vec<(String, Node)> {
        let mut out = Vec::new();
        for (kind, text) in lines {
            let mut text = text.clone();
            // A function's type is declared, and what `be` says of the
            // function is a fact like any other, asked for as `let y ∈ Y`
            // is: `let g : Y → X be one-to-one` asks that g be one-to-one.
            if *kind == Intro::Let
                && (function_being_re().is_match(&text) || part_re().is_match(&text))
            {
                text = let_formula(&text);
            } else if *kind == Intro::Let
                && (set_or_point_re().is_match(&text)
                    || function_re().is_match(&text)
                    || element_re().is_match(&text)
                    || group_re().is_match(&text))
            {
                continue;
            }
            if let Ok(tree) = parse_here(&text, self.env.g, sorts) {
                out.push((text, tree));
            }
        }
        out
    }
}

/// What a citation supplies, what it claims, and what it says its variables
/// stand for.
pub struct Parts {
    pub facts: Vec<Node>,
    pub claims: Vec<Node>,
    pub seed: Binding,
}

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
        parse_here(text, self.env.g, &self.sorts)
            .ok()
            .map(|n| expand(&n, &self.defined))
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
    let g = library.env.g;
    let scope = known.scope(step);
    let mut supplied: Vec<String> = Vec::new();
    for r in &step.just.refs {
        if let Some(text) = scope.get(r) {
            supplied.extend(sentences(text));
        }
    }
    supplied.extend(step.requires.iter().map(|r| r.fact.clone()));
    let mut facts: Vec<Node> = supplied.iter().filter_map(|s| known.read(s)).collect();
    // A defined function standing alone stays its name, so an item whose
    // function letter the claim fills with it (`h : A → B` from every h(s)
    // lying in B) asks for h(s) as written, which the expanded fact no
    // longer says. The fact is offered as written too.
    for text in &supplied {
        let Ok(written) = parse_here(text, g, &known.sorts) else {
            continue;
        };
        if facts.iter().all(|x| written.shape() != x.shape()) {
            facts.push(written);
        }
    }
    let mut facts = with_parts(&facts, library);
    let implied: Vec<Node> = facts
        .iter()
        .flat_map(|f| implied_facts(f, library.env, &known.sorts))
        .collect();
    facts.extend(implied);
    let claims = sentences(&step.claim_text())
        .iter()
        .filter_map(|s| known.read(s))
        .collect();
    let mut seed = Binding::new();
    for (name, value) in instantiation(&step.just.text) {
        if let Some(got) = known.read(&value) {
            seed.insert(name, got);
        }
    }
    Parts {
        facts,
        claims,
        seed,
    }
}

/// The facts, and each part of one that is a conjunction.
///
/// A line of two sentences supplies each, since a claim of several sentences
/// is their conjunction; a line saying `P and Q` is that same conjunction
/// written as one formula, and supplies each part the same way.
pub fn with_parts(facts: &[Node], library: &Library) -> Vec<Node> {
    let mut out: Vec<Node> = facts.to_vec();
    for fact in facts {
        for part in conjuncts(fact, library) {
            if out.iter().all(|x| part.shape() != x.shape()) {
                out.push(part);
            }
        }
    }
    out
}

/// A conjunction taken apart. A claim may take one part of what it gets,
/// and a fact may supply one part of what is asked, because a line is a
/// conjunction at kernel level either way and the projection lives in the
/// method's expansion.
pub fn conjuncts(node: &Node, library: &Library) -> Vec<Node> {
    if library.conj.contains(&node.notation) && node.children.len() == 2 {
        let mut out = conjuncts(&node.children[0], library);
        out.extend(conjuncts(&node.children[1], library));
        return out;
    }
    vec![node.clone()]
}

/// (what a step may claim, what a fact must state first), for one sentence
/// of an item's conclusion.
///
/// `SYNTAX.md` gives the moves: a sentence may be claimed as it stands;
/// where it is "A ↔ B" and a fact states A the step may claim B, and the
/// other way round; where it is "if A then B" and a fact states A the step
/// may claim B.
pub fn readings(node: &Node, library: &Library) -> Vec<(Node, Vec<Node>)> {
    let mut out = vec![(node.clone(), Vec::new())];
    if node.children.len() == 2 {
        let (left, right) = (&node.children[0], &node.children[1]);
        if library.bicond.contains(&node.notation) {
            out.push((right.clone(), vec![left.clone()]));
            out.push((left.clone(), vec![right.clone()]));
        } else if library.implies.contains(&node.notation) {
            out.push((right.clone(), vec![left.clone()]));
        }
    }
    out
}

fn template(said: &str, env: Env, sorts: &Sorts) -> Node {
    parse_here(said, env.g, sorts).unwrap_or_else(|p| {
        panic!("the notation database no longer reads {said:?}, which a membership implies: {p}")
    })
}

/// What a membership fact also says, by the table in `rules`.
///
/// `k ∈ ℕ` also says k ∈ ℤ, k ∈ ℝ and the rest, and k ≥ 1 and k ≠ 0
/// (`SYNTAX.md`, what a membership line says). A part of a set is a member
/// of its power set and the other way round, so `C ⊆ A` also says C ∈ 𝒫A,
/// which is what `for every X ⊆ A` ranges over. Anything else says only
/// itself.
pub fn implied_facts(fact: &Node, env: Env, sorts: &Sorts) -> Vec<Node> {
    let both = fact.children.len() == 2;
    if both
        && (fact.notation == "subset"
            || (fact.notation == "membership"
                && fact.children[1].notation == "powerset"))
    {
        let part = fact.children[0].clone();
        let whole = if fact.notation == "membership" {
            fact.children[1].children[0].clone()
        } else {
            fact.children[1].clone()
        };
        let mut local = sorts.clone();
        local.insert("x".into(), Sort::of("set"));
        local.insert("S".into(), Sort::of("set"));
        let said = if fact.notation == "subset" {
            "x ∈ 𝒫S"
        } else {
            "x ⊆ S"
        };
        let mut put = Binding::new();
        put.insert("x".into(), part);
        put.insert("S".into(), whole);
        return vec![substitute(&template(said, env, &local), &put)];
    }
    if fact.notation != "membership"
        || !both
        || fact.children[1].notation != "number-systems"
    {
        return Vec::new();
    }
    let term = fact.children[0].clone();
    let system = rules::system_of(&fact.children[1].text);
    // ℂ has no symbol on the page, so nothing a page writes asks for it.
    let mut templates: Vec<String> = rules::SYSTEM_OF
        .iter()
        .filter(|(_, label)| *label != "cc")
        .filter(|(_, big)| {
            Some(*big) != system && rules::within_path(system, Some(big)).is_some()
        })
        .map(|(sign, _)| format!("x ∈ {sign}"))
        .collect();
    templates.extend(
        rules::implied(system)
            .iter()
            .map(|(said, _)| said.to_string()),
    );
    let mut local = sorts.clone();
    local.insert("x".into(), Sort::of("number"));
    let mut put = Binding::new();
    put.insert("x".into(), term);
    templates
        .iter()
        .map(|t| substitute(&template(t, env, &local), &put))
        .collect()
}
