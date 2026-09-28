//! Turn a readable proof into a Metamath proof.
//!
//! `ELABORATION.md` lists what the expansion language has to have. `obtain`,
//! `contradiction`, `fix` and `induction` open scopes; `substitute`,
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

use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::provenance::item_clauses;
use super::reading::{hypothesis_body, is_subgroup, subject_of, CLASS_NAMES};
use super::state::{
    fit, names_of, number_of, Binding, Block, Closer, Elaborator, Vars,
};
use super::tables::Leaf;
use super::{Facts, Line, Lines};
use crate::binds;
use crate::corpus::{
    define_parts, fmt, outermost, Corpus, DefineParts, Intro, Item, Record, Step,
    Theorem,
};
use crate::formula::{Grammar, Node};
use crate::matching::{
    instantiation, match_tree, Binding as NodeBinding, Context, Defined,
};
use crate::mm::compress::{compressed, labels as compress_labels, shapes_of};
use crate::mm::kernel::Term;
use crate::mm::library::thousands;
use crate::mm::spell::Proof;
use crate::mm::{Kind, Layered, Lookup, Signature, Signatures};
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules::{self, lookup};
use crate::sorts::{file_definitions, sorts_in_scope, unlabel};
use crate::targets;
use crate::text::repr;
use crate::{pf, regex, t, take};

/// Why a side of a step citing a define is not what the define names.
const NAMES_NO_DEFINE: &str = "this side names no define";

regex!(
    SUBSTITUTE,
    r"^substitute\s+(.*)\s*\(([^()]*)\)(?:\s+into\s+(\S.*?))?\s*$"
);

/// Where a class that binds a name keeps it among its parts: a map and an
/// indexed union first, a set built from a property second, a sum third.
fn binder_at(label: &str) -> Option<usize> {
    match label {
        "cmpt" | "ciun" => Some(0),
        "crab" => Some(1),
        "csu" => Some(2),
        _ => None,
    }
}

/// Which of the three ways a biconditional definition reaches a claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Way {
    /// It concludes an existence claim from a witness.
    Conclude,
    /// Its right side is what the step holds, read right to left.
    Equivalent,
    /// Its left side is what the step holds, unfolded and taken apart.
    Unfolded,
}

/// What this elaborator calls a theorem it has written out.
///
/// set.mm proves some of what this corpus proves and has its own names for
/// them, so the label is moved off any that is already in use. The corpus's
/// own theorems can share a stem as well, so `ours`, the full names of every
/// theorem the corpus proves, are given labels one at a time in order of
/// full name, each moved off what set.mm and the ones before it hold. Which
/// label a theorem lands on then depends only on set.mm and the corpus.
pub fn label_of(
    name: &str,
    taken: &dyn Lookup,
    path: &str,
    line: usize,
    ours: &BTreeSet<String>,
) -> Checked<String> {
    let mut all = ours.clone();
    all.insert(name.to_string());
    let mut given: IndexMap<String, String> = IndexMap::new();
    for one in &all {
        let last = one.rsplit('/').next().unwrap_or(one);
        let stem: String = last.replace('-', "").chars().take(8).collect();
        let head: String = stem.chars().take(7).collect();
        let held: BTreeSet<&String> = given.values().collect();
        let mut candidates = vec![stem.clone()];
        candidates.extend((1..10).map(|d| format!("{head}{d}")));
        let free = candidates
            .into_iter()
            .find(|s| !taken.contains_key(s) && !held.contains(s));
        let Some(free) = free else {
            return Err(Problem::new(
                path,
                line,
                format!("no free label near {}", repr(&stem)),
            ));
        };
        given.insert(one.clone(), free);
    }
    Ok(given[name].clone())
}

/// The full names of the theorems this corpus proves.
pub fn proved_here(items: &IndexMap<String, Item>) -> BTreeSet<String> {
    items
        .iter()
        .filter(|(_, item)| item.proved())
        .map(|(name, _)| name.clone())
        .collect()
}

/// An item's full name: its file's module, then its own name.
fn qualified(item: Item) -> String {
    match item {
        Item::Record(r) => r.qualified(),
        Item::Theorem(t) => t.qualified(),
    }
}

fn item_kind(item: Item) -> &'static str {
    if item.kind() == "definition" {
        "def"
    } else {
        "thm"
    }
}

impl<'a> Elaborator<'a> {
    /// The biconditional a definition's lemma gives, in scope, and the right
    /// side it reached. `ex` is the wording the step wants; None takes
    /// whatever the lemma says.
    ///
    /// Which of the lemma's variables the readable left side fills, and what
    /// the lemma then asks for, are read off its statement rather than
    /// assumed of it.
    #[allow(clippy::too_many_arguments)]
    pub fn unfolding(
        &mut self,
        step: &Step,
        lemma: &str,
        left: &str,
        ex: Option<&str>,
        var: Option<&str>,
        over: Option<&str>,
        scope: &str,
        facts: &Facts,
        hint: Option<&str>,
    ) -> Checked<Route<(Proof, String)>> {
        let _ = over;
        let sig = self.sig(lemma).clone();
        let whole = self.statement(lemma);
        let variables = names_of(&whole);
        let mut asks = Vec::new();
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            asks.push(reads.children()[0].clone());
            reads = reads.children()[1].clone();
        }
        if reads.label() != Some("wb") {
            return Ok(Route::no(format!("{lemma} states no biconditional")));
        }
        let Some(mut binding) = fit(
            &reads.children()[0],
            &self.to_term(left),
            &Binding::new(),
            &variables,
        ) else {
            return Ok(self.no(format!("{lemma} does not unfold {{}}"), &[left]));
        };
        // A lemma in deduction form assumes a formula it says nothing else
        // about, and that formula is the step's scope.
        let deduced = match asks.first().and_then(|a| a.variable().map(String::from)) {
            Some(v) => {
                binding.insert(v, self.to_term(scope));
                asks.remove(0);
                true
            }
            None => false,
        };
        // A lemma's left side need not fix everything it mentions, so what
        // the caller can say of the right side fixes the rest.
        if let Some(offered) = hint.or(ex) {
            if let Some(filled) = fit(
                &reads.children()[1],
                &self.to_term(offered),
                &binding,
                &variables,
            ) {
                binding = filled;
            }
        }
        // A slot neither side fixes is set.mm asking where to look for the
        // thing, and _V holds everything that is a set; a fixed function's
        // type is read off the line saying it.
        let keys = facts.keys();
        for slot in &asks {
            for piece in super::matcher::conjuncts_of(slot) {
                if !function_fixed(&piece, &binding) {
                    continue;
                }
                for held in &keys {
                    if let Some(filled) =
                        fit(&piece, &self.to_term(held), &binding, &variables)
                    {
                        if !filled.is_empty() {
                            binding = filled;
                            break;
                        }
                    }
                }
            }
            for open in slot.names().iter() {
                if !binding.contains_key(&**open) {
                    binding.insert(open.to_string(), Term::apply("cvv", Vec::new()));
                }
            }
        }
        let mut binding = self.instanced(&sig, binding);
        // A definition that introduces a name says which variable it takes;
        // one that does not leaves the lemma's own, which the match fixed.
        let mut binds = self.spelt(&binding);
        let mut held = sig.bound().map(String::from);
        if let Some(h) = &held {
            if reads.children()[0].names().iter().any(|n| **n == **h) {
                held = None;
            }
        }
        if let (Some(v), Some(h)) = (var, &held) {
            binds.insert(h.clone(), v.to_string());
        }
        // A lemma may state a condition in full rather than ask for it, and
        // both are settled against the binding as the match left it.
        let mut conditions = Vec::new();
        for e in &sig.essentials {
            let asked = self.essential(e).substitute(&binding);
            conditions.push(self.prove_essential(&asked, scope, facts)?);
        }
        let mut proofs = Vec::new();
        for one in conditions {
            proofs.push(take!(one));
        }
        let applied = self.b.ap(lemma, &binds, &proofs.iter().collect::<Vec<_>>());
        // The lemma unfolds to its own wording, which need not be the
        // text's: what it gives is built first, and the text's wording is
        // reached from it.
        if let (Some(h), Some(v)) = (&held, var) {
            let var_term = self.var_of(v);
            binding.insert(h.clone(), var_term);
        }
        let given = self.rpn(&reads.children()[1].substitute(&binding));
        let says = t!(left, given, "wb");
        let proof = if deduced && asks.is_empty() {
            applied
        } else if asks.is_empty() {
            pf!(self.b; says, scope, applied, "a1i")
        } else {
            let mut holds = self.rpn(&asks[0].substitute(&binding));
            let mut proof = self.required(step, &holds, scope, facts)?;
            for slot in &asks[1..] {
                let extra = self.rpn(&slot.substitute(&binding));
                let more = self.required(step, &extra, scope, facts)?;
                proof = pf!(self.b; scope, holds, extra, proof, more, "jca");
                holds = t!(holds, extra, "wa");
            }
            pf!(self.b; scope, holds, says, proof, applied, "syl")
        };
        let Some(ex) = ex.filter(|ex| **ex != given) else {
            return Ok(Built((proof, given)));
        };
        // No bridge means the lemma unfolds to a wording this step cannot be
        // reached from, which is this route not applying.
        let across = take!(self.bridging(
            &self.to_term(&given),
            &self.to_term(ex),
            scope,
            facts,
            Some(step)
        )?);
        Ok(Built((
            pf!(self.b; scope, left, given, ex, proof, across, "bitrd"),
            ex.to_string(),
        )))
    }

    // --- the proof ------------------------------------------------------

    /// The theorem elaborated: its conclusion, its hypotheses, and the proof
    /// of the one from the other.
    pub fn run(&mut self) -> Checked<(String, Vec<String>, Proof)> {
        // The statement is read with the definitions the theorem sees from
        // outside it written out, which is what set.mm states.
        self.from_outside = file_definitions(self.thm, self.env());
        let nodes = self.hypotheses()?;
        // A sort is stated once, like a declared type, and a step may rest on
        // it without naming it. So may a define.
        let mut sorts: BTreeSet<String> = BTreeSet::new();
        let mut lets: Vec<(Intro, String, String)> = self
            .thm
            .hypotheses
            .iter()
            .map(|h| (h.kind, h.text.clone(), h.label.clone().unwrap_or_default()))
            .collect();
        for s in &self.thm.steps {
            for o in &s.openers {
                lets.push((o.kind, o.text.clone(), o.label.clone()));
            }
        }
        for (kind, text, label) in &lets {
            if *kind == Intro::Let
                && !label.is_empty()
                && (text.contains(" be a set")
                    || text.contains(" be a point")
                    || text.contains('→')
                    || text.contains(" group with operation "))
            {
                sorts.insert(label.clone());
            }
        }
        for (kind, text, label) in &lets {
            if *kind == Intro::Assume
                && !label.is_empty()
                && is_subgroup(str::trim(&unlabel(&hypothesis_body(
                    kind.as_str(),
                    text,
                ))))
            {
                sorts.insert(label.clone());
            }
        }
        for d in &self.thm.defines {
            sorts.insert(d.label.clone());
        }
        for (name, d, src) in self.visible_outside() {
            sorts.insert(self.outside_label(&name, &d, src));
        }
        self.sorts = sorts;
        let mut terms = Vec::new();
        for n in &nodes {
            terms.push(self.term(n)?);
        }
        // A theorem may assume nothing, and every step here is still an
        // implication out of the scope it sits in: the scope is truth,
        // discharged once at the end.
        let mut scope = terms.first().cloned().unwrap_or_else(|| "wtru".to_string());
        let mut facts = Facts::new();
        facts.set(scope.clone(), pf!(self.b; scope, "id"));
        for extra in terms.iter().skip(1) {
            let wider = t!(scope, extra, "wa");
            let weaken = pf!(self.b; scope, extra, "simpl");
            let lifted = Facts::new();
            for (k, v) in facts.entries() {
                lifted.set(k.clone(), pf!(self.b; wider, scope, k, weaken, v, "syl"));
            }
            lifted.set(extra.clone(), pf!(self.b; scope, extra, "simpr"));
            facts = lifted;
            scope = wider;
        }
        // Each hypothesis stands for itself, and is sealed before it is taken
        // apart so that what it says in pieces is still what it says.
        let hypotheses = self.thm.hypotheses.clone();
        for (h, t) in hypotheses.iter().zip(&terms) {
            if let (Some(label), Some(held)) =
                (h.label.clone().filter(|l| !l.is_empty()), facts.get(t))
            {
                let sealed = self.seal(held, &label);
                facts.set(t.clone(), sealed);
            }
        }
        // A hypothesis may say several things at once, and each of them is a
        // fact the proof may lean on without a step to take it apart.
        for extra in &terms {
            if let Some(held) = facts.get(extra) {
                self.unpack(extra, &held, &scope, &facts, 4);
            }
        }
        let more = self.sethoods(&nodes, &terms, &scope, &facts);
        self.sorts.extend(more);

        // Each keeps the sentence it was read from, as a block's opening
        // line does, so a step may substitute into it.
        let lines = Lines::new();
        for ((h, t), node) in hypotheses.iter().zip(&terms).zip(&nodes) {
            lines.set(
                h.label.clone().unwrap_or_default(),
                Line {
                    term: t.clone(),
                    proof: facts.get(t).expect("a hypothesis's fact"),
                    sentences: vec![node.clone()],
                },
            );
        }
        // A define by recursion in the statement is stated written out, as a
        // definition from outside is.
        let first = self.thm.steps.first().map(|s| s.line);
        for d in self.thm.defines.clone() {
            let Built(DefineParts::Recursion(given)) = define_parts(&d.text) else {
                continue;
            };
            if first.is_some_and(|f| d.line >= f) {
                continue;
            }
            for (name, made) in self.recursion_terms(&d.label, &given)? {
                self.from_outside
                    .insert(name, Defined::Term(Node::literal(&made)));
            }
        }
        let goal = self.claim_of(&self.thm.conclusion)?;
        self.from_outside = IndexMap::new();
        // What the conclusion quantifies over is spoken for before anything
        // else takes a variable.
        self.reserved = goal
            .split_whitespace()
            .filter(|t| {
                self.b
                    .sigs
                    .get(t)
                    .is_some_and(|s| s.statement[0] == "setvar")
            })
            .map(String::from)
            .collect();
        self.rules_read = IndexMap::new();
        self.open_outermost(&scope, &facts);
        self.lines = lines;
        let mut closers: Vec<Closer> = Vec::new();
        let mut blocks: Vec<Block> = Vec::new();
        for step in self.thm.steps.clone() {
            // A block's children are the steps numbered below it, so the
            // block closes at the first step that is not one of them.
            while blocks
                .last()
                .is_some_and(|b| step.number.len() <= b.owner.number.len())
            {
                let mut done = blocks.pop().unwrap();
                (scope, facts, closers) =
                    self.close_block(&mut done, &facts, closers, &scope)?;
                Self::hand_up(&done, &mut blocks);
            }
            // Any define standing above this step, now that the block it
            // sits in is open and the names it leans on are in hand.
            (scope, facts, closers) =
                self.define(step.line, &scope, &facts, closers)?;
            // A step in a case sits under the case's assumption, where the
            // part is new.
            let entering = match (blocks.last(), step.part) {
                (Some(b), Some(part)) => {
                    !b.assumed.is_empty() && b.entered != Some(part)
                }
                _ => false,
            };
            if entering {
                let mut block = blocks.pop().unwrap();
                closers = self.end_case(&mut block, closers)?;
                (scope, facts) = self.enter_case(&mut block, step.part.unwrap())?;
                block.case_opened_at = Some(closers.len());
                blocks.push(block);
            }
            if !step.openers.is_empty() || !step.parts.is_empty() {
                let mut block = self.open_block(&step, &scope, &facts)?;
                block.opened_at = closers.len();
                scope = block.scope.clone();
                facts = block.facts.clone();
                blocks.push(block);
                continue;
            }
            self.in_contradiction = blocks
                .last()
                .is_some_and(|b| b.owner.just.head.to_string() == "contradiction");
            (scope, facts, closers) = self.take_step(&step, &scope, &facts, closers)?;
            if let (Some(part), Some(block)) = (step.part, blocks.last_mut()) {
                let last = self.last.clone().expect("a step's number");
                let held = self.lines.get(&last).expect("the step's line");
                block
                    .parts
                    .insert(part, (held.term, held.proof, scope.clone()));
            }
        }
        while let Some(mut done) = blocks.pop() {
            (scope, facts, closers) =
                self.close_block(&mut done, &facts, closers, &scope)?;
            Self::hand_up(&done, &mut blocks);
        }

        let last = self.last.clone().expect("a proof of one step at least");
        let held = self.lines.get(&last).expect("the last line");
        let mut proof = held.proof;
        // The last line says it with the names, the statement with what they
        // name; the standard form reads the two as one.
        let said = held.term;
        if said != goal {
            let alike = self.same(
                &self.to_term(&said),
                &self.to_term(&goal),
                &scope,
                &facts,
                None,
            )?;
            let alike = match alike {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        self.thm.line,
                        format!(
                            "the last step does not say what the theorem states: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
            proof = pf!(self.b; scope, said, goal, proof, alike, "mpbid");
        }
        for close in closers.iter().rev() {
            proof = self.close(close, proof, &goal)?;
        }
        let unproved = self.unproved_requires();
        if let Some(first) = unproved.first() {
            let all: Vec<String> = unproved.iter().map(|n| n.to_string()).collect();
            return Err(self.defect(
                *first,
                format!(
                    "the requires lines at {} were never proved from their reasons",
                    all.join(", ")
                ),
            ));
        }
        Ok((goal, terms, proof))
    }

    /// One step, with the search offered only what the step names.
    fn take_step(
        &mut self,
        step: &Step,
        scope: &str,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        let number = number_of(step);
        let named = self.named(step, &number, false);
        self.resting_on(Some(named), |me| {
            me.one_step(step, &number, scope, facts, closers)
        })
    }

    fn one_step(
        &mut self,
        step: &Step,
        number: &str,
        scope: &str,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        let head = step.just.head.to_string();
        self.last = Some(number.to_string());
        self.at = step.line;
        if head == "obtain" {
            return self.obtain(step, number, scope, facts, closers);
        }
        let claim = step.claim_text();
        let sentences = self.sentences(&claim);
        let node = self.read(sentences.last().map(String::as_str).unwrap_or(""))?;
        let term = self.claim_of(&claim)?;
        let known_methods = [
            "algebra",
            "arithmetic",
            "inequalities",
            "membership",
            "substitute",
            "instantiate",
            "calculation",
            "join",
            "exhibit",
            "define",
        ];
        let mut how: Option<Method> = known_methods
            .contains(&head.as_str())
            .then(|| Method::Named(head.clone()));
        if how.is_none() && head.starts_with("def:") {
            let Item::Record(item) = self.item_cited(&head) else {
                panic!("{head} is a definition of the database");
            };
            // A definition stated as a biconditional is used by unfolding
            // it; one stated as an equation is used by citing the lemma that
            // proves it. With no target it is taken as stated.
            how = Some(if !item.fields.contains_key("target") {
                Method::TakeDefinition
            } else if item.conclusions.iter().any(|(text, _)| text.contains('↔')) {
                Method::Reading(self.reading(item, &term, step)?)
            } else {
                Method::UnfoldEquation
            });
        }
        if how.is_none() && head.starts_with("thm:") {
            how = Some(Method::Cite);
        }
        let Some(how) = how else {
            return Err(
                self.defect(step.line, format!("no expansion for {}", repr(&head)))
            );
        };
        // The step's own requires lines hold for the whole of it, offered as
        // `written` is, which the membership lookup and the one-lemma bridge
        // read and a search does not.
        let known = if step.requires.is_empty() {
            Facts::new()
        } else {
            self.supplied(Some(step), scope, facts)?
        };
        let citing = std::mem::replace(
            &mut self.citing,
            step.just.refs.iter().cloned().collect(),
        );
        let lines = self.lines.clone();
        let made = self.writing(scope, &known, true, |me| {
            me.by_method(&how, step, &node, &term, scope, facts, &lines)
        });
        self.citing = citing;
        let made = made?;
        // Every route the method had declined, so nothing here owns the
        // step: this elaborator's limit rather than a defect in the text.
        let proof = match made {
            Declined(d) => {
                return Err(self.defect(
                    step.line,
                    format!("no method owns this step: {}", self.say(&d)),
                ));
            }
            Built(None) => return Ok((scope.to_string(), facts.clone(), closers)), // a join, which emits nothing
            Built(Some(p)) => p,
        };
        let said = self.said(step)?;
        let proof = self.check_step(proof, step, number, false)?;
        self.lines.set(
            number,
            Line {
                term: term.clone(),
                proof: proof.clone(),
                sentences: said.clone(),
            },
        );
        facts.set(term.clone(), proof.clone());
        // A line saying several things says each of them, only as deep as
        // the sentences the text wrote.
        if said.len() > 1 {
            self.unpack(&term, &proof, scope, facts, said.len() - 1);
        }
        Ok((scope.to_string(), facts.clone(), closers))
    }

    /// A step's proof by the method its justification names.
    #[allow(clippy::too_many_arguments)]
    fn by_method(
        &mut self,
        how: &Method,
        step: &Step,
        node: &Node,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        let made = match how {
            Method::Named(name) => match name.as_str() {
                "algebra" => self.algebra(step, term, scope, facts, lines)?,
                "arithmetic" => self.arithmetic(step, term, scope, facts)?,
                "inequalities" => self.inequalities(step, term, scope, facts, lines)?,
                "membership" => self.by_membership(step, term, scope, facts)?,
                "substitute" => {
                    self.substitute(step, node, term, scope, facts, lines)?
                }
                "instantiate" => self.instantiate(step, term, scope, facts, lines)?,
                "calculation" => self.calculation(step, scope, facts, lines)?,
                "join" => return self.join(step, scope, facts).map(Built),
                "exhibit" => self.exhibit(step, node, term, scope, facts, lines)?,
                "define" => self.by_define(step, term, scope, facts)?,
                _ => unreachable!("a method this names"),
            },
            Method::TakeDefinition => {
                self.take_definition(step, term, scope, facts, lines)?
            }
            Method::Reading(Way::Conclude) => {
                self.conclude(step, term, scope, facts, lines)?
            }
            Method::Reading(way) => {
                let item = self.item_cited(&step.just.head.to_string());
                self.trying(item, step, *way, term, scope, facts, lines)?
            }
            Method::UnfoldEquation => self.unfold_equation(step, term, scope, facts)?,
            Method::Cite => self.cite(step, term, scope, facts, lines)?,
        };
        Ok(made.map(Some))
    }

    // --- the methods ----------------------------------------------------

    /// What an item states, however the database says it is supplied.
    ///
    /// An item with no target is assumed: nothing in the library has its
    /// shape, and the file says so at its head. An item that has one and
    /// whose every clause misses is an error: the field says where the claim
    /// lands, and it does not land there.
    pub fn cite_item(
        &mut self,
        step: &Step,
        goal: &str,
        scope: &str,
        facts: &Facts,
        item: Item<'a>,
        cites: Option<&str>,
    ) -> Checked<Route<Proof>> {
        // An item this corpus proves is applied the way a cited one is,
        // however the step reaches it.
        if let Item::Theorem(t) = item {
            return self
                .cite_corpus(step, goal, scope, facts, t, cites)
                .map(Built);
        }
        let Item::Record(record) = item else {
            unreachable!()
        };
        let labels = targets::clauses(record);
        let seed = self.filling(step, record, cites)?;
        for label in &labels {
            let found = self.apply_lemma(
                label,
                &self.to_term(goal),
                scope,
                facts,
                Some(step),
                true,
                Some(&seed),
            )?;
            if !found.is_declined() {
                return Ok(found);
            }
        }
        let assembled =
            self.from_lemmas(&labels, goal, scope, facts, step, Some(&seed))?;
        if !assembled.is_declined() {
            return Ok(assembled);
        }
        if !labels.is_empty() {
            // The item names itself, and what its labels did not reach is
            // said as it stands.
            let wanted = if step.just.head.to_string() == "obtain" {
                format!("what step {} obtains", fmt(&step.number))
            } else {
                self.render(&self.rpn(&self.to_term(goal)))
            };
            return Err(self.defect(
                step.line,
                format!(
                    "{}:{} targets {}, and none of them reaches {wanted}",
                    item_kind(item),
                    record.qualified(),
                    labels.join(", ")
                ),
            ));
        }
        self.assume_item(step, goal, scope, facts, record, cites)
            .map(Built)
    }

    /// An item the database gives no target for, taken as it states itself,
    /// under the hypotheses it asks for; and where the step claims one side
    /// of what it states, the other side is what the step cites.
    fn assume_item(
        &mut self,
        step: &Step,
        goal: &str,
        scope: &str,
        facts: &Facts,
        item: &'a Record,
        cites: Option<&str>,
    ) -> Checked<Proof> {
        let (asks, ends) =
            self.names_kept(|me| -> Checked<(Vec<String>, Vec<String>)> {
                for (name, node) in me.item_binding(step, item, cites)? {
                    let term = me.term(&node)?;
                    me.names.insert(name, term);
                }
                me.in_its_names(
                    Item::Record(item),
                    |me| -> Checked<(Vec<String>, Vec<String>)> {
                        let mut asks = Vec::new();
                        for h in &item.hypotheses {
                            let body = hypothesis_body(h.kind.as_str(), &h.text);
                            let node = me.read(&body)?;
                            asks.push(me.term(&node)?);
                        }
                        let mut ends = Vec::new();
                        for (text, _line) in &item.conclusions {
                            for sentence in me.sentences(text) {
                                let node = me.read(&sentence)?;
                                ends.push(me.term(&node)?);
                            }
                        }
                        Ok((asks, ends))
                    },
                )
            })?;
        // What is assumed is what the item states, and a step may claim one
        // side of it.
        let mut whole = ends[0].clone();
        for extra in &ends[1..] {
            whole = t!(whole, extra, "wa");
        }
        let mut other: Option<String> = None;
        if self.rebound(&whole, goal) {
            whole = goal.to_string();
        }
        if whole != goal {
            let node = self.to_term(&whole);
            let mut sides: Vec<String> = if node.label() == Some("wb") {
                node.children().iter().map(|c| self.rpn(c)).collect()
            } else {
                Vec::new()
            };
            // A side binding other letters than the claim is the claim, and
            // is stated in the claim's letters.
            for i in 0..sides.len() {
                if sides[i] != goal && self.rebound(&sides[i], goal) {
                    sides[i] = goal.to_string();
                    whole = t!(sides.join(" "), "wb");
                }
            }
            let Some(at) = sides.iter().position(|s| s == goal) else {
                return Err(self.defect(
                    step.line,
                    format!(
                        "{}:{} is taken as stated and states {}, where step {} claims {}",
                        item_kind(Item::Record(item)),
                        item.qualified(),
                        self.render(&whole),
                        fmt(&step.number),
                        self.render(goal)
                    ),
                ));
            };
            other = Some(sides[1 - at].clone());
        }
        let mut statement = whole.clone();
        for one in asks.iter().rev() {
            statement = t!(one, statement, "wi");
        }
        let label = self.fresh("itm")?;
        let text = format!("|- {}", self.render(&statement));
        self.axioms.push((label.clone(), text.clone()));
        let free = self.free_floats(&text);
        let floats = free
            .iter()
            .map(|v| (self.typecode(&self.float_of(v)).to_string(), v.clone()))
            .collect();
        self.b.sigs.insert(
            label.clone(),
            Signature {
                label: label.clone(),
                kind: Kind::Axiom,
                statement: text.split_whitespace().map(String::from).collect(),
                floats,
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
        let mut parts: Vec<String> = free.iter().map(|v| self.float_of(v)).collect();
        parts.push(label);
        let mut proof = pf!(self.b; parts.join(" "));
        // An item taken as stated asks for its hypotheses like any other.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let known = self.with_cited(Some(step), scope, &supplied, None);
        if asks.is_empty() {
            proof = pf!(self.b; whole, scope, proof, "a1i");
        }
        for (i, one) in asks.iter().enumerate() {
            let mut rest = whole.clone();
            for later in asks[i + 1..].iter().rev() {
                rest = t!(later, rest, "wi");
            }
            let lines = self.lines.clone();
            let found = self.settle(
                &self.to_term(one),
                scope,
                &known,
                3,
                Some(step),
                Some(&lines),
            )?;
            let found = match found {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "{}:{} is taken as stated and asks for {}, which step {} does not supply: {}",
                            item_kind(Item::Record(item)),
                            item.qualified(),
                            self.render(one),
                            fmt(&step.number),
                            self.say(&d)
                        ),
                    ));
                }
            };
            let fold = if i == 0 { "syl" } else { "mpd" };
            proof = pf!(self.b; scope, one, rest, found, proof, fold);
        }
        let Some(other) = other else {
            return Ok(proof);
        };
        // The side the step does not claim is what it cites, a line whole or
        // one line per conjunct.
        let node = self.to_term(&other);
        let pair: Vec<String> = if node.label() == Some("wa") {
            node.children().iter().map(|c| self.rpn(c)).collect()
        } else {
            Vec::new()
        };
        let given = if let Some(g) = known.get(&other) {
            g
        } else if !pair.is_empty() && pair.iter().all(|p| known.has(p)) {
            let a = known.get(&pair[0]).unwrap();
            let b = known.get(&pair[1]).unwrap();
            pf!(self.b; scope, pair[0], pair[1], a, b, "jca")
        } else {
            return Err(self.defect(
                step.line,
                format!(
                    "step {} cites nothing that says {}",
                    fmt(&step.number),
                    self.render(&other)
                ),
            ));
        };
        let near = self.rpn(&self.to_term(&whole).children()[0]);
        if goal == near {
            return Ok(pf!(self.b; scope, goal, other, given, proof, "mpbird"));
        }
        Ok(pf!(self.b; scope, other, goal, given, proof, "mpbid"))
    }

    /// What an item's names stand for at this step, as the page says it: a
    /// name the step writes first, then the item's conclusion matched
    /// against the step's claim, and each of its hypotheses against what the
    /// step cites, until nothing more is learned.
    fn item_binding(
        &mut self,
        step: &Step,
        item: &'a Record,
        cites: Option<&str>,
    ) -> Checked<NodeBinding> {
        let mut bound = NodeBinding::new();
        for (name, value) in instantiation(cites.unwrap_or(&step.just.text)) {
            let node = self.read(&value)?;
            bound.insert(name, node);
        }
        let (ends, mut hyps) = self.in_its_names(
            Item::Record(item),
            |me| -> Checked<(Vec<Node>, Vec<Node>)> {
                let mut ends = Vec::new();
                for (text, _line) in &item.conclusions {
                    for sentence in me.sentences(text) {
                        ends.push(me.read(&sentence)?);
                    }
                }
                let mut hyps = Vec::new();
                for h in &item.hypotheses {
                    hyps.push(me.read(&hypothesis_body(h.kind.as_str(), &h.text))?);
                }
                Ok((ends, hyps))
            },
        )?;
        let ctx = Context::new(&self.g.notations, self.records);
        // A name the item binds itself is the item's own and stands for
        // nothing at the step.
        let mut own: BTreeSet<String> = BTreeSet::new();
        let mut rest: Vec<Node> = ends.iter().chain(hyps.iter()).cloned().collect();
        while let Some(node) = rest.pop() {
            if let Some(b) = ctx.binders.get(&node.notation) {
                for &at in &b.held {
                    if node.children[at].is_name() {
                        own.insert(node.children[at].text.clone());
                    }
                }
            }
            rest.extend(node.children.iter().cloned());
        }
        let mut variables: BTreeSet<String> = BTreeSet::new();
        for n in ends.iter().chain(hyps.iter()) {
            variables.extend(n.names());
        }
        let variables: BTreeSet<String> = variables.difference(&own).cloned().collect();
        // A definition is a biconditional, and a step unfolding one claims
        // one side and cites the other, so each side is matched as well as
        // the whole.
        let sides: Vec<Node> = ends
            .iter()
            .filter(|e| e.notation == "biconditional")
            .flat_map(|e| e.children.iter().cloned())
            .collect();
        hyps.extend(sides.iter().cloned());
        let sites = indexmap::IndexSet::new();
        let said = self.said(step)?;
        for end in ends.iter().chain(sides.iter()) {
            for s in &said {
                if let Some(got) = match_tree(end, s, &bound, &variables, &sites, &ctx)
                {
                    bound = got;
                    break;
                }
            }
        }
        let mut given: Vec<Node> = Vec::new();
        for r in &step.just.refs {
            if let Some(line) = self.lines.get(r) {
                given.extend(line.sentences.iter().cloned());
            }
        }
        // Only what the step cites: a sort line fixes nothing.
        for h in &self.thm.hypotheses {
            if h.label.as_ref().is_some_and(|l| step.just.refs.contains(l)) {
                given.push(self.read(&hypothesis_body(h.kind.as_str(), &h.text))?);
            }
        }
        let mut learned = true;
        while learned {
            learned = false;
            for hyp in &hyps {
                for fact in &given {
                    if let Some(got) =
                        match_tree(hyp, fact, &bound, &variables, &sites, &ctx)
                    {
                        if got.len() > bound.len() {
                            bound = got;
                            learned = true;
                            break;
                        }
                    }
                }
            }
        }
        Ok(bound)
    }

    /// A universal used at one term: `instantiate s := a in line 10` takes a
    /// line claiming something of every s and claims it of one of them.
    fn instantiate(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let where_ = step.just.target.clone().unwrap_or_default();
        let Some(held) = lines.get(&where_) else {
            return Err(self.defect(
                step.line,
                format!("instantiate names no line or label {}", repr(&where_)),
            ));
        };
        // A line may say several things at once, and the `for every` is
        // rarely the first of them. Taken apart on its own.
        let known = Facts::new();
        known.set(held.term.clone(), self.carried(&where_, facts, lines));
        let whole_proof = known.get(&held.term).unwrap();
        self.unpack(&held.term, &whole_proof, scope, &known, 4);
        let universals: Vec<String> = self
            .parts(&held.term)
            .into_iter()
            .filter(|p| matches!(self.to_term(p).label(), Some("wral") | Some("wal")))
            .collect();
        // The universal is the one binding the name the step instantiates.
        let pairs = instantiation(&step.just.text);
        let bound: BTreeSet<Option<String>> = pairs
            .iter()
            .map(|(n, _)| {
                self.bound_as
                    .get(n)
                    .cloned()
                    .or_else(|| self.b.flabel.get(n).cloned())
            })
            .collect();
        let said = universals
            .iter()
            .find(|p| bound.contains(&Some(self.rpn(&self.to_term(p).children()[1]))))
            .or(universals.first())
            .cloned();
        let Some(said) = said else {
            return Err(self.defect(
                step.line,
                format!("{where_} claims nothing of every such name"),
            ));
        };
        let mut proof = known.get(&said).unwrap();
        let mut whole = self.to_term(&said);
        // Each value is the one written for the name the line quantifies at
        // that level, whatever its place in the list.
        let by_name: IndexMap<String, String> = pairs.iter().cloned().collect();
        for _ in 0..pairs.len() {
            let label = whole.label().unwrap_or("");
            let found = rules::INSTANCES.iter().find(|(k, _)| *k == label);
            let Some(instance) = found.map(|(_, i)| (i.lemma, i.domain_var, i.domain))
            else {
                return Err(self
                    .defect(step.line, "more names instantiated than are quantified"));
            };
            let (lemma, slot, domain) = instance;
            let (body, variable) =
                (whole.children()[0].clone(), whole.children()[1].clone());
            let domain = match domain {
                Some(d) => d.to_string(),
                None => self.rpn(&whole.children()[2]),
            };
            let letter = self.rpn(&variable);
            let named = self
                .written_as
                .get(&letter)
                .cloned()
                .unwrap_or(letter.clone());
            let Some(value) = by_name.get(&named).cloned() else {
                return Err(self.defect(
                    step.line,
                    format!("{where_} quantifies a name the step gives no value, before the ones it does"),
                ));
            };
            let mark = format!("{letter} cv");
            let node = self.read(&value)?;
            let at = self.term(&node)?;
            let instance = self.restated(&body, &mark, &at);
            let (ph, ps) = (self.rpn(&body), self.rpn(&instance));
            let member = t!(at, domain, "wcel");
            let tie = self.to_term(&t!(t!(mark, at, "wceq"), t!(ph, ps, "wb"), "wi"));
            let asked = match self.prove_essential(&tie, scope, facts)? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "{lemma} cannot tie the line to its instance: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
            let mut binds =
                binds! {"ph" => &ph, "ps" => &ps, "x" => &letter, "A" => &at};
            binds.insert(slot.to_string(), domain.clone());
            let applied = self.b.ap(lemma, &binds, &[&asked]);
            let w = self.rpn(&whole);
            let required = self.required(step, &member, scope, facts)?;
            let carried =
                pf!(self.b; scope, member, t!(w, ps, "wi"), required, applied, "syl");
            proof = pf!(self.b; scope, w, ps, proof, carried, "mpd");
            whole = instance;
        }
        // What a universal says of one name is often a conditional, and the
        // step claims what it concludes: each thing asked on the way is a
        // line the step cites.
        let mut reached = self.rpn(&whole);
        while reached != term {
            let reads = self.to_term(&reached);
            // What the universal says may be the claim in other words.
            if let Built(alike) =
                self.same(&reads, &self.to_term(term), scope, facts, None)?
            {
                return Ok(Built(
                    pf!(self.b; scope, reached, term, proof, alike, "mpbid"),
                ));
            }
            if reads.label() != Some("wi") {
                return Err(self.defect(
                    step.line,
                    format!(
                        "{where_} at those terms says {}, and the step claims {}",
                        self.render(&reached),
                        self.render(term)
                    ),
                ));
            }
            let (asks, rest) = (
                self.rpn(&reads.children()[0]),
                self.rpn(&reads.children()[1]),
            );
            // An `instantiate` is the head of a step, so what the universal
            // asks at this term is the text's to supply.
            let supplied = match self.settle(
                &self.to_term(&asks),
                scope,
                facts,
                3,
                None,
                None,
            )? {
                Built(p) => p,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "instantiating at that term wants {}, which step {} does not supply: {}",
                            self.render(&asks),
                            fmt(&step.number),
                            self.say(&d)
                        ),
                    ));
                }
            };
            proof = pf!(self.b; scope, asks, rest, supplied, proof, "mpd");
            reached = rest;
        }
        Ok(Built(proof))
    }

    /// One equation put into one claim, at the place the tree names: the
    /// step's own claim, or a line `into` names.
    fn substitute(
        &mut self,
        step: &Step,
        node: &Node,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let text = str::trim(&step.just.text).to_string();
        let Some(said) = SUBSTITUTE.captures(&text) else {
            return Err(self.defect(step.line, "a substitute that names no equation"));
        };
        let equation = self.read(&said[1])?;
        let (left, right) =
            (equation.children[0].clone(), equation.children[1].clone());
        let (old, new) = (self.term(&left)?, self.term(&right)?);
        // Which way the equation faces in the kernel is the lemma's choice,
        // not the text's, so either is accepted and turned if it has to be.
        let mut facing = facts.get(&t!(old, new, "wceq"));
        if str::trim(&said[2]) == "arithmetic" {
            let what = format!(
                "step {} substitutes {}",
                fmt(&step.number),
                str::trim(&said[1])
            );
            facing = Some(self.closed_fact(
                &t!(old, new, "wceq"),
                scope,
                facts,
                &what,
                Some(step),
            )?);
        }
        let facing = match facing {
            Some(f) => f,
            None => {
                let Some(held) = facts.get(&t!(new, old, "wceq")) else {
                    return Err(self.defect(
                        step.line,
                        format!("no equation {old} = {new} in scope"),
                    ));
                };
                pf!(self.b; scope, new, old, held, "eqcomd")
            }
        };
        let turned = pf!(self.b; scope, old, new, facing, "eqcomd");
        let into = said.get(3).map(|m| m.as_str().to_string());
        let Some(into_text) = into else {
            // An equation is one fact and a claimed equation is one fact, and
            // neither carries a direction: the cited equation is read
            // whichever way rewrites, and the step's own two sides whichever
            // way one reaches the other.
            let sides = [
                (node.children[0].clone(), node.children[1].clone(), false),
                (node.children[1].clone(), node.children[0].clone(), true),
            ];
            for (was, now, faces) in [(&old, &new, &facing), (&new, &old, &turned)] {
                for (start, other, flip) in &sides {
                    let Built((built, proof)) =
                        self.rewrite(start, was, now, scope, faces)?
                    else {
                        continue;
                    };
                    if built != self.term(other)? {
                        continue;
                    }
                    if *flip {
                        let (s, o) = (self.term(start)?, self.term(other)?);
                        return Ok(Built(pf!(self.b; scope, s, o, proof, "eqcomd")));
                    }
                    return Ok(Built(proof));
                }
            }
            return Err(self.defect(step.line, "the substitution misses the claim"));
        };
        let where_ = into_text
            .split_whitespace()
            .last()
            .unwrap_or("")
            .to_string();
        let into = lines
            .get(&where_)
            .unwrap_or_else(|| panic!("no line {where_} to substitute into"));
        if into.sentences.is_empty() {
            return Err(
                self.defect(step.line, format!("{into_text} is not a line to rewrite"))
            );
        }
        // A line may say several things and the substitution land in one of
        // them, so each sentence is offered with a proof of itself.
        let held = self.carried(&where_, facts, lines);
        let known = Facts::new();
        known.set(into.term.clone(), held.clone());
        self.unpack(&into.term, &held, scope, &known, 4);
        // A sentence joined by `and` is its parts as surely as a line of two
        // sentences is, so each is offered.
        let mut offered = Vec::new();
        let mut work: std::collections::VecDeque<Node> =
            into.sentences.iter().cloned().collect();
        while let Some(one) = work.pop_front() {
            offered.push(one.clone());
            if !one.children.is_empty() {
                let said = self.term(&one)?;
                if self.to_term(&said).label() == Some("wa") {
                    work.extend(one.children.iter().cloned());
                }
            }
        }
        for one in &offered {
            let start = self.term(one)?;
            if !known.has(&start) {
                if let Some(p) = facts.get(&start) {
                    known.set(start, p);
                }
            }
        }
        for (was, now, faces) in [(&old, &new, &facing), (&new, &old, &turned)] {
            for one in &offered {
                let start = self.term(one)?;
                let Some(given) = known.get(&start) else {
                    continue;
                };
                let Built((built, proof)) =
                    self.rewrite(one, was, now, scope, faces)?
                else {
                    continue;
                };
                if built == term {
                    return Ok(Built(
                        pf!(self.b; scope, start, term, given, proof, "mpbid"),
                    ));
                }
            }
        }
        Err(self.defect(step.line, "the substitution misses the claim"))
    }

    /// A definition whose right side is not an existence claim, read the way
    /// the text reads it: right to left.
    #[allow(clippy::too_many_arguments)]
    fn one_equivalent(
        &mut self,
        lemma: &str,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        // A claim the lemma's left side fits only as the standard form reads
        // it is reached at the lemma's own instance and carried by `same`.
        let mut whole = self.statement(lemma);
        while whole.label() == Some("wi") {
            whole = whole.children()[1].clone();
        }
        let binding = if whole.label() == Some("wb") {
            let variables = names_of(&whole);
            self.fits_as(&whole.children()[0], &self.to_term(term), &variables, None)
        } else {
            None
        };
        let instance = match &binding {
            Some(b) => self.rpn(&whole.children()[0].substitute(b)),
            None => term.to_string(),
        };
        if instance != term {
            let made = take!(
                self.one_equivalent(lemma, step, &instance, scope, facts, lines)?
            );
            let supplied = self.supplied(Some(step), scope, facts)?;
            let held = self.with_cited(Some(step), scope, &supplied, None);
            let alike = take!(self.same(
                &self.to_term(&instance),
                &self.to_term(term),
                scope,
                &held,
                None
            )?);
            return Ok(Built(
                pf!(self.b; scope, instance, term, made, alike, "mpbid"),
            ));
        }
        // What a lemma's right side says beyond what its left fixes can only
        // come from the lines the step cites, in the order it writes them.
        let said: Vec<String> = step
            .just
            .refs
            .iter()
            .filter_map(|r| lines.get(r).map(|l| l.term))
            .collect();
        let mut hint = said.first().cloned();
        for extra in said.iter().skip(1) {
            hint = Some(t!(hint.unwrap(), extra, "wa"));
        }
        let (says, right) = take!(self.unfolding(
            step,
            lemma,
            term,
            None,
            None,
            None,
            scope,
            facts,
            hint.as_deref()
        )?);
        // The right side is what the step supplies, and not whatever the
        // scope would give.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let known = self.with_cited(Some(step), scope, &supplied, None);
        let under = take!(self.settle(
            &self.to_term(&right),
            scope,
            &known,
            3,
            Some(step),
            Some(lines)
        )?);
        Ok(Built(
            pf!(self.b; scope, term, right, under, says, "mpbird"),
        ))
    }

    /// The same two-sided claim with its sides the other way round.
    fn turned(&self, rpn: &str) -> Option<String> {
        let node = self.to_term(rpn);
        if node.children().len() != 2 {
            return None;
        }
        Some(t!(
            self.rpn(&node.children()[1]),
            self.rpn(&node.children()[0]),
            node.label().unwrap_or("")
        ))
    }

    /// `(binding, proof of the left side at it)` from one of the things a
    /// cited line says: matched as written, with only defined names read,
    /// and as the standard form reads it; no one of the three covers the
    /// others.
    fn unfolds_from(
        &mut self,
        left: &Term,
        held: &Facts,
        variables: &Vars,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<(Binding, Proof)>> {
        let entries = held.entries();
        for (said, shown) in &entries {
            if let Some(binding) =
                fit(left, &self.to_term(said), &Binding::new(), variables)
            {
                if !binding.is_empty() {
                    return Ok(Built((binding, shown.clone())));
                }
            }
        }
        // Then with only the defined names read as what they name.
        for (said, shown) in &entries {
            let read = self.names_read(&self.to_term(said), None);
            let read_rpn = self.rpn(&read);
            if read_rpn == *said {
                continue;
            }
            let Some(binding) =
                fit(left, &read, &Binding::new(), variables).filter(|b| !b.is_empty())
            else {
                continue;
            };
            if let Built(alike) =
                self.same(&self.to_term(said), &read, scope, facts, None)?
            {
                return Ok(Built((
                    binding,
                    pf!(self.b; scope, said, read_rpn, shown, alike, "mpbid"),
                )));
            }
        }
        for (said, shown) in &entries {
            let Some(binding) = self
                .fits_as(left, &self.to_term(said), variables, None)
                .filter(|b| !b.is_empty())
            else {
                continue;
            };
            let instance = left.substitute(&binding);
            if let Built(alike) =
                self.same(&self.to_term(said), &instance, scope, facts, None)?
            {
                let i = self.rpn(&instance);
                return Ok(Built((
                    binding,
                    pf!(self.b; scope, said, i, shown, alike, "mpbid"),
                )));
            }
        }
        Ok(Route::no("nothing the line says is what the lemma unfolds"))
    }

    /// A definition unfolded to reach one part of what it says: read left to
    /// right, and what it gives taken apart.
    #[allow(clippy::too_many_arguments)]
    pub fn one_unfolded(
        &mut self,
        lemma: &str,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let sig = self.sig(lemma).clone();
        let whole = self.statement(lemma);
        let variables = names_of(&whole);
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        if reads.label() != Some("wb") {
            return Ok(Route::no(format!("{lemma} states no biconditional")));
        }
        // A line may say several things at once, and what the definition
        // unfolds is any one of them.
        let mut chosen = None;
        for r in &step.just.refs {
            let Some(cited) = lines.get(r) else {
                continue;
            };
            let held = Facts::new();
            held.set(cited.term.clone(), self.carried(r, facts, lines));
            for one in &cited.sentences {
                let said = self.term(one)?;
                if let Some(p) = facts.get(&said) {
                    held.set_default(said, p);
                }
            }
            let whole_proof = held.get(&cited.term).unwrap();
            self.unpack(&cited.term, &whole_proof, scope, &held, 4);
            if let Built(found) = self.unfolds_from(
                &reads.children()[0],
                &held,
                &variables,
                scope,
                facts,
            )? {
                chosen = Some(found);
                break;
            }
        }
        let Some((mut binding, given)) = chosen else {
            return Ok(Route::no(format!("no cited line is what {lemma} unfolds")));
        };
        // What the left side fixes need not be everything the right side
        // holds.
        let target = self.to_term(term);
        for part in self.parts(&self.rpn(&reads.children()[1])) {
            if let Some(filled) =
                fit(&self.to_term(&part), &target, &binding, &variables)
            {
                binding = filled;
                break;
            }
        }
        // The claim of the membership half leaves the property half
        // standing as the lemma's own name, and `elrab`'s hypothesis is what
        // says what that half is.
        for essential in &sig.essentials {
            let asked = self.essential(essential);
            if let Some(more) = self.substituted_slot(&asked, &binding) {
                for (k, v) in more {
                    binding.insert(k, v);
                }
            }
        }
        let left = self.rpn(&reads.children()[0].substitute(&binding));
        let right = self.rpn(&reads.children()[1].substitute(&binding));
        // What carries the unfolding to the claim asks from what the step
        // names, requires lines included.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let facts = self.with_cited(Some(step), scope, &supplied, None);
        let (made, _) = take!(self.unfolding(
            step,
            lemma,
            &left,
            Some(&right),
            None,
            None,
            scope,
            &facts,
            None
        )?);
        let proof = pf!(self.b; scope, left, right, given, made, "mpbid");
        let known = Facts::new();
        known.set(right.clone(), proof.clone());
        self.unpack(&right, &proof, scope, &known, 4);
        if let Some(p) = known.get(term) {
            return Ok(Built(p));
        }
        // Or it is, once what the lemma says is put in the page's words.
        for (said, shown) in known.entries() {
            if let Built(alike) =
                self.same(&self.to_term(&said), &target, scope, &facts, None)?
            {
                return Ok(Built(
                    pf!(self.b; scope, said, term, shown, alike, "mpbid"),
                ));
            }
        }
        // What the unfolding says and how the readable line spells it are
        // allowed to differ, so long as set.mm says they are the same claim.
        let offered = facts.with(&known);
        match self.settle(&target, scope, &offered, 3, Some(step), Some(lines))? {
            Built(p) => Ok(Built(p)),
            Declined(d) => {
                let inner = self.say(&d);
                Ok(self.no(format!("{lemma} does not say {{}}: {inner}"), &[term]))
            }
        }
    }

    /// Use whichever lemma the target names reaches the claim; a defect the
    /// way found on its own account is not one of the lemmas declining, and
    /// goes past.
    #[allow(clippy::too_many_arguments)]
    pub fn trying(
        &mut self,
        item: Item<'a>,
        step: &Step,
        way: Way,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let mut declines = Vec::new();
        for lemma in item_clauses(item) {
            let found = match way {
                Way::Equivalent => {
                    self.one_equivalent(&lemma, step, term, scope, facts, lines)?
                }
                _ => self.one_unfolded(&lemma, step, term, scope, facts, lines)?,
            };
            match found {
                Built(p) => return Ok(Built(p)),
                Declined(d) => declines.push(self.say(&d)),
            }
        }
        if declines.is_empty() {
            return Ok(Route::no(format!("{} targets nothing", qualified(item))));
        }
        Ok(Route::no(declines.join("; ")))
    }

    /// Which of three ways a biconditional definition reaches a claim: the
    /// claim decides, and what the lemma states decides with it.
    fn reading(&mut self, item: &'a Record, term: &str, step: &Step) -> Checked<Way> {
        for lemma in targets::clauses(item) {
            let mut whole = self.statement(&lemma);
            while whole.label() == Some("wi") {
                whole = whole.children()[1].clone();
            }
            if whole.label() != Some("wb") {
                return Ok(Way::Conclude);
            }
            if whole.children()[1].label() == Some("wrex") {
                // The existence claim itself is the definition unfolded from a
                // line saying its left side; a left side is shown by a witness.
                if self.to_term(term).label() == Some("wrex") {
                    return Ok(Way::Unfolded);
                }
                if step.just.refs.iter().any(|r| {
                    self.lines
                        .get(r)
                        .is_some_and(|l| self.to_term(&l.term).label() == Some("wrex"))
                }) {
                    return Ok(Way::Equivalent);
                }
                return Ok(Way::Conclude);
            }
            let variables = names_of(&whole);
            if self
                .fits_as(&whole.children()[0], &self.to_term(term), &variables, None)
                .is_some()
            {
                return Ok(Way::Equivalent);
            }
        }
        Ok(Way::Unfolded)
    }

    /// A definition with no target is taken as it states itself, unless a
    /// line the step cites already says it, whole or with another letter
    /// bound.
    fn take_definition(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(found) = self.projected(step, term, scope, facts, lines) {
            return Ok(Built(found));
        }
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            let parts = Facts::new();
            parts.set(held.term.clone(), self.carried(r, facts, lines));
            let whole = parts.get(&held.term).unwrap();
            self.unpack(&held.term, &whole, scope, &parts, 4);
            for (said, proof) in parts.entries() {
                if let Some(spelt) = self.respelt(&proof, &said, term, scope)? {
                    return Ok(Built(spelt));
                }
            }
        }
        let Item::Record(item) = self.item_cited(&step.just.head.to_string()) else {
            panic!("a definition of the database");
        };
        self.assume_item(step, term, scope, facts, item, None)
            .map(Built)
    }

    /// The claim, when a line the step cites is a conjunction stating it,
    /// taken apart on its own to the depth of a congruence's six conjuncts.
    fn projected(
        &self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Option<Proof> {
        for r in &step.just.refs {
            let cited = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
            let known = Facts::new();
            known.set(cited.term.clone(), self.carried(r, facts, lines));
            let whole = known.get(&cited.term).unwrap();
            self.unpack(&cited.term, &whole, scope, &known, 8);
            if let Some(p) = known.get(term) {
                return Some(p);
            }
        }
        None
    }

    /// A definition stated as an equation, one clause per `then` group: the
    /// clause is chosen by which lemma's conclusion is what the step claims.
    /// None reaching it is a defect, since the database named these lemmas.
    fn unfold_equation(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let head = step.just.head.to_string();
        let Item::Record(item) = self.item_cited(&head) else {
            panic!("a definition of the database");
        };
        let labels: Vec<String> = targets::split_entries(item.field_or_empty("target"))
            .into_iter()
            .map(String::from)
            .collect();
        let seed = self.filling(step, item, None)?;
        match self.by_clause(&labels, term, scope, facts, step, Some(&seed))? {
            Built(p) => Ok(Built(p)),
            Declined(_) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {head} gives what step {} claims",
                    fmt(&step.number)
                ),
            )),
        }
    }

    /// A label for a generated statement nothing else is using, saying which
    /// file it belongs to, and looked for rather than taken.
    pub fn fresh(&mut self, prefix: &str) -> Checked<String> {
        let stem = self.own_label()?;
        let mut number = self.axioms.len() + 1;
        while self
            .b
            .sigs
            .contains_key(&format!("{stem}.{prefix}{number}"))
        {
            number += 1;
        }
        Ok(format!("{stem}.{prefix}{number}"))
    }

    /// The label this theorem is written under.
    pub fn own_label(&self) -> Checked<String> {
        label_of(
            &self.thm.qualified(),
            &self.b.sigs,
            &self.thm.path,
            self.thm.line,
            &proved_here(self.items),
        )
    }

    /// A chain folded by transitivity, one link at a time: each link is read
    /// as the claim relating the run so far to what the link adds, and the
    /// lemma that folds it is chosen by the two relations either side of the
    /// join.
    fn calculation(
        &mut self,
        step: &Step,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let mut links: Vec<(String, String)> = Vec::new();
        for (text, _line) in &step.just.chain {
            let stripped = text.trim_end();
            let at = stripped.rfind(char::is_whitespace).unwrap_or(0);
            let (body, cite) = (&stripped[..at], str::trim(&stripped[at..]));
            links.push((str::trim(body).to_string(), cite.to_string()));
        }
        let mut defines: BTreeSet<String> =
            self.thm.defines.iter().map(|d| d.label.clone()).collect();
        for (name, d, src) in self.visible_outside() {
            defines.insert(self.outside_label(&name, &d, src));
        }
        let first = self.read(&links[0].0)?;
        if first.text.is_empty() {
            return Err(self.defect(step.line, "a chain starts with no relation"));
        }
        let words: Vec<&str> = links[0].0.split_whitespace().collect();
        let Some(at) = outermost(&words, &first.text) else {
            return Err(self.defect(
                step.line,
                format!(
                    "a chain's first line puts its {} only inside brackets",
                    first.text
                ),
            ));
        };
        let mut rest = words[at + 1..].join(" ");
        let first_term = self.term(&first)?;
        let whole = self.to_term(&first_term);
        let left = self.rpn(&whole.children()[0]);
        let mut right = self.rpn(&whole.children()[1]);
        let mut said = whole.label().unwrap_or("").to_string();
        let mut relation = if said == "wbr" {
            self.rpn(&whole.children()[2])
        } else {
            String::new()
        };
        let mut proof = self.link_held(
            step,
            &links[0].1,
            &whole,
            &links[0].0,
            scope,
            facts,
            lines,
            &defines,
        )?;
        for (body, cite) in &links[1..] {
            // The relation, and what follows it. `body` was trimmed when
            // it was read.
            let (mark, added) = match body.split_once(char::is_whitespace) {
                Some((mark, added)) => {
                    (mark.to_string(), added.trim_start().to_string())
                }
                None => (body.clone(), String::new()),
            };
            let written = format!("{rest} {mark} {added}");
            let node = self.read(&written)?;
            let joined_term = self.term(&node)?;
            let joined = self.to_term(&joined_term);
            let joined_label = joined.label().unwrap_or("").to_string();
            let Some(fold) = rules::folding(&said, &joined_label) else {
                return Err(self.defect(
                    step.line,
                    format!("no transitivity folds {said} into {joined_label}"),
                ));
            };
            if self.rpn(&joined.children()[0]) != right {
                return Err(self.defect(
                    step.line,
                    "a link that reads the other way round from the one above it",
                ));
            }
            let nxt = self.rpn(&joined.children()[1]);
            if joined_label == "wbr" {
                relation = self.rpn(&joined.children()[2]);
            }
            let held = self.link_held(
                step, cite, &joined, &written, scope, facts, lines, &defines,
            )?;
            proof = pf!(self.b; scope, left, right, nxt, relation, proof, held, fold);
            right = nxt;
            rest = added;
            said = if said == "wceq" && joined_label == "wceq" {
                "wceq".to_string()
            } else {
                "wbr".to_string()
            };
        }
        Ok(Built(proof))
    }

    /// The proof of one link of a chain, from what it cites.
    #[allow(clippy::too_many_arguments)]
    fn link_held(
        &mut self,
        step: &Step,
        cite: &str,
        claim: &Term,
        written: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
        defines: &BTreeSet<String>,
    ) -> Checked<Proof> {
        // A link of numerals alone may name `arithmetic` rather than a line.
        let what = format!("a link of step {} claims {written}", fmt(&step.number));
        if cite == "arithmetic" && claim.names().is_empty() {
            return self.closed_fact(&self.rpn(claim), scope, facts, &what, Some(step));
        }
        // One whose terms have letters in them may too, where only pieces of
        // numerals alone change.
        if cite == "arithmetic" {
            if claim.label() != Some("wceq") {
                return Err(self.defect(
                    step.line,
                    format!("{written} relates terms with letters in them, which arithmetic does not"),
                ));
            }
            let leaf = Leaf::Arithmetic {
                what,
                step: Box::new(step.clone()),
            };
            return match self.congruence(
                &claim.children()[0],
                &claim.children()[1],
                scope,
                facts,
                Some(step),
                &leaf,
            )? {
                Built(p) => Ok(p),
                Declined(d) => Err(self.defect(
                    step.line,
                    format!("{written} changes more than numerals: {}", self.say(&d)),
                )),
            };
        }
        let line = lines
            .get(cite)
            .unwrap_or_else(|| panic!("no line {cite} cited"));
        let wanted = self.rpn(claim);
        // A define says what its name is, and a link citing it says what that
        // comes to somewhere: the standard form reads the name as its rule.
        if defines.contains(cite) && line.term != wanted {
            let supplied = self.supplied(Some(step), scope, facts)?;
            let known = self.with_cited(Some(step), scope, &supplied, None);
            let offered = facts.with(&known);
            return match self.same(
                &claim.children()[0],
                &claim.children()[1],
                scope,
                &offered,
                Some(step),
            )? {
                Built(p) => Ok(p),
                Declined(d) => Err(self.defect(
                    step.line,
                    format!("{written} is not what {cite} makes it: {}", self.say(&d)),
                )),
            };
        }
        let proof = self.carried(cite, facts, lines);
        if line.term == wanted {
            return Ok(proof);
        }
        // A line may say several things, and the link be one of them.
        let known = Facts::new();
        known.set(line.term.clone(), proof.clone());
        self.unpack(&line.term, &proof, scope, &known, 4);
        for (said_as, held) in known.entries() {
            if said_as == wanted {
                return Ok(held);
            }
            let said = self.to_term(&said_as);
            if said.label() == Some("wceq") {
                let (was, now) =
                    (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
                if t!(now, was, "wceq") == wanted {
                    return Ok(pf!(self.b; scope, was, now, held, "eqcomd"));
                }
            }
        }
        Err(self.defect(step.line, format!("{cite} does not say {written}")))
    }

    /// A step citing a define: the name, applied or not, is its value, and
    /// where that is a rule by cases the lines the step cites say which case.
    fn by_define(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let whole = self.to_term(term);
        if whole.label() != Some("wceq") {
            return Err(self.defect(
                step.line,
                format!(
                    "{} is cited for a claim that is no equation",
                    step.just
                        .defined
                        .clone()
                        .unwrap_or_else(|| "None".to_string())
                ),
            ));
        }
        let supplied = self.supplied(Some(step), scope, facts)?;
        let held = self.with_cited(Some(step), scope, &supplied, None);
        let mut why: Option<crate::outcome::Decline> = None;
        let (a, b) = (whole.children()[0].clone(), whole.children()[1].clone());
        for (one, other, turned) in [(&a, &b, false), (&b, &a, true)] {
            let reached = self.define_value(one, scope, &held)?;
            let (value, mut proof) = match reached {
                Built(r) => r,
                Declined(d) => {
                    // What the side naming a define says, over the other's.
                    if why.as_ref().is_none_or(|w| w.reason() == NAMES_NO_DEFINE) {
                        why = Some(d);
                    }
                    continue;
                }
            };
            if self.rpn(&value) != self.rpn(other) {
                match self.same(&value, other, scope, &held, Some(step))? {
                    Declined(d) => {
                        why = Some(d);
                        continue;
                    }
                    Built(alike) => {
                        proof = self.b.ap(
                            "eqtrd",
                            &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(&value), "C" => self.rpn(other)},
                            &[&proof, &alike],
                        );
                    }
                }
            }
            if !turned {
                return Ok(Built(proof));
            }
            return Ok(Built(self.b.ap(
                "eqcomd",
                &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(other)},
                &[&proof],
            )));
        }
        Ok(Declined(
            why.expect("a reason one of the two sides declined"),
        ))
    }

    /// (value, ( scope -> one = value )) where `one` is a defined name or a
    /// defined function applied, read once and taken into the case the facts
    /// say; a decline otherwise.
    fn define_value(
        &mut self,
        one: &Term,
        scope: &str,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let kept =
            std::mem::replace(&mut self.binding, super::matcher::letters_bound(one));
        let head = self.standard_step(one);
        self.binding = kept;
        let Some((how, value)) = head.filter(|(h, _)| {
            matches!(
                h,
                super::matcher::How::Defined | super::matcher::How::Applied
            )
        }) else {
            return Ok(Route::no(NAMES_NO_DEFINE));
        };
        let proof = take!(self.standard_proof(one, &how, &value, scope, held)?);
        let (mut value, mut proof) =
            take!(self.recursion_value(one, &value, proof, scope, held)?);
        // Each case in turn: the condition held takes its value, the
        // condition refuted goes on to the rest.
        while value.label() == Some("cif") && value.children().len() == 3 {
            let (condition, first, rest) = (
                value.children()[0].clone(),
                value.children()[1].clone(),
                value.children()[2].clone(),
            );
            let cond = self.rpn(&condition);
            let parts =
                binds! {"ph" => &cond, "A" => self.rpn(&first), "B" => self.rpn(&rest)};
            let holds = self.settle(&condition, scope, held, 3, None, None)?;
            let fails = if holds.is_declined() {
                self.settle(&self.to_term(&t!(cond, "wn")), scope, held, 3, None, None)?
            } else {
                holds.clone()
            };
            let (taken, lemma, why) = match (holds, fails) {
                (Built(h), _) => (first, "iftrue", h),
                (_, Built(f)) => (rest, "iffalse", f),
                _ => return Ok(Route::no("no line the step cites says which case")),
            };
            let said = t!(self.rpn(&value), self.rpn(&taken), "wceq");
            let asked = if lemma == "iftrue" {
                cond.clone()
            } else {
                t!(cond, "wn")
            };
            let law = self.b.ap(lemma, &parts, &[]);
            let stepped = pf!(self.b; scope, asked, said, why, law, "syl");
            proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(&value), "C" => self.rpn(&taken)},
                &[&proof, &stepped],
            );
            value = taken;
        }
        Ok(Built((value, proof)))
    }

    /// (value, ( scope -> one = value )) taken one step further where `value`
    /// is a sequence's part of a recursion's value at 0 or at J + 1: at 0 the
    /// part of the start (`algr0`), at J + 1 the part of the step applied to
    /// the value at J (`algrp1`). Any other value is as it was.
    fn recursion_value(
        &mut self,
        one: &Term,
        value: &Term,
        proof: Proof,
        scope: &str,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let mut path = Vec::new();
        let mut core = value.clone();
        while core.label() == Some("cfv")
            && matches!(core.children()[1].label(), Some("c1st") | Some("c2nd"))
        {
            path.push(core.children()[1].label().unwrap().to_string());
            core = core.children()[0].clone();
        }
        if core.label() != Some("cfv")
            || !self.recursions.contains_key(&self.rpn(&core.children()[1]))
        {
            return Ok(Built((value.clone(), proof)));
        }
        let (at, made) = (core.children()[0].clone(), core.children()[1].clone());
        let recursion = self.rpn(&made);
        let (step, start, count) = self.recursions[&recursion].clone();
        let where_ = self.rpn(&at);
        let common = binds! {"ph" => scope, "A" => &start, "R" => &recursion, "S" => "cvv", "F" => &step, "M" => "cc0", "Z" => "cn0"};
        let start_set = take!(self.settle(
            &self.to_term(&t!(start, "cvv", "wcel")),
            scope,
            held,
            3,
            None,
            None
        )?);
        let asked = [
            self.step("nn0uz"),
            pf!(self.b; recursion, "eqid"),
            self.b.ap("0zd", &binds! {"ph" => scope}, &[]),
            start_set,
        ];
        let (mut state, mut moved);
        if where_ == "cc0" {
            state = start.clone();
            moved = self
                .b
                .ap("algr0", &common, &asked.iter().collect::<Vec<_>>());
        } else if at.label() == Some("co")
            && at.children()[1].label() == Some("c1")
            && at.children()[2].label() == Some("caddc")
        {
            let before = self.rpn(&at.children()[0]);
            let index_in = take!(self.settle(
                &self.to_term(&t!(before, "cn0", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?);
            let map = self.to_term(&step);
            let (var, rule) = (map.children()[0].clone(), map.children()[2].clone());
            let x = self.rpn(&var);
            let a_set = take!(self.a_set_under(&x, &rule));
            let r = self.rpn(&rule);
            let into = self.b.ap(
                "fmpti",
                &binds! {"x" => &x, "A" => "cvv", "B" => "cvv", "C" => &r, "F" => &step},
                &[&pf!(self.b; step, "eqid"), &a_set],
            );
            let maps = pf!(self.b; t!("cvv", "cvv", step, "wf"), scope, into, "a1i");
            let prior = t!(before, recursion, "cfv");
            let mut with_k = common.clone();
            with_k.insert("K".to_string(), before.clone());
            let mut all: Vec<&Proof> = asked.iter().collect();
            all.push(&maps);
            let rp1 = self.b.ap("algrp1", &with_k, &all);
            let stepped = self.b.ap(
                "mpdan",
                &binds! {"ph" => scope, "ps" => t!(before, "cn0", "wcel"),
                "ch" => t!(t!(where_, recursion, "cfv"), t!(prior, step, "cfv"), "wceq")},
                &[&index_in, &rp1],
            );
            state = self.rpn(&self.restated(&rule, &format!("{x} cv"), &prior));
            // The step is taken at its value over a letter of its own.
            let y = self.spare_var()?;
            let fresh =
                self.rpn(&self.restated(&rule, &format!("{x} cv"), &format!("{y} cv")));
            let tie = self.to_term(&t!(
                t!(format!("{x} cv"), format!("{y} cv"), "wceq"),
                t!(r, fresh, "wceq"),
                "wi"
            ));
            let renaming = take!(self.prove_essential(&tie, "", &Facts::new())?);
            let respelt = self.b.ap(
                "cbvmptv",
                &binds! {"x" => &x, "y" => &y, "A" => "cvv", "B" => &r, "C" => &fresh},
                &[&renaming],
            );
            let tie = self.to_term(&t!(
                t!(format!("{y} cv"), prior, "wceq"),
                t!(fresh, state, "wceq"),
                "wi"
            ));
            let instance = take!(self.prove_essential(&tie, "", &Facts::new())?);
            let state_set = take!(self.settle(
                &self.to_term(&t!(state, "cvv", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?);
            let fvex =
                self.b
                    .ap("fvex", &binds! {"A" => &before, "F" => &recursion}, &[]);
            let prior_set = pf!(self.b; t!(prior, "cvv", "wcel"), scope, fvex, "a1i");
            let applied = self.b.ap(
                "fvmptd3",
                &binds! {"ph" => scope, "x" => &y, "A" => &prior, "B" => &fresh, "C" => &state, "D" => "cvv", "F" => &step, "V" => "cvv"},
                &[&respelt, &instance, &prior_set, &state_set],
            );
            moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(where_, recursion, "cfv"), "B" => t!(prior, step, "cfv"), "C" => &state},
                &[&stepped, &applied],
            );
        } else {
            return Ok(Built((value.clone(), proof)));
        }
        // The part asked for, taken out of the state from the inside.
        let mut held_at = t!(where_, recursion, "cfv");
        for label in path.iter().rev() {
            let pair = self.to_term(&state);
            if pair.label() != Some("cop") || count < 2 {
                return Ok(Route::no("the recursion's state is not a pair here"));
            }
            let (first, rest) =
                (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
            let mut sets = Vec::new();
            for c in [&first, &rest] {
                sets.push(self.settle(
                    &self.to_term(&t!(c, "cvv", "wcel")),
                    scope,
                    held,
                    3,
                    None,
                    None,
                )?);
            }
            let mut set_proofs = Vec::new();
            for s in sets {
                set_proofs.push(take!(s));
            }
            let both = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => t!(first, "cvv", "wcel"), "ch" => t!(rest, "cvv", "wcel")},
                &[&set_proofs[0], &set_proofs[1]],
            );
            let (lemma, part) = if label == "c1st" {
                ("op1stg", first.clone())
            } else {
                ("op2ndg", rest.clone())
            };
            let taken = t!(t!(first, "cvv", "wcel"), t!(rest, "cvv", "wcel"), "wa");
            let out = t!(t!(state, label, "cfv"), part, "wceq");
            let law = self.b.ap(
                lemma,
                &binds! {"A" => &first, "B" => &rest, "V" => "cvv", "W" => "cvv"},
                &[],
            );
            let parted = pf!(self.b; scope, taken, out, both, law, "syl");
            let lifted = self.b.ap(
                "fveq2d",
                &binds! {"ph" => scope, "A" => &held_at, "B" => &state, "F" => label},
                &[&moved],
            );
            moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(held_at, label, "cfv"), "B" => t!(state, label, "cfv"), "C" => &part},
                &[&lifted, &parted],
            );
            held_at = t!(held_at, label, "cfv");
            state = part;
        }
        let whole = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => self.rpn(one), "B" => self.rpn(value), "C" => &state},
            &[&proof, &moved],
        );
        Ok(Built((self.to_term(&state), whole)))
    }

    /// ( x e. _V -> rule e. _V ): the state a step gives is a set with nothing
    /// assumed (`closed_set`), so it is one wherever x is.
    fn a_set_under(&self, x: &str, rule: &Term) -> Route<Proof> {
        let made = match self.closed_set(rule) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        Built(
            pf!(self.b; t!(self.rpn(rule), "cvv", "wcel"), t!(format!("{x} cv"), "cvv", "wcel"), made, "a1i"),
        )
    }

    /// |- term e. _V from the lemmas `rules::CLOSED_SETHOOD` names, each asked
    /// of the parts it asks for; a decline naming a head none covers.
    fn closed_set(&self, term: &Term) -> Route<Proof> {
        let label = if term.variable().is_none() {
            term.label().and_then(|l| lookup(rules::CLOSED_SETHOOD, l))
        } else {
            None
        };
        let Some(label) = label else {
            return Route::no(format!(
                "nothing says a {} is a set",
                term.label().unwrap_or("None")
            ));
        };
        let sig = self.sig(label);
        let binds: crate::mm::spell::Binds = sig
            .floats
            .iter()
            .zip(term.children())
            .map(|((_, name), child)| (name.clone(), self.rpn(child)))
            .collect();
        let mut asked = Vec::new();
        for said in &sig.essentials {
            match self.closed_set(&self.to_term(&binds[&said[1]])) {
                Built(p) => asked.push(p),
                Declined(d) => return Declined(d),
            }
        }
        Built(self.b.ap(label, &binds, &asked.iter().collect::<Vec<_>>()))
    }

    /// An existence claim shown by naming something that answers it: the
    /// witness is read off a line the step cites, by walking that line
    /// against the shape the claim quantifies.
    fn exhibit(
        &mut self,
        step: &Step,
        node: &Node,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let whole = self.to_term(term);
        if whole.label() != Some("wrex") {
            return Err(self.defect(step.line, "an exhibit that claims no existence"));
        }
        // A claim may quantify over more than one name, and reading several
        // witnesses off the lines a step cites is what `witnessed` does.
        if whole.children()[0].label() == Some("wrex") {
            let supplied = self.supplied(Some(step), scope, facts)?;
            return self.witnessed(step, &whole, scope, &supplied, lines);
        }
        let (mut body, domain) =
            (whole.children()[0].clone(), whole.children()[2].clone());
        // The name the text quantifies under and the variable it stands for
        // are two different things.
        let said = node.children[0].text.clone();
        let mut stands = format!("{} cv", self.binder_var(&said)?);
        // The witness stands where the claim's name does in a cited line,
        // read against the whole of what the claim asks of it.
        let asked_shape = self.to_term(&t!(
            t!(stands, self.rpn(&domain), "wcel"),
            self.rpn(&body),
            "wa"
        ));
        let asked = self.applications_read(&asked_shape);
        let mut witness = None;
        for r in &step.just.refs {
            let line = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
            let actual = self.applications_read(&self.to_term(&line.term));
            witness = self.witness_in(&asked, &actual, &stands);
            if witness.is_some() {
                break;
            }
        }
        let Some(witness) = witness else {
            return Err(self.defect(step.line, "no cited line names a witness"));
        };
        // The witness may be the very letter the claim binds, so the claim is
        // exhibited under a letter nothing holds and renamed back.
        let binder = self.binder_var(&said)?;
        let mut apart = None;
        let mut renamed = None;
        if witness.split_whitespace().any(|t| t == binder.as_str()) {
            let Some(letter) = self.unheld(&[&whole, &self.to_term(&witness)]) else {
                return Err(
                    self.defect(step.line, "no letter left to exhibit the witness by")
                );
            };
            let spare = self.rpn(&letter);
            stands = format!("{spare} cv");
            let mut put = Binding::new();
            put.insert(
                whole.children()[1].variable().unwrap_or("").to_string(),
                letter.clone(),
            );
            body = body.substitute(&put);
            renamed = Some(Term::apply(
                "wrex",
                vec![body.clone(), letter, domain.clone()],
            ));
            apart = Some(spare);
        }
        let shape = self.names_kept(|me| -> Checked<Node> {
            me.names.insert(said.clone(), stands.clone());
            me.freeze(&node.children[2])
        })?;
        let at = t!(stands, witness, "wceq");
        let identity = pf!(self.b; at, "id");
        let (here, instance) =
            match self.rewrite(&shape, &stands, &witness, &at, &identity)? {
                Built(made) => made,
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "the witness stands nowhere in the claim: {}",
                            self.say(&d)
                        ),
                    ));
                }
            };
        let known = self.supplied(Some(step), scope, facts)?;
        let member = t!(witness, self.rpn(&domain), "wcel");
        // What is left is that the witness lies in the domain and that the
        // body holds of it, and both are the text's to supply.
        let mut shown = Vec::new();
        for want in [&member, &here] {
            match self.settle(&self.to_term(want), scope, &known, 3, None, None)? {
                Built(p) => shown.push(p),
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "exhibiting that witness wants {}, which step {} does not supply: {}",
                            self.render(want),
                            fmt(&step.number),
                            self.say(&d)
                        ),
                    ));
                }
            }
        }
        let spare = apart.clone().unwrap_or(binder);
        let claimed = match &renamed {
            Some(r) => self.rpn(r),
            None => term.to_string(),
        };
        let both = pf!(self.b; scope, member, here, shown[0], shown[1], "jca");
        let made = pf!(self.b; scope, t!(member, here, "wa"), claimed, both,
            self.rpn(&body), here, spare, witness, self.rpn(&domain), instance, "rspcev", "syl");
        let Some(renamed) = renamed else {
            return Ok(Built(made));
        };
        let Some(back) = self.renaming(&renamed, &whole)? else {
            return Err(self.defect(
                step.line,
                "the renamed claim does not read back as the claim",
            ));
        };
        Ok(Built(self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &claimed, "ch" => term},
            &[&made, &back],
        )))
    }

    /// What stands where `mark` does, in a line shaped like the pattern.
    fn witness_in(&self, pattern: &Term, actual: &Term, mark: &str) -> Option<String> {
        let marks: BTreeSet<String> = std::iter::once(mark.to_string()).collect();
        self.witnesses_in(pattern, actual, &marks)
            .map(|found| found[mark].clone())
    }

    /// What stands where each of `marks` does, or nothing unless all do: the
    /// search runs over the claim's parts, aligning each against the whole
    /// of the line, starting only at a part built the same way the line is.
    pub fn witnesses_in(
        &self,
        pattern: &Term,
        actual: &Term,
        marks: &BTreeSet<String>,
    ) -> Option<IndexMap<String, String>> {
        let mut found = IndexMap::new();
        if pattern.label() == actual.label()
            && self.aligned(pattern, actual, marks, &mut found, &IndexMap::new())
            && found.len() == marks.len()
        {
            return Some(found);
        }
        for child in pattern.children() {
            if let Some(got) = self
                .witnesses_in(child, actual, marks)
                .filter(|g| !g.is_empty())
            {
                return Some(got);
            }
        }
        None
    }

    /// Whether these agree everywhere but the marked places. A letter each
    /// binds at the same place may differ, and is the same letter below it.
    fn aligned(
        &self,
        pattern: &Term,
        actual: &Term,
        marks: &BTreeSet<String>,
        found: &mut IndexMap<String, String>,
        paired: &IndexMap<String, String>,
    ) -> bool {
        let here = self.rpn(pattern);
        if marks.contains(&here) {
            let was = self.rpn(actual);
            return *found.entry(here).or_insert_with(|| was.clone()) == was;
        }
        if pattern.variable().is_some() || actual.variable().is_some() {
            let p = pattern
                .variable()
                .map(|v| paired.get(v).map(String::as_str).unwrap_or(v));
            return p == actual.variable();
        }
        if pattern.label() != actual.label()
            || pattern.children().len() != actual.children().len()
        {
            return false;
        }
        // A class binds too.
        let label = pattern.label().unwrap_or("");
        let at = if lookup(rules::BOUND, label).is_some() {
            Some(1)
        } else {
            binder_at(label)
        };
        let mut inner = paired.clone();
        if let Some(at) = at {
            if pattern.children().len() > at {
                if let (Some(p), Some(a)) = (
                    pattern.children()[at].variable(),
                    actual.children()[at].variable(),
                ) {
                    inner.insert(p.to_string(), a.to_string());
                }
            }
        }
        pattern
            .children()
            .iter()
            .zip(actual.children())
            .all(|(a, b)| self.aligned(a, b, marks, found, &inner))
    }

    /// A definition used the other way: to conclude an existence claim, the
    /// witness read off the cited line by walking the shape the definition
    /// states against it.
    fn conclude(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let head = step.just.head.to_string();
        let named = instantiation(&step.just.text);
        let given = self.subject_given(&head, &named, step.line)?;
        let subject_node = self.read(&given)?;
        let subject = self.term(&subject_node)?;
        let var = self.spare_var()?;
        let (lemma, var, kernel, over) =
            self.names_kept(|me| -> Checked<(String, String, Node, String)> {
                // A definition may name more than the thing it is about.
                for (name, value) in instantiation(&step.just.text) {
                    let node = me.read(&value)?;
                    let term = me.term(&node)?;
                    me.names.insert(name, term);
                }
                let (lemma, var, kernel, _w, over, _left) =
                    me.definition(&head, &subject, Some(var))?;
                let kernel = me.freeze(&kernel)?;
                Ok((lemma, var, kernel, over))
            })?;
        // A step cites the lines it leans on, and only one of them says what
        // the witness is: the one whose claim is what the definition would say
        // of the witness it names, facing either way.
        let body = self.term(&kernel)?;
        let mark = format!("{var} cv");
        enum Source {
            Line(String),
            Known(String),
        }
        let mut candidates: Vec<(String, Source)> = step
            .just
            .refs
            .iter()
            .map(|r| {
                let line = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
                (line.term, Source::Line(r.clone()))
            })
            .collect();
        let mut known = Facts::new();
        if !step.requires.is_empty() {
            known = self.supplied(Some(step), scope, facts)?;
            for r in &step.requires {
                let said = self.claim_of(&r.fact)?;
                if known.has(&said) {
                    candidates.push((said.clone(), Source::Known(said)));
                }
            }
        }
        let mut chosen = None;
        for (said, source) in &candidates {
            let held = self.to_term(said);
            let mut witness = None;
            for shape in [Some(body.clone()), self.turned(&body)] {
                if let Some(shape) = shape {
                    witness = self.witness_in(&self.to_term(&shape), &held, &mark);
                }
                if witness.is_some() {
                    break;
                }
            }
            let Some(witness) = witness else {
                continue;
            };
            let substituted = self.substituted(&kernel, &mark, &witness)?;
            let here = self.term(&substituted)?;
            if *said == here || Some(said.clone()) == self.turned(&here) {
                chosen = Some((said.clone(), source, witness, here));
                break;
            }
        }
        let Some((said, source, witness, here)) = chosen else {
            return Err(self.defect(step.line, "no cited line names a witness"));
        };
        let at = t!(format!("{var} cv"), witness, "wceq");
        let identity = pf!(self.b; at, "id");
        let instance = match self.rewrite(
            &kernel,
            &format!("{var} cv"),
            &witness,
            &at,
            &identity,
        )? {
            Built((_built, instance)) => instance,
            Declined(d) => {
                return Err(self.defect(
                    step.line,
                    format!(
                        "the witness stands nowhere in the claim: {}",
                        self.say(&d)
                    ),
                ));
            }
        };
        let ex = t!(body, var, over, "wrex");
        let member = t!(witness, over, "wcel");
        let p_member = self.required(step, &member, scope, facts)?;
        // A line proved before a block opened holds inside it too, and the
        // scope's own copy is what says so where the step sits.
        let mut p_cited = match source {
            Source::Line(r) => {
                let line = lines.get(r).unwrap();
                facts.get(&line.term).unwrap_or(line.proof)
            }
            Source::Known(said) => known.get(said).unwrap(),
        };
        if said != here {
            let was = self.to_term(&said);
            let (a, b) = (self.rpn(&was.children()[0]), self.rpn(&was.children()[1]));
            p_cited = pf!(self.b; scope, a, b, p_cited, "eqcomd");
        }
        let both = pf!(self.b; scope, member, here, p_member, p_cited, "jca");
        let p_ex = pf!(self.b; scope, t!(member, here, "wa"), ex, both, body, here, var, witness, over, instance, "rspcev", "syl");
        let (made, _) = take!(self.unfolding(
            step,
            &lemma,
            term,
            Some(&ex),
            Some(&var),
            Some(&over),
            scope,
            facts,
            None
        )?);
        Ok(Built(pf!(self.b; scope, term, ex, p_ex, made, "mpbird")))
    }

    /// A theorem cited: either set.mm supplies it or this corpus does.
    fn cite(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let _ = lines;
        match self.item_cited(&step.just.head.to_string()) {
            Item::Theorem(t) => self
                .cite_corpus(step, term, scope, facts, t, None)
                .map(Built),
            Item::Record(r) => self.cite_library(step, term, scope, facts, r),
        }
    }

    /// Apply the set.mm theorem the item's `target` names, its variables read
    /// off matching its conclusion against the claim, or given by the item's
    /// `with` where the conclusion is the claim said differently.
    fn cite_library(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        item: &'a Record,
    ) -> Checked<Route<Proof>> {
        let labels = targets::clauses(item);
        if labels.is_empty() {
            // Nothing in the library has its shape, so the file states what
            // it claims and lists it.
            return self
                .assume_item(step, term, scope, facts, item, None)
                .map(Built);
        }
        let seed = self.filling(step, item, None)?;
        match self.by_clause(&labels, term, scope, facts, step, Some(&seed))? {
            Built(p) => Ok(Built(p)),
            Declined(_) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {} reaches what step {} claims",
                    step.just.head,
                    fmt(&step.number)
                ),
            )),
        }
    }

    /// What one clause of an item gives, or what several give together, one
    /// to a sentence of the claim.
    fn by_clause(
        &mut self,
        labels: &[String],
        term: &str,
        scope: &str,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        for label in labels {
            let found = self.apply_lemma(
                label,
                &self.to_term(term),
                scope,
                facts,
                Some(step),
                true,
                seed,
            )?;
            if !found.is_declined() {
                return Ok(found); // otherwise not this `then` group
            }
        }
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return Ok(Route::no("no clause of the item reaches the claim"));
        }
        let halves: Vec<String> = node.children().iter().map(|c| self.rpn(c)).collect();
        let mut made = Vec::new();
        for one in &halves {
            made.push(self.by_clause(labels, one, scope, facts, step, seed)?);
        }
        let mut proofs = Vec::new();
        for one in made {
            proofs.push(take!(one));
        }
        Ok(Built(
            pf!(self.b; scope, halves[0], halves[1], proofs[0], proofs[1], "jca"),
        ))
    }

    /// What a `with` target says the lemma's variables stand for, read under
    /// the citation's instantiation.
    fn filling(
        &mut self,
        step: &Step,
        item: &'a Record,
        cites: Option<&str>,
    ) -> Checked<Binding> {
        let (_label, fills) = targets::lemma(item);
        if fills.is_empty() {
            return Ok(Binding::new());
        }
        self.names_kept(|me| -> Checked<Binding> {
            for (name, value) in instantiation(cites.unwrap_or(&step.just.text)) {
                let node = me.read(&value)?;
                let term = me.term(&node)?;
                me.names.insert(name, term);
            }
            let mut out = Binding::new();
            for (name, formula) in &fills {
                let node = me.read(formula)?;
                let term = me.term(&node)?;
                out.insert(name.clone(), me.to_term(&term));
            }
            Ok(out)
        })
    }

    /// The variables the file this corpus wrote for a theorem declares, read
    /// off the statement as this proof has it: a class for each `let`, and
    /// whatever each binder takes.
    fn cited_floats(
        &self,
        said: &[String],
        classes: &IndexMap<String, String>,
    ) -> Vec<String> {
        let mut bound: BTreeSet<String> = BTreeSet::new();
        let mut rest: Vec<Term> = said.iter().map(|s| self.to_term(s)).collect();
        while let Some(node) = rest.pop() {
            let label = node.label().unwrap_or("");
            if matches!(label, "wral" | "wrex" | "wreu") {
                bound.insert(self.rpn(&node.children()[1]));
            }
            if label == "cmpt" || label == "wal" {
                let at = if label == "cmpt" { 0 } else { 1 };
                bound.insert(self.rpn(&node.children()[at]));
            }
            if label == "csu" {
                bound.insert(self.rpn(&node.children()[2]));
            }
            rest.extend(node.children().iter().cloned());
        }
        bound.extend(classes.keys().cloned());
        let mut out: Vec<String> = bound.into_iter().collect();
        out.sort_by_key(|label| {
            self.b.forder.get(label).copied().unwrap_or(usize::MAX)
        });
        out
    }

    /// What a citation pushes, in the order the cited theorem's own statement
    /// declares: what it binds decides both the order and how many. None
    /// where that statement is not known.
    fn cited_pushes(
        &self,
        name: &str,
        binds: &IndexMap<String, String>,
        mine: &[String],
    ) -> Option<Vec<String>> {
        let said = (self.statements)(name)?;
        let mut theirs: Vec<String> = Vec::new();
        for token in said.split_whitespace() {
            if let Some(label) = self.b.flabel.get(token) {
                if !theirs.contains(label) {
                    theirs.push(label.clone());
                }
            }
        }
        theirs.sort_by_key(|label| {
            self.b.forder.get(label).copied().unwrap_or(usize::MAX)
        });
        let mut spare: std::collections::VecDeque<&String> = mine
            .iter()
            .filter(|v| !binds.contains_key(*v) && self.typecode(v) == "setvar")
            .collect();
        let mut out = Vec::new();
        for label in &theirs {
            if let Some(b) = binds.get(label) {
                out.push(b.clone());
            } else if self.typecode(label) == "setvar" && !spare.is_empty() {
                out.push(spare.pop_front().unwrap().clone());
            } else {
                return None;
            }
        }
        Some(out)
    }

    /// Apply a theorem this corpus proves, as this elaborator states it: its
    /// hypotheses became the antecedent of one implication, so citing it is
    /// conjoining the facts the step supplies and applying one label.
    fn cite_corpus(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        other: &'a Theorem,
        cites: Option<&str>,
    ) -> Checked<Proof> {
        let full = other.qualified();
        if !self.cited.contains(&full) {
            self.cited.push(full.clone());
        }
        let mut spare: std::collections::VecDeque<&str> =
            CLASS_NAMES.iter().copied().collect();
        let written: IndexMap<String, String> =
            instantiation(cites.unwrap_or(&step.just.text))
                .into_iter()
                .collect();
        let claim_text = step.claim_text();
        let (binds, wanted, whole) = self.names_and_sets_kept(
            |me| -> Checked<(IndexMap<String, String>, Vec<String>, String)> {
                let saved = me.names.clone();
                let mut binds: IndexMap<String, String> = IndexMap::new();
                for h in &other.hypotheses {
                    let node = me.read(&hypothesis_body(h.kind.as_str(), &h.text))?;
                    // `let X be a set` names a class as surely as `let n ∈ ℕ`
                    // does, and the name is in the same place.
                    if h.kind == Intro::Let
                        && matches!(
                            node.notation.as_str(),
                            "membership" | "is-a-set" | "conjunction" | "function-type"
                        )
                    {
                        let name = subject_of(&node).text.clone();
                        let theirs = spare
                            .pop_front()
                            .expect("a class for each let")
                            .to_string();
                        // A hypothesis the citation does not name stands for what
                        // the citing proof calls by the same word.
                        if let Some(value) = written.get(&name) {
                            let v = me.read(value)?;
                            let term = me.term(&v)?;
                            me.names.insert(name.clone(), term);
                        } else if !saved.contains_key(&name) {
                            me.names.insert(name.clone(), theirs.clone());
                        }
                        binds.insert(theirs, me.names[&name].clone());
                    }
                }
                // Read in its own file's definitions, as its conclusion is below.
                let wanted = me.in_its_names(
                    Item::Theorem(other),
                    |me| -> Checked<Vec<String>> {
                        let mut out = Vec::new();
                        for h in &other.hypotheses {
                            let node =
                                me.read(&hypothesis_body(h.kind.as_str(), &h.text))?;
                            out.push(me.term(&node)?);
                        }
                        Ok(out)
                    },
                )?;
                // The step may claim one sentence of a conclusion that says
                // several, or the conclusion in other words.
                let stated = me.in_its_names(Item::Theorem(other), |me| {
                    me.claim_of(&other.conclusion)
                })?;
                let mut whole = if stated == term || me.rebound(&stated, term) {
                    term.to_string()
                } else {
                    stated.clone()
                };
                if me.sentences(&other.conclusion).len()
                    > me.sentences(&claim_text).len()
                {
                    whole = stated;
                }
                Ok((binds, wanted, whole))
            },
        )?;
        // A cited theorem asks for what it asks for, and a hypothesis a
        // reader would not think to write as a line is written as a
        // `requires` instead, or settled as a side condition.
        let known = self.supplied(Some(step), scope, facts)?;
        for one in &wanted {
            if known.has(one) {
                continue;
            }
            match self.settle(&self.to_term(one), scope, &known, 3, None, None)? {
                Built(p) => known.set(one.clone(), p),
                Declined(_) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "nothing supplies {}, which {} assumes",
                            self.render(one),
                            step.just.head
                        ),
                    ));
                }
            }
        }
        let mut pair = wanted.first().cloned();
        let mut proof = pair.as_ref().map(|p| known.get(p).unwrap());
        for extra in wanted.iter().skip(1) {
            let held = known.get(extra).unwrap();
            let p = pair.clone().unwrap();
            proof = Some(pf!(self.b; scope, p, extra, proof.unwrap(), held, "jca"));
            pair = Some(t!(p, extra, "wa"));
        }
        // A variable the file declares and this proof says nothing about is
        // one the statement binds, and it stands for itself.
        let mut said = wanted.clone();
        said.push(whole.clone());
        let mine = self.cited_floats(&said, &binds);
        let pushed = self
            .cited_pushes(&full, &binds, &mine)
            .filter(|p| !p.is_empty())
            .unwrap_or_else(|| {
                mine.iter()
                    .map(|l| binds.get(l).cloned().unwrap_or(l.clone()))
                    .collect()
            });
        let cited = label_of(
            &full,
            &self.b.sigs,
            &self.thm.path,
            self.thm.line,
            &proved_here(self.items),
        )?;
        // The cited theorem is proved in another file, so the library does
        // not hold it; what it takes is what is being pushed. Kept apart from
        // the signatures, which `label_of` reads.
        if !self.b.arities.contains_key(&cited) {
            self.b.arities.insert(
                cited.clone(),
                Signature {
                    label: cited.clone(),
                    kind: Kind::Theorem,
                    statement: vec!["|-".to_string()],
                    floats: (0..pushed.len())
                        .map(|n| ("class".to_string(), format!("{cited}.{n}")))
                        .collect(),
                    essentials: Vec::new(),
                    disjoint: BTreeSet::new(),
                },
            );
        }
        // A theorem that assumes nothing states its conclusion outright.
        let mut parts: Vec<crate::mm::spell::Part> = Vec::new();
        let proof = match (&pair, &proof) {
            (Some(pair), Some(given)) => {
                parts.push(super::part(scope));
                parts.push(super::part(pair));
                parts.push(super::part(&whole));
                parts.push(super::part(given));
                parts.extend(pushed.iter().map(|p| super::part(p)));
                parts.push(super::part(&cited));
                parts.push(super::part("syl"));
                self.b.proof(&parts)
            }
            _ => {
                parts.push(super::part(&whole));
                parts.push(super::part(scope));
                parts.extend(pushed.iter().map(|p| super::part(p)));
                parts.push(super::part(&cited));
                parts.push(super::part("a1i"));
                self.b.proof(&parts)
            }
        };
        if term == whole {
            return Ok(proof);
        }
        let taken = Facts::new();
        taken.set(whole.clone(), proof.clone());
        self.unpack(&whole, &proof, scope, &taken, 4);
        if let Some(p) = taken.get(term) {
            return Ok(p);
        }
        for (one, shown) in taken.entries() {
            if let Built(alike) =
                self.same(&self.to_term(&one), &self.to_term(term), scope, facts, None)?
            {
                return Ok(pf!(self.b; scope, one, term, shown, alike, "mpbid"));
            }
        }
        Err(self.defect(
            step.line,
            format!(
                "{} does not conclude what step {} claims",
                step.just.head,
                fmt(&step.number)
            ),
        ))
    }
}

/// How a step is expanded, by what its justification opens with.
enum Method {
    Named(String),
    TakeDefinition,
    Reading(Way),
    UnfoldEquation,
    Cite,
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

/// set.mm and the corpus's library, as every theorem of a build reads them.
pub struct Library {
    /// set.mm and `proved.mm` together, held once and shared by every
    /// theorem, each of which adds its own labels in a [`Layered`] table.
    pub sigs: Rc<Signatures>,
    /// The labels `proved.mm` holds.
    pub provided: BTreeSet<String>,
    /// How many assertions set.mm holds, which the file header says.
    pub size: usize,
    /// set.mm's SHA-256, which the file header says.
    pub digest: String,
}

impl Library {
    /// The library read from set.mm and, where it has been built, the
    /// corpus's `proved.mm`.
    pub fn read(
        setmm: &std::path::Path,
        proved: Option<&std::path::Path>,
    ) -> Checked<Library> {
        let text = std::fs::read_to_string(setmm).map_err(|e| {
            Problem::new(
                setmm.display().to_string(),
                0,
                format!("cannot read set.mm: {e}"),
            )
        })?;
        let proved = match proved {
            Some(p) => Some(std::fs::read_to_string(p).map_err(|e| {
                Problem::new(p.display().to_string(), 0, e.to_string())
            })?),
            None => None,
        };
        Ok(Library::from_texts(&text, proved.as_deref()))
    }

    /// The library from set.mm's text and, where there is one, `proved.mm`'s.
    pub fn from_texts(setmm: &str, proved: Option<&str>) -> Library {
        let digest = {
            use sha2::{Digest, Sha256};
            Sha256::digest(setmm.as_bytes())
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect()
        };
        let provided: BTreeSet<String> = match proved {
            Some(p) => crate::mm::read_texts(&[p]).into_keys().collect(),
            None => BTreeSet::new(),
        };
        let mut texts = vec![setmm];
        texts.extend(proved);
        let sigs = crate::mm::read_texts(&texts);
        let size = sigs.len() - provided.len();
        Library {
            sigs: Rc::new(sigs),
            provided,
            size,
            digest,
        }
    }
}

/// The constants the corpus introduces, declared on the library: they are
/// not in it, so a notation that reaches one needs them declared before it is
/// read. They are the statements `definitions.mm` writes, built here rather
/// than read back from it.
fn declare_constants(sigs: &mut Layered, records: &[Record]) -> Checked<()> {
    for one in super::definitions::definitions(records, sigs)? {
        let rendered = crate::mm::library::render(&one.body, sigs);
        sigs.insert(
            format!("c{}", one.token),
            Signature {
                label: format!("c{}", one.token),
                kind: Kind::Axiom,
                statement: vec!["class".to_string(), one.token.clone()],
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
        let mut statement = vec!["|-".to_string(), one.token.clone(), "=".to_string()];
        statement.extend(rendered.split_whitespace().map(String::from));
        sigs.insert(
            format!("df-{}", one.token),
            Signature {
                label: format!("df-{}", one.token),
                kind: Kind::Axiom,
                statement,
                floats: Vec::new(),
                essentials: Vec::new(),
                disjoint: BTreeSet::new(),
            },
        );
    }
    Ok(())
}

/// What an elaboration may be asked to do differently.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// The search offered every fact in scope, as it was before a step's
    /// proof was held to rest only on what the step names. Only the test of
    /// that rule turns it on, to see that the rule afterwards still catches
    /// what the search would have taken.
    pub whole_scope_offered: bool,
}

/// One theorem's elaborated file, and the statement it proves, which a
/// theorem citing this one reads for the order of what it pushes.
pub struct Elaborated {
    pub text: String,
    pub statement: String,
}

/// Elaborate one theorem of the corpus into its file.
///
/// `statements` gives the statement a cited theorem's file proves, where it
/// is known.
pub fn elaborate(
    corpus: &Corpus,
    g: &Grammar,
    items: &IndexMap<String, Item>,
    thm: &Theorem,
    library: &Library,
    statements: &dyn Fn(&str) -> Option<String>,
    options: Options,
) -> Checked<Elaborated> {
    let env = crate::sorts::Env {
        g,
        scopes: &corpus.scopes,
    };
    let sorts_now = sorts_in_scope(thm, env);
    let mut sigs = Layered::new(Rc::clone(&library.sigs));
    declare_constants(&mut sigs, &corpus.records)?;
    let mut work = Elaborator::new(
        thm,
        g,
        items,
        sigs,
        &corpus.records,
        &corpus.scopes,
        sorts_now,
        statements,
    );
    work.whole_scope = options.whole_scope_offered;
    let (goal, hypotheses, mut proof) = work.run()?;
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
        "$( {}, elaborated from {} by parley/elaborate.py.\n",
        thm.qualified(),
        thm.path
    ));
    if work.axioms.is_empty() {
        out.push_str("   Nothing here is assumed.\n");
    } else {
        out.push_str("   Everything is built except the statements below, which are\n");
        out.push_str("   taken as the readable lines state them: a closure method\n");
        out.push_str("   the elaborator does not expand, or a definition the\n");
        out.push_str("   database gives no target for.\n");
    }
    out.push_str(&format!(
        "   Checked against a set.mm of {} assertions, sha256\n   {}. $)\n",
        thousands(library.size),
        library.digest
    ));
    out.push('\n');
    // A theorem this corpus proves is cited as one label, so the file that
    // elaborated it is read first and the rest comes in through it.
    for name in &work.cited {
        out.push_str(&format!("$[ {name}.mm $]\n"));
    }
    if work.cited.is_empty() {
        // proved.mm includes the definitions, so a proof that reaches one of
        // its labels needs only the one include.
        let wants = used.iter().any(|l| library.provided.contains(&**l));
        let file = if wants {
            "stdlib/proved"
        } else {
            "stdlib/definitions"
        };
        out.push_str(&format!("$[ {file}.mm $]\n"));
    }
    out.push('\n');
    for (label, statement) in &work.axioms {
        out.push_str(&format!("{label} $a {statement} $.\n"));
    }
    if !work.axioms.is_empty() {
        out.push('\n');
    }
    // Every variable the proof touches has to be disjoint from every other
    // it binds: a name it binds from everything else.
    let sigs = &work.b.sigs;
    let held: Vec<&str> = used
        .iter()
        .map(|l| &**l)
        .filter(|t| sigs.get(t).is_some_and(|s| s.kind == Kind::Float))
        .collect();
    let mut bound: Vec<String> = held
        .iter()
        .filter(|t| sigs[**t].statement[0] == "setvar")
        .map(|t| sigs[*t].statement[1].clone())
        .collect();
    bound.sort();
    let mut free: Vec<String> = held
        .iter()
        .filter(|t| sigs[**t].statement[0] != "setvar")
        .map(|t| sigs[*t].statement[1].clone())
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
        Some(a) => format!("( {} -> {} )", work.render(a), work.render(&goal)),
        None => work.render(&goal),
    };
    let mut mandatory: Vec<String> = says
        .split_whitespace()
        .filter_map(|t| work.b.flabel.get(t).cloned())
        .collect::<BTreeSet<String>>()
        .into_iter()
        .collect();
    mandatory.sort_by_key(|one| work.b.forder.get(one).copied().unwrap_or(usize::MAX));
    out.push_str(&format!("  {label} $p |- {says} $=\n"));
    out.push_str(&format!(
        "    {} $.\n",
        compressed(root, &kinds, &mandatory)
    ));
    out.push_str("$}\n");
    Ok(Elaborated {
        text: out,
        statement: format!("|- {says}"),
    })
}

/// The statement a written file proves, read off its `$p` line: what a
/// theorem citing it pushes is decided by what that statement binds.
pub fn statement_of(text: &str) -> Option<String> {
    for line in text.lines() {
        if let Some((_, rest)) = line.split_once(" $p ") {
            return Some(rest.split("$=").next().unwrap_or("").to_string());
        }
    }
    None
}
