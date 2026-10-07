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

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use indexmap::IndexMap;

use super::field::{self, Verdict};
use super::linear;
use super::matcher::ChainLink;
use super::provenance::{item_clauses, requirement};
use super::reading::{hypothesis_body, is_subgroup, subject_of, CLASS_NAMES};
use super::state::{
    fit, names_of, number_of, Binding, Block, Closer, Elaborator, Vars,
};
use super::tables::Leaf;
use super::{Facts, Line, Lines};
use crate::binds;
use crate::citing::{self, asked, claimed_member, filled, finished, obtained, Parts};
use crate::corpus::proof::{requires_as_step, requires_item, Requires};
use crate::corpus::{
    define_parts, fmt, item_prefix, outermost, references, Corpus, DefineParts, Intro,
    Item, Record, Step, Theorem,
};
use crate::formula::{Grammar, Node};
use crate::matching::{expand, instantiation, Binding as NodeBinding, Defined};
use crate::mm::compress::{compressed, labels as compress_labels, shapes_of};
use crate::mm::kernel::{Syntax, Term};
use crate::mm::library::thousands;
use crate::mm::spell::Proof;
use crate::mm::{Kind, Layered, Lookup, Signature, Signatures};
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::rules::{self, lookup};
use crate::sorts::{
    cited_defines, file_definitions, said_by_line, sorts_in_scope, supplied_by, unlabel,
};
use crate::targets;
use crate::text::repr;
use crate::{pf, regex, t, take};

/// Why a side of a step citing a define is not what the define names.
const NAMES_NO_DEFINE: &str = "this side names no define";

/// What a requires line's record asks of it (`Elaborator::asked_here`).
pub(crate) struct AskedHere<'a> {
    /// The record the line cites, in whose names the hypotheses are terms.
    pub item: &'a Record,
    /// Its hypotheses, each letter the citation fixes put in.
    pub hypotheses: Vec<Node>,
}

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

/// What this elaborator calls a theorem it has written out: its full name,
/// file and theorem, with a dot where the name has a slash, which Metamath
/// does not allow in a label: `proofs.sqrt2-irrational.even-square`.
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
    let label = crate::text::spelt_in_ascii(&name.replace('/', "."));
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
        // about, and that formula is a scope: which one is chosen below,
        // once the lemma's other variables are fixed.
        let deduced = asks.first().and_then(|a| a.variable().map(String::from));
        if let Some(v) = &deduced {
            binding.insert(v.clone(), self.to_term(scope));
            asks.remove(0);
        }
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
        // The scope is the innermost one the lemma's disjointness conditions
        // allow, as for any lemma applied (`allowed`), and what it gives is
        // carried in to the step's.
        // Where no scope allows it, the letters it keeps apart from its scope
        // and the scope spells are moved to letters nothing holds, as a
        // claim's are (`over_other_letters`), and the side the step holds is
        // renamed to them below.
        let (mut at, mut frame) = (scope.to_string(), None);
        let mut moved = Binding::new();
        if let Some(v) = &deduced {
            let mut open = binding.clone();
            open.shift_remove(v);
            let (mut where_, mut index) = self.allowed(&sig, &open);
            if where_.is_declined() {
                let spelt: BTreeSet<&str> = scope.split_whitespace().collect();
                let letters: Vec<String> = sig
                    .disjoint
                    .iter()
                    .flat_map(|(a, b)| [(a, b), (b, a)])
                    .filter(|(_, other)| *other == v)
                    .filter_map(|(one, _)| open.get(one.as_str()))
                    .filter_map(|t| t.variable().map(String::from))
                    .filter(|l| spelt.contains(self.float_of(l).as_str()))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                let avoid: Vec<Term> = [self.to_term(scope), whole.clone()]
                    .into_iter()
                    .chain(open.values().cloned())
                    .collect();
                if let Some(m) =
                    self.unheld_for(letters, &avoid.iter().collect::<Vec<_>>())
                {
                    moved = m;
                    open = open
                        .into_iter()
                        .map(|(k, t)| (k, t.substitute(&moved)))
                        .collect();
                    (where_, index) = self.allowed(&sig, &open);
                }
            }
            at = take!(where_);
            frame = index;
            binding = open;
            binding.insert(v.clone(), self.to_term(&at));
        }
        let at_facts = match frame {
            Some(f) => self.frames_facts(f, facts),
            None => facts.clone(),
        };
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
            conditions.push(self.prove_essential(&asked, &at, &at_facts)?);
        }
        let mut proofs = Vec::new();
        for one in conditions {
            proofs.push(take!(one));
        }
        let mut applied = self.b.ap(lemma, &binds, &proofs.iter().collect::<Vec<_>>());
        // The lemma unfolds to its own wording, which need not be the
        // text's: what it gives is built first, and the text's wording is
        // reached from it.
        if let (Some(h), Some(v)) = (&held, var) {
            let var_term = self.var_of(v);
            binding.insert(h.clone(), var_term);
        }
        if let (Some(_), Some(f)) = (&deduced, frame) {
            let gives = self.rpn(&whole.children()[1].substitute(&binding));
            applied = self.carry(applied, &gives, f);
        }
        let given = self.rpn(&reads.children()[1].substitute(&binding));
        let near = if moved.is_empty() {
            left.to_string()
        } else {
            self.rpn(&reads.children()[0].substitute(&binding))
        };
        let says = t!(near, given, "wb");
        let proof = if deduced.is_some() && asks.is_empty() {
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
        // The side the step holds, renamed to the letters the lemma was
        // applied over, closed.
        let proof = if near == left {
            proof
        } else {
            let (was, now) = (self.to_term(left), self.to_term(&near));
            let Some(renamed) = self.renaming(&was, &now)? else {
                return Ok(Route::no("the side the step holds is not renamed apart"));
            };
            let first = pf!(self.b; t!(left, near, "wb"), scope, renamed, "a1i");
            self.chained(
                scope,
                &[
                    ChainLink {
                        from: was,
                        to: now.clone(),
                        proof: first,
                    },
                    ChainLink {
                        from: now,
                        to: self.to_term(&given),
                        proof,
                    },
                ],
            )
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
        // it without naming it. A define is not one: a step that uses what it
        // says cites it, as it cites any line it uses.
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
                    || text.contains(" be a polynomial")
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
        let id = pf!(self.b; scope, "id");
        self.know(&facts, scope.clone(), id);
        for extra in terms.iter().skip(1) {
            let wider = t!(scope, extra, "wa");
            let weaken = pf!(self.b; scope, extra, "simpl");
            let lifted =
                facts.rebased(|k, v| pf!(self.b; wider, scope, k, weaken, v, "syl"));
            let simpr = pf!(self.b; scope, extra, "simpr");
            self.know(&lifted, extra.clone(), simpr);
            facts = lifted;
            scope = wider;
        }
        // Each hypothesis stands for itself, and is sealed before it is taken
        // apart so that what it says in pieces is still what it says.
        let hypotheses = self.thm.hypotheses.clone();
        for (h, t) in hypotheses.iter().zip(&terms) {
            let Some(label) = h.label.clone().filter(|l| !l.is_empty()) else {
                continue;
            };
            if let Some(held) = self.held(&facts, t, &scope)? {
                let sealed = self.seal(held, &label);
                self.know(&facts, t.clone(), sealed);
            }
        }
        // A hypothesis may say several things at once, and each of them is a
        // fact the proof may lean on without a step to take it apart.
        for extra in &terms {
            if let Some(held) = self.held(&facts, extra, &scope)? {
                self.unpack(extra, &held, &scope, &facts, 4);
            }
        }
        let more = self.sethoods(&nodes, &terms, &scope, &facts)?;
        self.sorts.extend(more);

        // Each keeps the sentence it was read from, as a block's opening
        // line does, so a step may substitute into it.
        let lines = Lines::new();
        for ((h, t), node) in hypotheses.iter().zip(&terms).zip(&nodes) {
            let proof = self.held(&facts, t, &scope)?.expect("a hypothesis's fact");
            lines.set(
                h.label.clone().unwrap_or_default(),
                Line {
                    term: t.clone(),
                    proof,
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
                closers = self.settle_claimed(&mut done, closers, None)?;
                (scope, facts, closers) =
                    self.close_block(&mut done, &facts, closers, &scope)?;
                Self::hand_up(&done, &mut blocks);
            }
            // A step in a case sits under the case's assumption, and one in
            // an induction's step part under what that part opens with, where
            // the part is new.
            let inducts = |b: &Block| b.owner.just.head.to_string() == "induction";
            let entering = match (blocks.last(), step.part) {
                (Some(b), Some(part)) => {
                    (!b.assumed.is_empty() || inducts(b)) && b.entered != Some(part)
                }
                _ => false,
            };
            if entering {
                let mut block = blocks.pop().unwrap();
                closers = self.settle_claimed(&mut block, closers, step.part)?;
                closers = self.end_case(&mut block, closers)?;
                let part = step.part.unwrap();
                (scope, facts) = if inducts(&block) {
                    self.enter_induction_part(&mut block, part)?
                } else {
                    self.enter_case(&mut block, part)?
                };
                block.case_opened_at = Some(closers.len());
                blocks.push(block);
            }
            // Any define standing above this step, now that the block and
            // the case it sits in are open and the names it leans on are in
            // hand: a define written inside a case is the case's.
            (scope, facts, closers) =
                self.define(step.line, &scope, &facts, closers)?;
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
            // A step contradicting a line closes a contradiction block on the
            // two of them, as its last pair.
            if let (Some(other), true) =
                (&step.just.contradicting, self.in_contradiction)
            {
                let said = self.lines.get(other).map(|l| l.term).unwrap_or_default();
                self.contradicted = Some(said);
            }
            // A step that says its claim is impossible is its own opposite:
            // `arithmetic` works the claim out, refuses one it does not find
            // false, and proves its denial, which stands as the line it
            // contradicts.
            let denied = if step.impossible {
                let last = self.last.clone().expect("a step's number");
                let held = self.lines.get(&last).expect("the step's line");
                let negated = t!(held.term, "wn");
                let what = format!(
                    "step {} says {} is impossible",
                    fmt(&step.number),
                    step.claim_text()
                );
                let why = match field::decide_closed(&self.to_term(&negated)) {
                    Built(Verdict::Holds(true)) => None,
                    Built(Verdict::Holds(false)) => Some("which is true".to_string()),
                    Built(Verdict::Unworked(why)) => Some(format!("which {why}")),
                    Declined(_) => {
                        Some("which is not a fact about numerals alone that arithmetic decides".into())
                    }
                };
                if let Some(why) = why {
                    return Err(self.defect(step.line, format!("{what}, {why}")));
                }
                let proof = self.closed_fact(&negated, &scope, &facts, &what, None)?;
                self.know(&facts, negated.clone(), proof.clone());
                if self.in_contradiction {
                    self.contradicted = Some(negated.clone());
                }
                Some(proof)
            } else {
                None
            };
            if let (Some(part), Some(block)) = (step.part, blocks.last_mut()) {
                let last = self.last.clone().expect("a step's number");
                let held = self.lines.get(&last).expect("the step's line");
                let (term, proof) = match (&step.just.contradicting, denied) {
                    // A case that cannot occur gives the block's claim from
                    // its line and the line it contradicts.
                    (Some(other), _) => {
                        let claim = self.claim_of(&block.owner.claim_text())?;
                        let made = self.by_opposites(
                            &step, &held, other, &claim, &scope, &facts,
                        )?;
                        (claim, made)
                    }
                    // Or from its line and that line shown false.
                    (None, Some(not)) => {
                        let claim = self.claim_of(&block.owner.claim_text())?;
                        let made = pf!(self.b; scope, held.term, claim, held.proof, not, "pm2.21dd");
                        (claim, made)
                    }
                    (None, None) => (held.term, held.proof),
                };
                block.parts.insert(part, (term, proof, scope.clone()));
            }
        }
        while let Some(mut done) = blocks.pop() {
            closers = self.settle_claimed(&mut done, closers, None)?;
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

    /// ( scope -> claim ) from a step's line and the line it contradicts, the
    /// one a formula and the other, or a sentence of it, that formula negated
    /// (`pm2.21dd`), found as a contradiction block finds its pair.
    fn by_opposites(
        &mut self,
        step: &Step,
        held: &Line,
        other: &str,
        claim: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Proof> {
        let lines = self.lines.clone();
        let Some(there) = lines.get(other) else {
            return Err(self.defect(step.line, format!("{other} is no line in scope")));
        };
        let pair = Facts::new();
        self.know(&pair, held.term.clone(), held.proof.clone());
        let carried = self.carried(other, facts, &lines);
        self.know(&pair, there.term.clone(), carried);
        let offered = [held.term.clone(), there.term.clone()];
        let Some((first, second, known)) = self.opposing(&offered, &pair, scope)?
        else {
            return Err(self.defect(
                step.line,
                format!("the step and {other} are not a formula and its negation"),
            ));
        };
        let one = self
            .held(&known, &first, scope)?
            .expect("a claim `opposing` found held");
        let two = self
            .held(&known, &second, scope)?
            .expect("a claim `opposing` found held");
        Ok(self.b.ap(
            "pm2.21dd",
            &binds! {"ph" => scope, "ps" => &first, "ch" => claim},
            &[&one, &two],
        ))
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
            // An obtain's requires lines cite items as any step's do.
            if self.answers.is_some() {
                self.list_asked(step)?;
            }
            return self.obtain(step, number, scope, facts, closers);
        }
        let claim = step.claim_text();
        let sentences = self.sentences(&claim);
        let node = self.read(sentences.last().map(String::as_str).unwrap_or(""))?;
        let term = self.claim_of(&claim)?;
        if self.said_back.is_some() {
            self.say_back(&sentences, step.line)?;
        }
        if self.answers.is_some() {
            let mut facts = sentences.clone();
            facts.extend(step.requires.iter().map(|r| r.fact.clone()));
            self.list_implied(step, &facts)?;
            self.list_asked(step)?;
        }
        let Some(how) = self.method_for(step, &term)? else {
            return Err(
                self.defect(step.line, format!("no expansion for {}", repr(&head)))
            );
        };
        let citing = std::mem::replace(
            &mut self.citing,
            step.just.refs.iter().cloned().collect(),
        );
        let lines = self.lines.clone();
        let made =
            self.by_method_written(&how, step, &node, &term, scope, facts, &lines);
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
        self.know(facts, term.clone(), proof.clone());
        self.know_turned(facts, &term, &proof, scope);
        // A line saying several things says each of them, only as deep as
        // the sentences the text wrote.
        if said.len() > 1 {
            self.unpack(&term, &proof, scope, facts, said.len() - 1);
        }
        Ok((scope.to_string(), facts.clone(), closers))
    }

    /// A requires line whose reason is a method or an item, proved as the
    /// step it would be (`requires_as_step`): the same method, chosen the
    /// same way, by the same route a numbered step takes. The step's
    /// requires lines above it, which `supplied` has proved and put in hand,
    /// are lines it cites (R2), offered as what `inequalities` combines from
    /// a line above: orders and equations. Two terms differing is taken only
    /// from a line the requires line cites (`METHODS.md`).
    pub fn as_a_step(
        &mut self,
        step: &Step,
        req: &Requires,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut at = requires_as_step(step, req, &self.thm.path)?;
        let lines = self.lines.copy();
        let labels = self.b.flabel.clone();
        for o in step.requires_above(req.line) {
            let node = self.read(&o.fact)?;
            let above = self.term(&node)?;
            let key = requirement(o.line);
            let sealed = self
                .held(facts, &above, scope)?
                .filter(|p| p.origin.contains(&key));
            let bound = linear::fact(&self.to_term(&above), &labels)
                .is_some_and(|f| f.how != linear::How::Ne);
            if let Some(proof) = sealed.filter(|_| bound) {
                lines.set(
                    key.clone(),
                    Line {
                        term: above,
                        proof,
                        sentences: vec![node],
                    },
                );
                at.just.refs.push(key);
            }
        }
        let node = self.read(&req.fact)?;
        let term = self.term(&node)?;
        let Some(how) = self.method_for(&at, &term)? else {
            return Ok(Route::no(format!("no expansion for {}", repr(&req.how))));
        };
        let kept = std::mem::replace(&mut self.lines, lines.clone());
        let citing =
            std::mem::replace(&mut self.citing, at.just.refs.iter().cloned().collect());
        let made =
            self.by_method_written(&how, &at, &node, &term, scope, facts, &lines);
        self.citing = citing;
        self.lines = kept;
        // What the step route says of the line it was given is said of the
        // requires line, whose step it is not.
        let made = made.map_err(|mut p| {
            if p.line.line == req.line {
                p.message = format!(
                    "the requires line {} of step {}, read as a step citing what it cites: {}",
                    str::trim(&req.fact),
                    fmt(&step.number),
                    p.message
                );
            }
            p
        });
        Ok(match made? {
            Built(Some(p)) => Built(p),
            Built(None) => Route::no("the requires line's method gives no proof"),
            Declined(d) => Declined(d),
        })
    }

    /// The method a step's justification names: one of the methods, or what
    /// citing its item comes to, by the item's kind and what it states. A
    /// requires line made a step (`requires_as_step`) is read the same way.
    fn method_for(&mut self, step: &Step, term: &str) -> Checked<Option<Method>> {
        let head = step.just.head.to_string();
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
        // Whether a step unfolds what it cites is read from the record: a
        // mundane definition is cited `mun:` and is unfolded all the same.
        let cited = item_prefix(&head);
        if how.is_none() && cited.is_some() && self.item_cited(&head).unfolds() {
            let Item::Record(item) = self.item_cited(&head) else {
                panic!("{head} is a definition of the database");
            };
            // A definition stated as a biconditional is used by unfolding
            // it; one stated as an equation is used by citing the lemma that
            // proves it. With no target it is read off the lines the step
            // cites, or is a defect (`take_definition`).
            how = Some(if !item.fields.contains_key("target") {
                Method::TakeDefinition
            } else if item.conclusions.iter().any(|(text, _)| text.contains('↔')) {
                Method::Reading(self.reading(item, term, step, None)?)
            } else {
                Method::UnfoldEquation
            });
        }
        if how.is_none() && cited.is_some() {
            how = Some(Method::Cite);
        }
        Ok(how)
    }

    /// A step's proof by the method its justification names, with its
    /// requires lines, as it is written or at a member of what it says
    /// "for all" of.
    #[allow(clippy::too_many_arguments)]
    fn by_method_written(
        &mut self,
        how: &Method,
        step: &Step,
        node: &Node,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        // Said of every member: an item whose conclusions say no "for all", a
        // define, and a method proving one fact, are applied at a member and
        // the claim generalised; the checker reads an item's citation the same
        // way (`SYNTAX.md`, a step said of every member). The requires lines
        // are then about that member, and are proved where it is in scope.
        let at_a_member = match how {
            Method::Cite | Method::Reading(_) => {
                !self.item_cited(&step.just.head.to_string()).says_for_all()
            }
            Method::Named(name) => ["define", "membership", "algebra", "inequalities"]
                .contains(&name.as_str()),
            _ => false,
        };
        let whole = self.to_term(term);
        if at_a_member && whole.variable().is_none() && whole.label() == Some("wral") {
            let letter = self.member_letter(step)?;
            let kids = whole.children();
            let (body, variable, over) =
                (kids[0].clone(), kids[1].clone(), kids[2].clone());
            // The member is fixed as the claim's own letter where neither the
            // scope nor a name holds it, and a spare otherwise, the claim then
            // proved over the spare and renamed back. Either is reserved, so
            // that no later step is handed it as a letter nothing holds; the
            // page's letter is bound to it only while the step is proved.
            let name = self.rpn(&variable);
            let scope_term = self.to_term(scope);
            let var = if scope.split_whitespace().any(|t| t == name)
                || self.names_held().contains(&name)
            {
                match self.unheld(&[&scope_term, &body, &over]) {
                    Some(spare) => self.rpn(&spare),
                    None => {
                        return Ok(Route::no(format!(
                            "no letter left to say {name} over"
                        )));
                    }
                }
            } else {
                name.clone()
            };
            self.reserved.insert(var.clone());
            let (body, variable) = if var == name {
                (body, variable)
            } else {
                let again =
                    self.restated(&body, &format!("{name} cv"), &format!("{var} cv"));
                (again, self.var_of(&var))
            };
            let made = self.for_every(
                scope,
                facts,
                &body,
                &variable,
                &over,
                &mut |me, said, inner, lifted| {
                    let at = me.rpn(said);
                    // The membership the member was fixed by, over the
                    // letter it was fixed as, which a spare replaces
                    // where the claim's own is held.
                    let member = me
                        .frames
                        .last()
                        .and_then(|f| f.added.clone())
                        .expect("a member fixed in its own frame");
                    let fixed = me.rpn(&me.to_term(&member).children()[0]);
                    let kept = me.member.replace(member);
                    let made = me.names_kept(|me| {
                        if let Some((page, _)) = &letter {
                            me.names.insert(page.clone(), fixed.clone());
                        }
                        me.with_requires(how, step, node, &at, inner, lifted, lines)
                    });
                    me.member = kept;
                    Ok(match made? {
                        Built(Some(p)) => Built(p),
                        Built(None) => Route::no("the step gives no proof at a member"),
                        Declined(d) => Declined(d),
                    })
                },
                true,
            )?;
            let made = take!(made);
            if var == name {
                return Ok(Built(Some(made)));
            }
            let said = t!(self.rpn(&body), var, self.rpn(&over), "wral");
            let Some(across) = self.renaming(&self.to_term(&said), &whole)? else {
                return Ok(Route::no(format!(
                    "the claim over {var} is not carried back to {name}"
                )));
            };
            return Ok(Built(Some(self.b.ap(
                "sylib",
                &binds! {"ph" => scope, "ps" => &said, "ch" => term},
                &[&made, &across],
            ))));
        }
        self.with_requires(how, step, node, term, scope, facts, lines)
    }

    /// The method run with the step's own requires lines, which hold for the
    /// whole of it, offered as `written` is, which the membership lookup and
    /// the one-lemma bridge read and a search does not.
    #[allow(clippy::too_many_arguments)]
    fn with_requires(
        &mut self,
        how: &Method,
        step: &Step,
        node: &Node,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        let known = if step.requires.is_empty() {
            Facts::new()
        } else {
            self.supplied(Some(step), scope, facts)?
        };
        // What the step writes is its requires lines and the lines it cites:
        // a cited `N ∈ ℕ` says N ≠ 0 as surely as a requires line would
        // (`READERS.md`, what a membership says).
        let known = self.with_cited(Some(step), scope, &known, None);
        // An `obtain`'s memberships are in the scope under its name rather
        // than in its proved line, and are what it writes all the same.
        for r in &step.just.refs {
            if let Some(line) = self.lines.get(r) {
                for said in &line.sentences {
                    let term = self.term(said)?;
                    if let Some(p) = self.held(facts, &term, scope)? {
                        self.know_default(&known, term, p);
                    }
                }
            }
        }
        self.writing(scope, &known, true, |me| {
            me.by_method(how, step, node, term, scope, facts, lines)
        })
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
                self.trying(item, step, *way, term, scope, facts, lines, None)?
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
        Err(self.untargeted(step, record))
    }

    /// An item the database gives no target for: nothing builds what it
    /// says, and the build takes nothing as stated, so citing it stops here.
    fn untargeted(&self, step: &Step, item: &Record) -> Problem {
        self.defect(
            step.line,
            format!(
                "step {} cites {}:{}, which the database gives no target for, and nothing is taken as stated",
                fmt(&step.number),
                item_kind(Item::Record(item)),
                item.qualified()
            ),
        )
    }

    /// A sentence of an item, read in the item's own names and then said at
    /// this step: each name the step's citation fixes (`citing::obtained`) is
    /// what it stands for, and a function letter standing for a rule is that
    /// rule where the sentence applies it. `x(n) ≤ B` of
    /// `convergent-bounded`, with x the partial sums of 1/k, is
    /// Σ(k = 1 to n) 1/k ≤ B.
    ///
    /// The citation is read as the checker reads it: the lines the step
    /// names, its requires lines, and the instantiation written in `cites`.
    /// An item that gives no "there is" from them is a defect, which the
    /// checker reports of the same step.
    pub(crate) fn item_sentence_here(
        &mut self,
        step: &Step,
        item: &'a Record,
        cites: Option<&str>,
        text: &str,
    ) -> Checked<Node> {
        let binding = self.matched_here(step, item, cites)?;
        let library = self.item_library();
        let node = self.in_its_names(Item::Record(item), |me| me.read(text))?;
        Ok(filled(&node, &binding, &library.ctx))
    }

    /// What each letter of a record a step cites stands for at that step,
    /// as the checker reads the citation (`citing`): the instantiation
    /// written in `cites`, and what the step's lines, its requires lines and,
    /// where it does not obtain, its claim fix. A letter is the record's own
    /// whatever the proof calls its letters, so a record's `k` is what the
    /// citation makes it and never the proof's `k`.
    ///
    /// A step that obtains takes the record's "there is" (`obtained`), and a
    /// record that gives none from what the step names is a defect, which the
    /// checker reports of the same step. Any other step concludes what it
    /// claims (`taken`); where no clause does, the binding is what the step
    /// writes, and the step fails further on, where it can say why.
    pub(crate) fn matched_here(
        &mut self,
        step: &Step,
        item: &'a Record,
        cites: Option<&str>,
    ) -> Checked<NodeBinding> {
        let library = self.item_library();
        let Some(groups) = library.groups(&item.qualified()) else {
            return Err(self.defect(
                step.line,
                format!("{} is not an item a step may cite", item.qualified()),
            ));
        };
        let mut facts = self.cited_sentences(&step.just.refs)?;
        for r in &step.requires {
            facts.push(self.read(&r.fact)?);
        }
        let cites = cites.unwrap_or(&step.just.text);
        let obtains = step.just.text.trim_start().starts_with("obtain");
        let claims = if obtains {
            Vec::new()
        } else {
            self.said(step)?
        };
        let parts =
            self.citation_parts(facts, claims, cites, &step.just.refs, &library)?;
        if !obtains {
            return match citing::taken(
                &groups,
                &parts.claims,
                &parts.facts,
                &parts.seed,
                &library,
            ) {
                Built(t) => Ok(t.binding),
                // The citation fixes only what it writes, and the step fails
                // where what it cites does not reach its claim, which says
                // why more exactly than that no clause matched.
                Declined(_) => Ok(parts.seed),
            };
        }
        let taken = match obtained(&groups, &parts.facts, &parts.seed, &library) {
            Built(t) => t,
            Declined(d) => {
                let missing = unsupplied_alone(&groups, &parts, &library);
                if missing.is_empty() {
                    return Err(d.into_problem(&self.thm.path, step.line));
                }
                return Err(self.defect(
                    step.line,
                    format!(
                        "step {} cites {}:{}, which asks for {}, and what it cites does not supply it",
                        fmt(&step.number),
                        item_kind(Item::Record(item)),
                        item.qualified(),
                        missing.join("; ")
                    ),
                ));
            }
        };
        Ok(taken.binding)
    }

    /// What a requires line citing an item asks for, as terms
    /// (`asked_here`). Empty where the line cites no record, and where no
    /// group of the item concludes the line's fact: then it asks nothing.
    pub fn asked_by_requires(
        &mut self,
        step: &Step,
        o: &Requires,
    ) -> Checked<Vec<String>> {
        let AskedHere { item, hypotheses } = match self.asked_here(step, o)? {
            Built(here) => here,
            Declined(_) => return Ok(Vec::new()),
        };
        // Each letter the binding fixes is already replaced in the hypotheses
        // (`citing::filled`), so they are terms in the item's names as they
        // stand.
        self.in_its_names(Item::Record(item), |me| {
            hypotheses.iter().map(|h| me.term(h)).collect()
        })
    }

    /// What a requires line citing a record asks for: the record's
    /// hypotheses under the binding the line's citation fixes
    /// (`citing::asked`), as trees. The citation is read as the checker
    /// reads it: the line's fact is its claim, and its facts are the lines
    /// its reason names, the requires lines above it, and the member a claim
    /// said of every member names. Declined where the line cites no record,
    /// and where no group of the record concludes the line's fact from them.
    pub(crate) fn asked_here(
        &mut self,
        step: &Step,
        o: &Requires,
    ) -> Checked<Route<AskedHere<'a>>> {
        let Some((cited, _)) = requires_item(&o.how) else {
            return Ok(Route::no("the line cites no item"));
        };
        let name = cited.split_once(':').map_or(cited.as_str(), |(_, n)| n);
        let full = self.thm.names.full(name);
        let Some(Item::Record(item)) = self.items.get(&full).copied() else {
            return Ok(Route::no("the line cites no record"));
        };
        let library = self.item_library();
        let refs = references(&o.how).0;
        let mut facts = self.cited_sentences(&refs)?;
        for above in step.requires_above(o.line) {
            facts.push(self.read(&above.fact)?);
        }
        if step.openers.is_empty() {
            if let [claim] = self.said(step)?.as_slice() {
                if let Some((member, _)) =
                    claimed_member(claim, &library, &self.sorts_now)
                {
                    facts.push(member);
                }
            }
        }
        let claims = self
            .sentences(&o.fact)
            .iter()
            .map(|s| self.read(s))
            .collect::<Checked<Vec<Node>>>()?;
        let parts = self.citation_parts(facts, claims, &o.how, &refs, &library)?;
        Ok(
            asked(&item.qualified(), &parts, &library).map(|asks| AskedHere {
                item,
                hypotheses: asks.hypotheses,
            }),
        )
    }

    /// What a citation supplies and claims (`citing::finished`), with the
    /// instantiation written in `cites` as its seed.
    ///
    /// A defined name is written out where the citation names its define
    /// among `refs`, and kept as the page writes it where it does not
    /// (`SYNTAX.md`, `cited_defines`): `x₁ ∈ ℝ` cited with D2 is
    /// `min(b, c + δ/2) ∈ ℝ`, and an obtain citing `S := S` without the
    /// define of S claims something of S.
    fn citation_parts(
        &self,
        facts: Vec<Node>,
        claims: Vec<Node>,
        cites: &str,
        refs: &[String],
        library: &citing::Library,
    ) -> Checked<Parts> {
        let defined = cited_defines(self.thm, self.env(), &self.sorts_now, refs);
        let facts = facts.iter().map(|n| expand(n, &defined)).collect();
        let claims = claims.iter().map(|n| expand(n, &defined)).collect();
        let mut seed = NodeBinding::new();
        for (name, value) in instantiation(cites) {
            seed.insert(name, expand(&self.read(&value)?, &defined));
        }
        Ok(finished(facts, claims, seed, library, &self.sorts_now))
    }

    /// The values a citation gives its item's letters, `name := value`, each
    /// read in the names as they stand before any is given: values are
    /// simultaneous, so `a := b/k, b := a/k` swaps the two.
    pub(crate) fn instantiated(
        &mut self,
        cites: &str,
    ) -> Checked<Vec<(String, String)>> {
        let mut out = Vec::new();
        for (name, value) in instantiation(cites) {
            let node = self.read(&value)?;
            out.push((name, self.term(&node)?));
        }
        Ok(out)
    }

    /// What the lines and labelled hypotheses `refs` name say, each sentence
    /// read.
    pub(crate) fn cited_sentences(&self, refs: &[String]) -> Checked<Vec<Node>> {
        let mut given: Vec<Node> = Vec::new();
        for r in refs {
            if let Some(line) = self.lines.get(r) {
                given.extend(line.sentences.iter().cloned());
                // A line of several sentences is their conjunction too
                // (`sorts::supplied_by`), read as the checker reads it.
                if line.sentences.len() > 1 {
                    let parts: Vec<String> = line
                        .sentences
                        .iter()
                        .map(|s| format!("({})", self.g.print(s)))
                        .collect();
                    given.push(self.read(&parts.join(" and "))?);
                }
            }
        }
        // Only what the step cites: a sort line fixes nothing. A cited
        // hypothesis says what it says to the checker (`said_by_line`).
        for h in &self.thm.hypotheses {
            if h.label.as_ref().is_some_and(|l| refs.contains(l)) {
                for s in supplied_by(&unlabel(&said_by_line(h.kind, &h.text))) {
                    given.push(self.read(&s)?);
                }
            }
        }
        Ok(given)
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
        // A line may say several things at once, and the `for all` is
        // rarely the first of them. Taken apart on its own.
        let known = Facts::new();
        let whole_proof = self.carried(&where_, facts, lines);
        self.know(&known, held.term.clone(), whole_proof.clone());
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
        let mut proof = self
            .held(&known, &said, scope)?
            .expect("a part of the line, taken apart above");
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
        let mut facing = self.held(facts, &t!(old, new, "wceq"), scope)?;
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
                let Some(held) = self.held(facts, &t!(new, old, "wceq"), scope)? else {
                    return Err(self.defect(
                        step.line,
                        format!("no equation {old} = {new} in scope"),
                    ));
                };
                pf!(self.b; scope, new, old, held, "eqcomd")
            }
        };
        // The claim is what it rewrites with one side of the equation put
        // for the other at some of the places it stands, every place or
        // fewer: where the two differ, the equation says they are equal, and
        // nothing else is asked (`congruence` over the equation alone).
        let equation = Facts::new();
        self.know(&equation, t!(old, new, "wceq"), facing);
        let leaf = Leaf::Rows(vec![super::tables::Row::Held]);
        let into = said.get(3).map(|m| m.as_str().to_string());
        let Some(into_text) = into else {
            let (start, other) =
                (self.term(&node.children[0])?, self.term(&node.children[1])?);
            let alike = self.congruence(
                &self.to_term(&start),
                &self.to_term(&other),
                scope,
                &equation,
                Some(step),
                &leaf,
            )?;
            return match alike {
                Built(p) if start != other => Ok(Built(p)),
                _ => Err(self.defect(step.line, "the substitution misses the claim")),
            };
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
        // them, so each sentence is offered with a proof of itself; and the
        // line as a whole is offered, which a claim of as many sentences
        // rewrites (`SYNTAX.md`: the equation is replaced inside the line).
        let held = self.carried(&where_, facts, lines);
        let known = Facts::new();
        self.know(&known, into.term.clone(), held.clone());
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
        let mut starts: Vec<String> = vec![into.term.clone()];
        for one in &offered {
            let start = self.term(one)?;
            if !starts.contains(&start) {
                starts.push(start);
            }
        }
        for start in &starts {
            if !self.holds(&known, start) {
                if let Some(p) = self.held(facts, start, scope)? {
                    self.know(&known, start.clone(), p);
                }
            }
        }
        // The claim as written, and an equation's the other way round: what
        // the substitution makes may face either way (`turned_claim`).
        let mut aims: Vec<(String, Option<&'static str>)> =
            vec![(term.to_string(), None)];
        if let Some((turned, flip)) = self.turned_claim(term) {
            aims.push((turned, Some(flip)));
        }
        for (aim, flip) in &aims {
            for start in &starts {
                if start == aim {
                    continue;
                }
                let Some(given) = self.held(&known, start, scope)? else {
                    continue;
                };
                let Built(alike) = self.congruence(
                    &self.to_term(start),
                    &self.to_term(aim),
                    scope,
                    &equation,
                    Some(step),
                    &leaf,
                )?
                else {
                    continue;
                };
                let made = pf!(self.b; scope, start, aim, given, alike, "mpbid");
                let Some(flip) = flip else {
                    return Ok(Built(made));
                };
                let sides = self.to_term(aim);
                let (a, b) = (
                    self.rpn(&sides.children()[0]),
                    self.rpn(&sides.children()[1]),
                );
                return Ok(Built(pf!(self.b; scope, a, b, made, *flip)));
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
        cites: Option<&[String]>,
    ) -> Checked<Route<Proof>> {
        let refs = cites.unwrap_or(&step.just.refs);
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
            let made = take!(self
                .one_equivalent(lemma, step, &instance, scope, facts, lines, cites)?);
            let supplied = self.supplied(Some(step), scope, facts)?;
            let held = self.with_cited(Some(step), scope, &supplied, cites);
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
        let said: Vec<String> = refs
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
        let known = self.with_cited(Some(step), scope, &supplied, cites);
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
        cites: Option<&[String]>,
    ) -> Checked<Route<Proof>> {
        let refs = cites.unwrap_or(&step.just.refs);
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
        for r in refs {
            let Some(cited) = lines.get(r) else {
                continue;
            };
            let held = Facts::new();
            let whole_proof = self.carried(r, facts, lines);
            self.know(&held, cited.term.clone(), whole_proof.clone());
            for one in &cited.sentences {
                let said = self.term(one)?;
                if let Some(p) = self.held(facts, &said, scope)? {
                    self.know_default(&held, said, p);
                }
            }
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
        // A step said of every member unfolds the membership its claim's
        // "for all" gives, as it would a cited line saying it.
        if chosen.is_none() {
            if let Some(member) = self.member.clone() {
                if let Some(p) = self.held(facts, &member, scope)? {
                    let held = Facts::new();
                    self.know(&held, member, p);
                    if let Built(found) = self.unfolds_from(
                        &reads.children()[0],
                        &held,
                        &variables,
                        scope,
                        facts,
                    )? {
                        chosen = Some(found);
                    }
                }
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
        // A letter the lemma binds is kept apart from every letter the
        // values spell: `divides` binds n, and unfolding "m + n is even"
        // under it would capture the step's own n. Where one meets, it takes
        // a letter nothing holds, as `applied_body` moves a rule's letter.
        let values: Vec<Term> = binding.values().cloned().collect();
        let spelt: BTreeSet<String> = values
            .iter()
            .flat_map(|v| {
                self.rpn(v)
                    .split_whitespace()
                    .map(String::from)
                    .collect::<Vec<_>>()
            })
            .collect();
        let meeting: Vec<String> = self
            .letters_bound(&reads)
            .iter()
            .filter(|v| {
                !binding.contains_key(&***v) && spelt.contains(&self.float_of(v))
            })
            .map(|v| v.to_string())
            .collect();
        if !meeting.is_empty() {
            let seen: Vec<&Term> = values.iter().collect();
            if let Some(moved) = self.unheld_for(meeting, &seen) {
                binding.extend(moved);
            }
        }
        let left = self.rpn(&reads.children()[0].substitute(&binding));
        let right = self.rpn(&reads.children()[1].substitute(&binding));
        // What carries the unfolding to the claim asks from what the step
        // names, requires lines included.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let facts = self.with_cited(Some(step), scope, &supplied, cites);
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
        self.know(&known, right.clone(), proof.clone());
        self.unpack(&right, &proof, scope, &known, 4);
        if let Some(p) = self.held(&known, term, scope)? {
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
    ///
    /// `cites` is the lines the citation names: None for a step's own, and a
    /// requires line's where the line cites the item (`by_its_reason`).
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
        cites: Option<&[String]>,
    ) -> Checked<Route<Proof>> {
        let mut declines = Vec::new();
        for lemma in item_clauses(item) {
            let found = match way {
                Way::Equivalent => {
                    self.one_equivalent(&lemma, step, term, scope, facts, lines, cites)?
                }
                _ => {
                    self.one_unfolded(&lemma, step, term, scope, facts, lines, cites)?
                }
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
    pub fn reading(
        &mut self,
        item: &'a Record,
        term: &str,
        step: &Step,
        cites: Option<&[String]>,
    ) -> Checked<Way> {
        let refs = cites.unwrap_or(&step.just.refs);
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
                if refs.iter().any(|r| {
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

    /// A definition with no target, read off a line the step cites that
    /// already says what the step claims, whole or with another letter bound.
    /// Nothing builds it otherwise, and nothing is taken as stated.
    fn take_definition(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(found) = self.projected(step, term, scope, facts, lines)? {
            return Ok(Built(found));
        }
        for r in &step.just.refs {
            let Some(held) = lines.get(r) else {
                continue;
            };
            let parts = Facts::new();
            let whole = self.carried(r, facts, lines);
            self.know(&parts, held.term.clone(), whole.clone());
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
        Err(self.defect(
            step.line,
            format!(
                "{}:{} has no target, and nothing step {} cites says {}",
                item_kind(Item::Record(item)),
                item.qualified(),
                fmt(&step.number),
                self.render(term)
            ),
        ))
    }

    /// The claim, when a line the step cites is a conjunction stating it,
    /// taken apart on its own to the depth of a congruence's six conjuncts.
    fn projected(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Option<Proof>> {
        for r in &step.just.refs {
            let cited = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
            let known = Facts::new();
            let whole = self.carried(r, facts, lines);
            self.know(&known, cited.term.clone(), whole.clone());
            self.unpack(&cited.term, &whole, scope, &known, 8);
            if let Some(p) = self.held(&known, term, scope)? {
                return Ok(Some(p));
            }
        }
        Ok(None)
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
        match self.by_clause_either_way(
            &labels,
            term,
            scope,
            facts,
            step,
            Some(&seed),
        )? {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {head} gives what step {} claims: {}",
                    fmt(&step.number),
                    self.say(&d)
                ),
            )),
        }
    }

    /// The label this theorem is written under.
    pub fn own_label(&self) -> Checked<String> {
        label_of(
            &self.thm.qualified(),
            &self.b.sigs,
            self.b.syntax(),
            &self.thm.path,
            self.thm.line,
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
        self.know(&known, line.term.clone(), proof.clone());
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
        if whole.label() == Some("wfn") {
            let supplied = self.supplied(Some(step), scope, facts)?;
            let held = self.with_cited(Some(step), scope, &supplied, None);
            return self.define_on(&whole, scope, &held);
        }
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

    /// ( scope -> t Fn A ) for a function a define gives on A: the map is a
    /// function on its domain where each value its rule gives is a set
    /// (`mptfng`), and the define's equation carries that to its name
    /// (`fneq1d`), for a step citing the define and for a `requires` line
    /// resting on it. `ELABORATION.md`, "A defined function is a map".
    pub fn define_on(
        &mut self,
        whole: &Term,
        scope: &str,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let name = whole.children()[0].clone();
        let (map, is_map) = take!(self.define_value(&name, scope, held)?);
        if map.label() != Some("cmpt") || map.children().len() != 3 {
            return Ok(Route::no(
                "what is claimed a function is no function a define gives",
            ));
        }
        let (letter, over, rule) = (
            self.rpn(&map.children()[0]),
            self.rpn(&map.children()[1]),
            self.rpn(&map.children()[2]),
        );
        let every = t!(t!(rule, "cvv", "wcel"), letter, over, "wral");
        let sets =
            take!(self.settle(&self.to_term(&every), scope, held, 3, None, None)?);
        let map_rpn = self.rpn(&map);
        let on = self.b.ap(
            "mptfng",
            &binds! {"F" => &map_rpn, "x" => &letter, "A" => &over, "B" => &rule},
            &[&self.b.ap("eqid", &binds! {"A" => &map_rpn}, &[])],
        );
        let map_on = t!(map_rpn, over, "wfn");
        let mapped = self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &every, "ch" => &map_on},
            &[&sets, &on],
        );
        let name_rpn = self.rpn(&name);
        let carried = self.b.ap(
            "fneq1d",
            &binds! {"ph" => scope, "F" => &name_rpn, "G" => &map_rpn, "A" => &over},
            &[&is_map],
        );
        let on_over = t!(name_rpn, over, "wfn");
        let named = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &on_over, "ch" => &map_on},
            &[&mapped, &carried],
        );
        // A domain the claim names by a define is the set the define's body
        // holds written out, and the two are one in standard form.
        let claimed = self.rpn(whole);
        if claimed == on_over {
            return Ok(Built(named));
        }
        let alike =
            take!(self.same(&self.to_term(&on_over), whole, scope, held, None)?);
        Ok(Built(
            pf!(self.b; scope, on_over, claimed, named, alike, "mpbid"),
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
        let letters = self.letters_bound(one);
        let kept = std::mem::replace(&mut self.binding, letters);
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
        let super::state::Recurrence {
            step,
            start,
            count,
            input,
        } = self.recursions[&recursion].clone();
        let where_ = self.rpn(&at);
        if let Some(input) = &input {
            let Some((state, moved)) = take!(
                self.indexed_value(&at, &recursion, &step, &start, input, scope, held)?
            ) else {
                return Ok(Built((value.clone(), proof)));
            };
            return self.part_of_state(
                one,
                value,
                proof,
                &path,
                state,
                moved,
                &where_,
                &recursion,
                count + 1,
                scope,
                held,
            );
        }
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
        let (state, moved);
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
        self.part_of_state(
            one, value, proof, &path, state, moved, &where_, &recursion, count, scope,
            held,
        )
    }

    /// (state, ( scope -> R(at) = state )) for a recursion whose rules name
    /// the index (`recursion_terms`), the state being ⟨at, the values⟩;
    /// None where `at` is neither 0 nor J + 1.
    ///
    /// At 0, `seq1` says R(0) is G(0), which is ⟨0, start⟩. At J + 1,
    /// `seqp1d` says R(J + 1) is F(R(J), G(J + 1)), and `ovmpog` takes F at
    /// the two over letters of its own (`cbvmpov`), since R(J) holds F and
    /// with it F's letters. What F gives names the index as 1st(G(J + 1)),
    /// and k as that less one, which `op1stg` and `pncand` make J + 1 and J.
    #[allow(clippy::too_many_arguments)]
    fn indexed_value(
        &mut self,
        at: &Term,
        recursion: &str,
        step: &str,
        start: &str,
        input: &str,
        scope: &str,
        held: &Facts,
    ) -> Checked<Route<Option<(String, Proof)>>> {
        let where_ = self.rpn(at);
        let at_zero = where_ == "cc0";
        let at_next = at.label() == Some("co")
            && at.children()[1].label() == Some("c1")
            && at.children()[2].label() == Some("caddc");
        if !at_zero && !at_next {
            return Ok(Built(None));
        }
        let index_in = if at_zero {
            pf!(self.b; t!("cc0", "cn0", "wcel"), scope, "0nn0", "a1i")
        } else {
            take!(self.settle(
                &self.to_term(&t!(where_, "cn0", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?)
        };
        // G at the index: ⟨index, start⟩ (`fvmptd3`).
        let g = self.to_term(input);
        let letter = self.rpn(&g.children()[0]);
        let body = self.rpn(&g.children()[2]);
        let given = t!(where_, start, "cop");
        let tie = self.to_term(&t!(
            t!(format!("{letter} cv"), where_, "wceq"),
            t!(body, given, "wceq"),
            "wi"
        ));
        let instance = take!(self.prove_essential(&tie, "", &Facts::new())?);
        let given_set = pf!(self.b; t!(given, "cvv", "wcel"), scope,
            self.b.ap("opex", &binds! {"A" => &where_, "B" => start}, &[]), "a1i");
        let given_is = self.b.ap(
            "fvmptd3",
            &binds! {"ph" => scope, "x" => &letter, "A" => &where_, "B" => &body, "C" => &given, "D" => "cn0", "F" => input, "V" => "cvv"},
            &[&pf!(self.b; input, "eqid"), &instance, &index_in, &given_set],
        );
        let at_r = t!(where_, recursion, "cfv");
        let at_g = t!(where_, input, "cfv");
        if at_zero {
            let law = self.b.ap(
                "seq1",
                &binds! {"M" => "cc0", ".+" => step, "F" => input},
                &[],
            );
            let first = self.b.ap(
                "ax-mp",
                &binds! {"ph" => t!("cc0", "cz", "wcel"), "ps" => t!(at_r, at_g, "wceq")},
                &[&self.step("0z"), &law],
            );
            let first = pf!(self.b; t!(at_r, at_g, "wceq"), scope, first, "a1i");
            let moved = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &at_r, "B" => &at_g, "C" => &given},
                &[&first, &given_is],
            );
            return Ok(Built(Some((given, moved))));
        }
        let before = self.rpn(&at.children()[0]);
        let before_in = take!(self.settle(
            &self.to_term(&t!(before, "cn0", "wcel")),
            scope,
            held,
            3,
            None,
            None
        )?);
        let prior = t!(before, recursion, "cfv");
        let applied = t!(prior, given, step, "co");
        let stepped = self.b.ap(
            "seqp1d",
            &binds! {"ph" => scope, "Z" => "cn0", "M" => "cc0", "N" => &before, "K" => &where_,
            ".+" => step, "F" => input, "A" => &prior, "B" => &given},
            &[
                &self.step("nn0uz"),
                &before_in,
                &pf!(self.b; where_, "eqid"),
                &self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &prior}, &[]),
                &given_is,
            ],
        );
        // F taken at R(J) and G(J + 1), over letters R(J) does not hold.
        let map = self.to_term(step);
        let (z, w) = (self.rpn(&map.children()[0]), self.rpn(&map.children()[1]));
        let rule = map.children()[4].clone();
        let (x, y) = (self.spare_var()?, self.spare_var()?);
        let (zc, wc, xc, yc) = (
            format!("{z} cv"),
            format!("{w} cv"),
            format!("{x} cv"),
            format!("{y} cv"),
        );
        let r = self.rpn(&rule);
        let half = self.rpn(&self.restated(&rule, &zc, &xc));
        let fresh = self.rpn(&self.restated(&self.to_term(&half), &wc, &yc));
        let mut ties = Vec::new();
        for (from, to, was, now) in [(&zc, &xc, &r, &half), (&wc, &yc, &half, &fresh)] {
            let tie =
                self.to_term(&t!(t!(from, to, "wceq"), t!(was, now, "wceq"), "wi"));
            ties.push(take!(self.prove_essential(&tie, "", &Facts::new())?));
        }
        let respelt = self.b.ap(
            "cbvmpov",
            &binds! {"x" => &z, "y" => &w, "z" => &x, "w" => &y, "A" => "cvv", "B" => "cvv",
            "C" => &r, "E" => &half, "D" => &fresh},
            &[&ties[0], &ties[1]],
        );
        let once = self.rpn(&self.restated(&self.to_term(&fresh), &xc, &prior));
        let taken = self.rpn(&self.restated(&self.to_term(&once), &yc, &given));
        let mut ties = Vec::new();
        for (from, to, was, now) in
            [(&xc, &prior, &fresh, &once), (&yc, &given, &once, &taken)]
        {
            let tie =
                self.to_term(&t!(t!(from, to, "wceq"), t!(was, now, "wceq"), "wi"));
            ties.push(take!(self.prove_essential(&tie, "", &Facts::new())?));
        }
        let law = self.b.ap(
            "ovmpog",
            &binds! {"x" => &x, "y" => &y, "A" => &prior, "B" => &given, "C" => "cvv", "D" => "cvv",
            "R" => &fresh, "G" => &once, "S" => &taken, "F" => step, "H" => "cvv"},
            &[&ties[0], &ties[1], &respelt],
        );
        let pair = self.to_term(&taken);
        let mut sets = Vec::new();
        for (term, made) in [
            (&prior, self.b.ap("fvex", &binds! {"A" => &before, "F" => recursion}, &[])),
            (&given, self.b.ap("opex", &binds! {"A" => &where_, "B" => start}, &[])),
            (
                &taken,
                self.b.ap(
                    "opex",
                    &binds! {"A" => self.rpn(&pair.children()[0]), "B" => self.rpn(&pair.children()[1])},
                    &[],
                ),
            ),
        ] {
            sets.push(pf!(self.b; t!(term, "cvv", "wcel"), scope, made, "a1i"));
        }
        let evaluated = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(prior, "cvv", "wcel"), "ch" => t!(given, "cvv", "wcel"),
            "th" => t!(taken, "cvv", "wcel"), "ta" => t!(applied, taken, "wceq")},
            &[&sets[0], &sets[1], &sets[2], &law],
        );
        // 1st(G(J + 1)) is J + 1 (`op1stg`), and that less one is J (`pncand`).
        let first_of = t!(given, "c1st", "cfv");
        let mut parts_set = Vec::new();
        for c in [&where_, &start.to_string()] {
            parts_set.push(take!(self.settle(
                &self.to_term(&t!(c, "cvv", "wcel")),
                scope,
                held,
                3,
                None,
                None
            )?));
        }
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(where_, "cvv", "wcel"), "ch" => t!(start, "cvv", "wcel")},
            &[&parts_set[0], &parts_set[1]],
        );
        let law = self.b.ap(
            "op1stg",
            &binds! {"A" => &where_, "B" => start, "V" => "cvv", "W" => "cvv"},
            &[],
        );
        let index_is = pf!(self.b; scope,
            t!(t!(where_, "cvv", "wcel"), t!(start, "cvv", "wcel"), "wa"),
            t!(first_of, where_, "wceq"), both, law, "syl");
        let less_one = t!(first_of, "c1", "cmin", "co");
        let shifted = self.b.ap(
            "oveq1d",
            &binds! {"ph" => scope, "A" => &first_of, "B" => &where_, "C" => "c1", "F" => "cmin"},
            &[&index_is],
        );
        let before_cc = self.b.ap(
            "nn0cnd",
            &binds! {"ph" => scope, "A" => &before},
            &[&before_in],
        );
        let one_cc = self.b.ap("1cnd", &binds! {"ph" => scope}, &[]);
        let cancelled = self.b.ap(
            "pncand",
            &binds! {"ph" => scope, "A" => &before, "B" => "c1"},
            &[&before_cc, &one_cc],
        );
        let k_is = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &less_one, "B" => t!(where_, "c1", "cmin", "co"), "C" => &before},
            &[&shifted, &cancelled],
        );
        let known = Facts::new();
        self.know(&known, t!(first_of, where_, "wceq"), index_is);
        self.know(&known, t!(less_one, before, "wceq"), k_is);
        let state = {
            let read = self.restated(&pair, &less_one, &before);
            self.rpn(&self.restated(&read, &first_of, &where_))
        };
        let tidied = take!(self.congruence(
            &pair,
            &self.to_term(&state),
            scope,
            &known,
            None,
            &Leaf::Rows(vec![super::tables::Row::Held])
        )?);
        let mut moved = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &at_r, "B" => &applied, "C" => &taken},
            &[&stepped, &evaluated],
        );
        moved = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &at_r, "B" => &taken, "C" => &state},
            &[&moved, &tidied],
        );
        Ok(Built(Some((state, moved))))
    }

    /// (part, ( scope -> one = part )) from ( scope -> R(where) = state ):
    /// the part `path` names, taken out of the state from the inside with
    /// `op1stg` and `op2ndg`. `parts` is how many components the state
    /// holds, so a state of one is never taken apart.
    #[allow(clippy::too_many_arguments)]
    fn part_of_state(
        &mut self,
        one: &Term,
        value: &Term,
        proof: Proof,
        path: &[String],
        mut state: String,
        mut moved: Proof,
        where_: &str,
        recursion: &str,
        parts: usize,
        scope: &str,
        held: &Facts,
    ) -> Checked<Route<(Term, Proof)>> {
        let mut held_at = t!(where_, recursion, "cfv");
        for label in path.iter().rev() {
            let pair = self.to_term(&state);
            if pair.label() != Some("cop") || parts < 2 {
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
        // Each sentence of a cited line is read on its own, as `witnessed`
        // reads them: a line saying two things names a witness in either.
        let mut witness = None;
        // An equation names its witness whichever way round it is written,
        // `(f(b) − f(a))/(b − a) = f′(c)` as well as `f′(c) = …`.
        'lines: for r in &step.just.refs {
            let line = lines.get(r).unwrap_or_else(|| panic!("no line {r} cited"));
            for part in self.parts(&line.term) {
                let mut ways = vec![part.clone()];
                ways.extend(self.turned_claim(&part).map(|(t, _)| t));
                for way in ways {
                    let actual = self.applications_read(&self.to_term(&way));
                    witness = self.witness_in(&asked, &actual, &stands);
                    if witness.is_some() {
                        break 'lines;
                    }
                }
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

    /// An existence claim with the equation under its quantifiers turned
    /// round, where a definition's lemma writes it the other way from the
    /// page (`targets::unfolding`).
    fn body_turned(term: &Term) -> Term {
        if term.label() == Some("wrex") {
            let mut kids = term.children().to_vec();
            kids[0] = Self::body_turned(&kids[0]);
            return Term::apply("wrex", kids);
        }
        if term.label() == Some("wceq") && term.children().len() == 2 {
            return Term::apply(
                "wceq",
                vec![term.children()[1].clone(), term.children()[0].clone()],
            );
        }
        term.clone()
    }

    /// A definition used the other way: its right side, an existence claim
    /// with as many witnesses as it quantifies over, is proved from the lines
    /// the step names as `exhibit` proves one (`witnessed`), and the
    /// definition folds it into the claim.
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
        let Item::Record(cited) = self.item_cited(&head) else {
            panic!("{head} is a definition of the database");
        };
        // Each letter of the definition is what the citation makes it,
        // `matched_here`: the g of `u ∈ gH` is the element the step's claim
        // writes there, whatever the proof calls it.
        let mut matched = Vec::new();
        for (name, node) in self.matched_here(step, cited, None)? {
            if node.notation != crate::matching::PROPERTY {
                matched.push((name, self.term(&node)?));
            }
        }
        // The values are read in the proof's names, before any letter of
        // the definition is given one: `n := d, d := a` gives n the proof's
        // d, not the definition's.
        let values = self.instantiated(&step.just.text)?;
        let (lemma, flipped, right) =
            self.names_kept(|me| -> Checked<(String, bool, String)> {
                for (name, term) in matched {
                    me.names.insert(name, term);
                }
                // A definition may name more than the thing it is about.
                for (name, term) in values {
                    me.names.insert(name, term);
                }
                let item = cited;
                let (lemma, flipped) = targets::unfolding(item);
                let Some(lemma) = lemma else {
                    return Err(me.defect(me.at, format!("{head} has no target field")));
                };
                let node = me.in_its_names(Item::Record(item), |me| {
                    me.read(&item.conclusions[0].0)
                })?;
                let (left, right) =
                    (node.children[0].clone(), node.children[1].clone());
                me.names
                    .insert(subject_of(&left).text.clone(), subject.clone());
                // Each name the right side binds is a letter nothing in the
                // proof holds and the subject does not spell (`unheld_for`, as
                // the renaming rule gives one), given for this reading only.
                let mut bound = Vec::new();
                let mut rest = vec![right.clone()];
                while let Some(node) = rest.pop() {
                    if let Some(held) = me.binders.get(&node.notation) {
                        for &at in held {
                            if node.children[at].is_name() {
                                bound.push(node.children[at].text.clone());
                            }
                        }
                    }
                    rest.extend(node.children.iter().cloned());
                }
                let Some(letters) = me.unheld_for(bound, &[&me.to_term(&subject)])
                else {
                    return Err(me.defect(
                        step.line,
                        "no letter left to read the definition by",
                    ));
                };
                let kept = me.bound_as.clone();
                for (name, letter) in &letters {
                    me.bound_as.insert(name.clone(), me.rpn(letter));
                }
                let read = me.term(&right);
                me.bound_as = kept;
                Ok((lemma, flipped, read?))
            })?;
        // Its equation faces the way the lemma writes it.
        let mut whole = self.to_term(&right);
        if flipped {
            whole = Self::body_turned(&whole);
        }
        let ex = self.rpn(&whole);
        let (var, over) = (
            self.rpn(&whole.children()[1]),
            self.rpn(&whole.children()[2]),
        );
        let supplied = self.supplied(Some(step), scope, facts)?;
        let p_ex = take!(self.witnessed(step, &whole, scope, &supplied, lines)?);
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

    /// `by_clause`, with an equation one claim either way round, as the
    /// checker reads an item's conclusion (`citing::either_way`): `b = a` is
    /// what an item concluding `a = b` gives, turned.
    fn by_clause_either_way(
        &mut self,
        labels: &[String],
        term: &str,
        scope: &str,
        facts: &Facts,
        step: &Step,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        let found = self.by_clause(labels, term, scope, facts, step, seed)?;
        if !found.is_declined() {
            return Ok(found);
        }
        let Some((turned, flip)) = self.turned_claim(term) else {
            return Ok(found);
        };
        match self.by_clause(labels, &turned, scope, facts, step, seed)? {
            Built(p) => {
                let sides = self.to_term(&turned);
                let (a, b) = (
                    self.rpn(&sides.children()[0]),
                    self.rpn(&sides.children()[1]),
                );
                Ok(Built(pf!(self.b; scope, a, b, p, flip)))
            }
            Declined(_) => Ok(found),
        }
    }

    /// An equation or disequation with its sides the other way round, and
    /// the lemma that turns a proof of it back: `B = A` and `eqcomd`, or
    /// `B ≠ A` and `necomd`. None for any other claim.
    pub(crate) fn turned_claim(&self, term: &str) -> Option<(String, &'static str)> {
        let whole = self.to_term(term);
        let flip = match whole.label() {
            Some("wceq") => "eqcomd",
            Some("wne") => "necomd",
            _ => return None,
        };
        let label = whole.label()?.to_string();
        let (a, b) = (
            self.rpn(&whole.children()[0]),
            self.rpn(&whole.children()[1]),
        );
        Some((t!(b, a, &label), flip))
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
            return Err(self.untargeted(step, item));
        }
        let seed = self.filling(step, item, None)?;
        match self.by_clause_either_way(
            &labels,
            term,
            scope,
            facts,
            step,
            Some(&seed),
        )? {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {} reaches what step {} claims: {}",
                    step.just.head,
                    fmt(&step.number),
                    self.say(&d)
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
        // Why each clause did not reach the claim, said in order, so that a
        // message names what the clause that came closest lacked.
        let mut why: Vec<String> = Vec::new();
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
            match found {
                Declined(d) => why.push(self.say(&d)),
                built => return Ok(built),
            }
        }
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return Ok(Route::no(why.join("; ")));
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
        // A fill is written in the record's letters, each replaced by what it
        // stands for in the proof's names: a letter the step gives a value is
        // that value as the step writes it, and any other is what the
        // citation makes it (`matched_here`), never what the proof calls by
        // the same letter.
        let given = instantiation(cites.unwrap_or(&step.just.text));
        let mut bound: NodeBinding = self
            .matched_here(step, item, cites)?
            .into_iter()
            .filter(|(name, _)| !given.iter().any(|(g, _)| g == name))
            .collect();
        for (name, value) in &given {
            bound.insert(name.clone(), self.read(value)?);
        }
        let library = self.item_library();
        let mut out = Binding::new();
        for (name, formula) in &fills {
            let node = self.in_its_names(Item::Record(item), |me| me.read(formula))?;
            let node = filled(&node, &bound, &library.ctx);
            let term = self.term(&node)?;
            out.insert(name.clone(), self.to_term(&term));
        }
        Ok(out)
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
        let claim_text = step.claim_text();
        let (binds, wanted, whole) = self.names_and_sets_kept(
            |me| -> Checked<(IndexMap<String, String>, Vec<String>, String)> {
                let saved = me.names.clone();
                // Every value is read in the step's own names before any
                // letter of the theorem is given one: `a := b/k, b := a/k`
                // swaps the two, and reading the second after the first is
                // given would read a/k as (b/k)/k.
                let values: IndexMap<String, String> = me
                    .instantiated(cites.unwrap_or(&step.just.text))?
                    .into_iter()
                    .collect();
                let mut binds: IndexMap<String, String> = IndexMap::new();
                for h in &other.hypotheses {
                    // Parsed with the theorem's own sorts, which say what its
                    // letters are; only its shape and name are used here.
                    let said = me.hypothesis_formula(h.kind.as_str(), &h.text);
                    let node =
                        me.in_its_names(Item::Theorem(other), |me| me.read(&said))?;
                    // `let X be a set` and `let A be a point` name a class as
                    // surely as `let n ∈ ℕ` does, and the name is in the same
                    // place.
                    if h.kind == Intro::Let
                        && matches!(
                            node.notation.as_str(),
                            "membership"
                                | "is-a-set"
                                | "is-a-point"
                                | "conjunction"
                                | "function-type"
                        )
                    {
                        let name = subject_of(&node).text.clone();
                        let theirs = spare
                            .pop_front()
                            .expect("a class for each let")
                            .to_string();
                        // A hypothesis the citation does not name stands for what
                        // the citing proof calls by the same word.
                        if let Some(term) = values.get(&name) {
                            me.names.insert(name.clone(), term.clone());
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
                            let node = me.read(
                                &me.hypothesis_formula(h.kind.as_str(), &h.text),
                            )?;
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
                // What the cited label proves is its statement over its own
                // letters, which the claim may bind otherwise; the two are
                // joined below, not taken to be one.
                let mut whole = stated.clone();
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
            if self.holds(&known, one) {
                continue;
            }
            match self.settle(&self.to_term(one), scope, &known, 3, None, None)? {
                Built(p) => self.know(&known, one.clone(), p),
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
        let mut proof = match &pair {
            Some(p) => Some(
                self.held(&known, p, scope)?
                    .expect("a hypothesis just supplied"),
            ),
            None => None,
        };
        for extra in wanted.iter().skip(1) {
            let held = self
                .held(&known, extra, scope)?
                .expect("a hypothesis just supplied");
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
            self.b.syntax(),
            &self.thm.path,
            self.thm.line,
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
        // A theorem of this file stated over the file's own defines speaks of
        // them by name, as the citing step does, so the step reads them as
        // the statement does without citing them, as the checker reads it.
        let kept = self.resting.clone();
        let over = self.stated_over(other);
        if let Some(allowed) = &mut self.resting {
            allowed.extend(over);
        }
        // What the step writes and cites is what reading the statement over
        // the step's own terms may ask: e(n) ∈ ℤ, to read s at e(n).
        let read = self.with_cited(Some(step), scope, &known, None);
        let offered = facts.with(&read);
        let concluded = self.concluded(step, term, &whole, proof, scope, &offered);
        self.resting = kept;
        concluded
    }

    /// ( scope -> term ) from the cited theorem's statement `whole`, proved
    /// by `proof`: the statement itself, over other bound letters, or one
    /// sentence of it said in other words.
    fn concluded(
        &mut self,
        step: &Step,
        term: &str,
        whole: &str,
        proof: Proof,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Proof> {
        let whole = whole.to_string();
        if term == whole {
            return Ok(proof);
        }
        // The claim over other bound letters: one claim, renamed closed by
        // way of letters nothing holds (`renaming_apart`).
        if self.rebound(&whole, term) {
            if let Some(across) = self.renaming_apart(&whole, term)? {
                let turned = pf!(self.b; t!(whole, term, "wb"), scope, across, "a1i");
                return Ok(pf!(self.b; scope, whole, term, proof, turned, "mpbid"));
            }
        }
        let taken = Facts::new();
        self.know(&taken, whole.clone(), proof.clone());
        self.unpack(&whole, &proof, scope, &taken, 4);
        if let Some(p) = self.held(&taken, term, scope)? {
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
    /// The syntax the library gives with the corpus's constants declared,
    /// and every statement it has read, shared by every theorem elaborated
    /// against the same constants. A theorem reads the statements of the
    /// labels it uses, and reading them afresh for each theorem measured at
    /// four seconds of a ten-second build. Keyed by the constants, since a
    /// syntax holds for
    /// them alone and one library may serve corpora that declare others.
    syntaxes: RefCell<IndexMap<Constants, Rc<Syntax>>>,
}

/// The labels a corpus declares on top of the library, with their
/// statements, in the order they are declared.
type Constants = Vec<(String, Vec<String>)>;

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
            syntaxes: RefCell::new(IndexMap::new()),
        }
    }

    /// The syntax these signatures give, built once for each set of labels
    /// the corpus adds on top of the library.
    ///
    /// Only what a theorem adds before it reads anything may be added here:
    /// the corpus's constants. What it adds later (a step taken as stated, a
    /// lemma or hypothesis a library proof states) is never a syntax axiom,
    /// so the syntax built now is the one it would build itself.
    fn syntax_for(&self, sigs: &Layered) -> Rc<Syntax> {
        let key: Constants = sigs
            .added()
            .map(|(label, sig)| (label.clone(), sig.statement.clone()))
            .collect();
        if let Some(found) = self.syntaxes.borrow().get(&key) {
            return Rc::clone(found);
        }
        let made = Rc::new(Syntax::new(sigs));
        self.syntaxes.borrow_mut().insert(key, Rc::clone(&made));
        made
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
    /// Each sentence a step claims, said back from its kernel term as a
    /// message would say it and read again (`spoken`), with every sentence
    /// that comes back as another term kept in `Elaborated::said_back`.
    /// Only the test of what messages say turns it on.
    pub say_back: bool,
    /// What the elaborator answers to the questions the checker answers
    /// too, listed in `Elaborated::answers` for `tests/agree.rs`.
    pub list_answers: bool,
}

/// One theorem's elaborated file, and the statement it proves, which a
/// theorem citing this one reads for the order of what it pushes.
pub struct Elaborated {
    pub text: String,
    pub statement: String,
    /// Where `Options::say_back` is on, each sentence said back as another
    /// term: the sentence, what it was said back as, and its line.
    pub said_back: Vec<String>,
    /// Where `Options::list_answers` is on, the elaborator's answers.
    pub answers: Vec<String>,
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
    let syntax = library.syntax_for(&sigs);
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
    work.b.share_syntax(syntax);
    work.whole_scope = options.whole_scope_offered;
    work.said_back = options.say_back.then(Vec::new);
    work.answers = options.list_answers.then(Vec::new);
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
        "$( {}, elaborated from {} by parley build.\n",
        crate::text::spelt_in_ascii(&thm.qualified()),
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
    // A theorem this corpus proves is cited as one label, so the file that
    // elaborated it is read first and the rest comes in through it.
    for name in &work.cited {
        out.push_str(&format!("$[ {}.mm $]\n", crate::text::spelt_in_ascii(name)));
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
        Some(a) => {
            format!("( {} -> {} )", work.kernel_text(a), work.kernel_text(&goal))
        }
        None => work.kernel_text(&goal),
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
        said_back: work.said_back.take().unwrap_or_default(),
        answers: work.answers.take().unwrap_or_default(),
    })
}

/// The hypotheses of an item, as the item writes them, that no one fact of
/// the citation supplies on its own: what a message names when the item
/// gives the citation nothing.
fn unsupplied_alone(
    groups: &[citing::Group],
    parts: &Parts,
    library: &citing::Library,
) -> Vec<String> {
    let mut out = Vec::new();
    for group in groups {
        for (text, tree) in &group.wants {
            let one = std::slice::from_ref(tree);
            let mut sites = citing::Sites::new();
            crate::matching::binding_sites(tree, &library.ctx, &[], &mut sites);
            let variables = citing::names_of(one);
            let found = citing::supply(
                one,
                &parts.facts,
                &parts.seed,
                &variables,
                library,
                &sites,
                false,
            );
            if found.is_none() && !out.contains(text) {
                out.push(text.clone());
            }
        }
    }
    out
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
