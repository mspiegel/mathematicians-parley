//! Scopes: the context each line of a proof is proved under.
//!
//! This is the second of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given the blocks, hypotheses, cases and
//! `define` lines, it produces the context each line is proved under,
//! carries a fact into an inner scope, and closes a block into the claim it
//! owns. This is working in deduction form.
//!
//! Every scope is a conjunction of what has been assumed, and `frames` keeps
//! one entry per assumption: the scope with it conjoined, the assumption,
//! and what was known there. A step whose lemma forbids an inner assumption
//! is proved at an outer frame and carried back in.

use std::rc::Rc;

use indexmap::IndexMap;

use super::reading::subject_of;
use super::state::{
    fit, number_of, Binding, Block, Closer, DefineCloser, Elaborator, Frame,
    ObtainCloser, Vars,
};
use super::{Facts, Line, Lines};
use crate::binds;
use crate::corpus::{
    define_parts, fmt, item_prefix, DefineParts, Intro, Item, Step, CITED, ITEM_PREFIX,
};
use crate::matching::instantiation;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Signature;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup};
use crate::sorts::file_definitions;
use crate::{pf, regex, t, take};

regex!(OBTAINED, r"obtain\s+(.+?)(?::|\s+from\b)");
regex!(OBTAIN_ITEM, format!(r"\b({ITEM_PREFIX}{CITED})"));
regex!(INDUCTION_ON, r"induction on (\S+)");
regex!(STARTING_AT, r"starting at ([^\s,]+)");
regex!(MEMBER_OF, r"^(\S+)\s*∈\s*(.+)$");

/// What proves a claim under a widened scope, given the claim, the scope and
/// what is known there.
pub type Prove<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &Term, &str, &Facts) -> Checked<Route<Proof>> + 'p;

impl<'a> Elaborator<'a> {
    /// The first frame: the theorem's hypotheses, and what they say.
    pub fn open_outermost(&mut self, scope: &str, facts: &Facts) {
        self.frames = vec![Frame {
            scope: scope.to_string(),
            added: None,
            facts: facts.clone(),
        }];
    }

    /// Run `f` with the frames as they stand given back when it ends.
    ///
    /// A route that widens the scope to prove something under a binder or a
    /// case owns the frames it pushes and nothing else does. A frame left
    /// standing is offered to whatever is proved next.
    pub fn frames_kept<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        let frame = self.frames.len();
        let out = f(self);
        self.frames.truncate(frame);
        out
    }

    /// ( scope -> for all variable ∈ over, body ), from one member.
    ///
    /// The member is fixed, what its membership says laid beside the facts
    /// (and, where `implied`, what that membership implies), the body proved
    /// of it by `prove`, and the claim generalised by `ralrimiva`.
    ///
    /// `ralrimiva` asks that the scope not name the variable, even bound.
    /// There the claim is proved over a spare variable the scope does not
    /// name, and `renaming` says the two spellings are one claim.
    #[allow(clippy::too_many_arguments)]
    pub fn for_every(
        &mut self,
        scope: &str,
        facts: &Facts,
        body: &Term,
        variable: &Term,
        over: &Term,
        prove: &mut Prove<'_, 'a>,
        implied: bool,
    ) -> Checked<Route<Proof>> {
        let name = self.rpn(variable);
        if !scope.split_whitespace().any(|t| t == name.as_str()) {
            return self.generalised(scope, facts, body, &name, over, prove, implied);
        }
        let where_ = self.rpn(over);
        let scope_term = self.to_term(scope);
        let Some(letter) = self.unheld(&[&scope_term, body, over]) else {
            return Ok(Route::no(format!(
                "no letter left to generalise {name} over"
            )));
        };
        let spare = self.rpn(&letter);
        let again = self.restated(body, &format!("{name} cv"), &format!("{spare} cv"));
        let made = take!(
            self.generalised(scope, facts, &again, &spare, over, prove, implied)?
        );
        let said = t!(self.rpn(&again), spare, where_, "wral");
        let want = t!(self.rpn(body), name, where_, "wral");
        let across = self.renaming(&self.to_term(&said), &self.to_term(&want))?;
        let Some(across) = across else {
            return Ok(Route::no(format!(
                "the scope names {name}, and the claim over another name is not carried back to it"
            )));
        };
        Ok(Built(self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &said, "ch" => &want},
            &[&made, &across],
        )))
    }

    /// `for_every` where the scope does not name the variable.
    #[allow(clippy::too_many_arguments)]
    fn generalised(
        &mut self,
        scope: &str,
        facts: &Facts,
        body: &Term,
        name: &str,
        over: &Term,
        prove: &mut Prove<'_, 'a>,
        implied: bool,
    ) -> Checked<Route<Proof>> {
        let where_ = self.rpn(over);
        let member = t!(format!("{name} cv"), where_, "wcel");
        let made = self.frames_kept(|me| -> Checked<Route<Proof>> {
            let (inner, lifted) = me.widen(scope, facts, &member, None);
            let lifted = if implied {
                let held = lifted.get(&member).expect("the membership just laid down");
                let more = me.implied(&member, &held, &inner);
                let out = lifted.copy();
                for (k, v) in more {
                    out.set(k, v);
                }
                out
            } else {
                lifted
            };
            prove(me, body, &inner, &lifted)
        })?;
        let made = take!(made);
        Ok(Built(
            pf!(self.b; scope, self.rpn(body), name, where_, made, "ralrimiva"),
        ))
    }

    /// Conjoin one more thing onto the antecedent, carrying the facts.
    ///
    /// This is what every block form does when it opens. The frame is kept so
    /// that a step whose lemma forbids the innermost assumption can be proved
    /// without it. `origin` is what on the page the assumption is, where it
    /// is on the page at all.
    pub fn widen(
        &mut self,
        scope: &str,
        facts: &Facts,
        added: &str,
        origin: Option<&str>,
    ) -> (String, Facts) {
        self.widen_to(scope, facts, added, origin, 4)
    }

    /// `widen`, taking the assumption apart `depth` conjunctions deep: an
    /// `obtain` says as many things as its claim has sentences, and each is
    /// a fact a later step may cite on its own.
    pub fn widen_to(
        &mut self,
        scope: &str,
        facts: &Facts,
        added: &str,
        origin: Option<&str>,
        depth: usize,
    ) -> (String, Facts) {
        let inner = t!(scope, added, "wa");
        let lifted = Facts::new();
        let weaken = pf!(self.b; scope, added, "simpl");
        for (k, v) in facts.entries() {
            let carried = pf!(self.b; inner, scope, k, weaken, v, "syl");
            lifted.set(k, carried);
        }
        let mut here = pf!(self.b; scope, added, "simpr");
        if let Some(origin) = origin {
            here = self.seal(here, origin);
        }
        lifted.set(added, here.clone());
        self.unpack(added, &here, &inner, &lifted, depth);
        // Each frame keeps what is known at it, because a step whose lemma
        // forbids an inner assumption is proved at an outer one. What is
        // known at the frame widened is what has been proved there up to
        // now, the lines written since it opened included.
        if let Some(widened) = self.frames.last_mut().filter(|f| f.scope == scope) {
            widened.facts = facts.clone();
        }
        self.frames.push(Frame {
            scope: inner.clone(),
            added: Some(added.to_string()),
            facts: lifted.clone(),
        });
        (inner, lifted)
    }

    /// A proof made under `at`, said under `scope`, if `scope` is `at`
    /// widened; None otherwise.
    pub fn lifted_to(
        &self,
        claim: &str,
        proof: &Proof,
        at: &str,
        scope: &str,
    ) -> Option<Proof> {
        if at == scope {
            return Some(proof.clone());
        }
        let mut chain = Vec::new();
        let mut node = self.to_term(scope);
        let mut reached = false;
        while node.variable().is_none()
            && node.label() == Some("wa")
            && node.children().len() == 2
        {
            let (outer, added) =
                (node.children()[0].clone(), node.children()[1].clone());
            chain.push(self.rpn(&added));
            if self.rpn(&outer) == at {
                reached = true;
                break;
            }
            node = outer;
        }
        if !reached {
            return None;
        }
        let mut here = at.to_string();
        let mut proof = proof.clone();
        for added in chain.iter().rev() {
            let inner = t!(here, added, "wa");
            proof = pf!(self.b; inner, here, claim, pf!(self.b; here, added, "simpl"), proof, "syl");
            here = inner;
        }
        (here == scope).then_some(proof)
    }

    /// A conjunctive goal, from whatever answers each of its parts; None
    /// where the goal is not one of these shapes, which is not a decline:
    /// the caller has its own way on and this had no opinion.
    pub fn conjoined(
        &mut self,
        wanted: &Term,
        scope: &str,
        answer: &mut dyn FnMut(&mut Self, &Term) -> Checked<Route<Proof>>,
    ) -> Checked<Option<Route<Proof>>> {
        let Some(join) = wanted.label().and_then(|l| lookup(rules::JOIN, l)) else {
            return Ok(None);
        };
        let mut under = Vec::new();
        for one in wanted.children() {
            under.push(answer(self, one)?);
        }
        let mut proofs = Vec::new();
        for one in under {
            match one {
                Built(p) => proofs.push(p),
                Declined(d) => return Ok(Some(Declined(d))),
            }
        }
        let parts: Vec<String> =
            wanted.children().iter().map(|c| self.rpn(c)).collect();
        let mut all: Vec<crate::mm::spell::Part> = vec![crate::elab::part(scope)];
        all.extend(parts.iter().map(|p| crate::elab::part(p)));
        all.extend(proofs.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(join));
        Ok(Some(Built(self.b.proof(&all))))
    }

    /// Record each conjunct of a fact as a fact of its own.
    pub fn unpack(
        &self,
        term: &str,
        proof: &Proof,
        scope: &str,
        facts: &Facts,
        depth: usize,
    ) {
        if depth == 0 {
            return;
        }
        let node = self.to_term(term);
        let Some(picks) = node.label().and_then(|l| lookup(rules::SPLIT, l)) else {
            return;
        };
        if picks.len() != node.children().len() {
            return;
        }
        let kids: Vec<String> = node.children().iter().map(|c| self.rpn(c)).collect();
        for (part, pick) in kids.iter().zip(picks.iter()) {
            if facts.has(part) {
                continue;
            }
            let mut all: Vec<crate::mm::spell::Part> = vec![
                crate::elab::part(scope),
                crate::elab::part(term),
                crate::elab::part(part),
                crate::elab::part(proof),
            ];
            all.extend(kids.iter().map(|k| crate::elab::part(k)));
            all.push(crate::elab::part(*pick));
            all.push(crate::elab::part("syl"));
            let made = self.b.proof(&all);
            facts.set(part.clone(), made.clone());
            self.unpack(part, &made, scope, facts, depth - 1);
        }
    }

    /// A block's assumption is conjoined onto the antecedent. All four block
    /// forms do this; what differs is the lemma that closes them.
    pub fn open_block(
        &mut self,
        step: &Step,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Block> {
        let head = step.just.head.to_string();
        let mut block = Block {
            owner: step.clone(),
            outer: scope.to_string(),
            outside: facts.clone(),
            frame: self.frames.len() - 1,
            scope: scope.to_string(),
            facts: facts.clone(),
            supposed: None,
            over: None,
            base: None,
            variable: None,
            // Taken before the block names anything, so that what it names is
            // what closing it gives back.
            named: self.names.clone(),
            bound: self.bound_as.clone(),
            inner: IndexMap::new(),
            assumed: IndexMap::new(),
            entered: None,
            case_opened_at: None,
            opened_at: 0,
            claim: String::new(),
            proof: None,
            parts: IndexMap::new(),
        };
        match head.as_str() {
            "contradiction" => {
                let o = &step.openers[0];
                let node =
                    self.read(&self.hypothesis_formula(o.kind.as_str(), &o.text))?;
                let supposed = self.term(&node)?;
                let origin = assumption(&block, &o.label);
                let (inner, lifted) =
                    self.widen(scope, facts, &supposed, Some(&origin));
                if !o.label.is_empty() {
                    let proof = lifted
                        .get(&supposed)
                        .expect("the supposition just laid down");
                    self.lines.set(
                        o.label.clone(),
                        Line {
                            term: supposed.clone(),
                            proof,
                            sentences: vec![node],
                        },
                    );
                }
                block.supposed = Some(supposed);
                block.scope = inner;
                block.facts = lifted;
                self.contradicted = None;
            }
            "fix" => {
                for o in &step.openers {
                    let body = self.hypothesis_formula(o.kind.as_str(), &o.text);
                    if o.kind == Intro::Let {
                        // A fixed name is a variable of the kernel, not a
                        // class, and it must avoid whatever the notations
                        // bind.
                        let node = self.read(&body)?;
                        let name = subject_of(&node).text.clone();
                        let var = self.fixed_var(&name, &block.scope.clone())?;
                        self.names.insert(name.clone(), format!("{var} cv"));
                        block.variable = Some(var);
                        // `let X be a set` fixes a name over nothing, so
                        // there is no set to record.
                        if node.notation == "membership" {
                            let set = self.term(&node.children[1])?;
                            self.sets.insert(name, set);
                        }
                    }
                    let node = self.read(&body)?;
                    let added = self.term(&node)?;
                    let origin = assumption(&block, &o.label);
                    let (inner, lifted) = self.widen(
                        &block.scope.clone(),
                        &block.facts.clone(),
                        &added,
                        Some(&origin),
                    );
                    block.scope = inner;
                    block.facts = lifted;
                    if !o.label.is_empty() {
                        let proof = block
                            .facts
                            .get(&added)
                            .expect("the assumption just laid down");
                        self.lines.set(
                            o.label.clone(),
                            Line {
                                term: added,
                                proof,
                                sentences: vec![node],
                            },
                        );
                    }
                }
            }
            "cases" => {
                // Every other block opens one scope for all its children. A
                // `cases` opens one per part, so nothing is widened here and
                // the part is entered when its first child arrives.
                for o in &step.openers {
                    let body = self.hypothesis_formula(o.kind.as_str(), &o.text);
                    let node = self.read(&body)?;
                    block
                        .assumed
                        .insert(o.part.unwrap_or(0), (node, o.label.clone()));
                }
            }
            "induction" => {
                let over = INDUCTION_ON
                    .captures(&step.just.text)
                    .map(|m| m[1].to_string())
                    .expect("an induction says what it is on");
                block.over = Some(over);
                let base = self.spare_var()?;
                // The step part fixes a name of its own, and `nn0indd` wants
                // that one apart from this.
                self.taken.insert(base.clone());
                block.base = Some(base);
            }
            _ => {
                return Err(
                    self.defect(step.line, format!("no expansion for a {head} block"))
                );
            }
        }
        Ok(block)
    }

    /// Open the scope one case of a `cases` block runs under.
    pub fn enter_case(
        &mut self,
        block: &mut Block,
        part: usize,
    ) -> Checked<(String, Facts)> {
        if block.entered == Some(part) {
            return Ok((block.scope.clone(), block.facts.clone()));
        }
        self.frames.truncate(block.frame + 1);
        // A case gives back what it named, the way the block does when it
        // closes: the next one starts from where the block started.
        self.names = block.named.clone();
        let (node, label) = block.assumed[&part].clone();
        let assumed = self.term(&node)?;
        let origin = assumption(block, &label);
        let (inner, lifted) = self.widen(
            &block.outer.clone(),
            &block.outside.clone(),
            &assumed,
            Some(&origin),
        );
        block.scope = inner;
        block.facts = lifted;
        block.entered = Some(part);
        if !label.is_empty() {
            let proof = block.facts.get(&assumed).expect("the case just laid down");
            self.lines.set(
                label,
                Line {
                    term: assumed,
                    proof,
                    sentences: vec![node],
                },
            );
        }
        Ok((block.scope.clone(), block.facts.clone()))
    }

    /// The cases that are the claim and come before part `before`, or all of
    /// them: each has no steps, and what it shows is what it assumes.
    pub fn settle_claimed(
        &mut self,
        block: &mut Block,
        closers: Vec<Closer>,
        before: Option<usize>,
    ) -> Checked<Vec<Closer>> {
        let mut closers = closers;
        for o in block.owner.openers.clone() {
            let Some(part) = o.part.filter(|_| o.is_claim) else {
                continue;
            };
            if block.parts.contains_key(&part) || before.is_some_and(|b| part >= b) {
                continue;
            }
            closers = self.end_case(block, closers)?;
            let (scope, facts) = self.enter_case(block, part)?;
            block.case_opened_at = Some(closers.len());
            let claim = self.claim_of(&block.owner.claim_text())?;
            let assumed = self.term(&block.assumed[&part].0)?;
            if assumed != claim {
                return Err(self
                    .defect(o.line, "the case's assumption is not the block's claim"));
            }
            let proof = facts.get(&assumed).expect("the case just laid down");
            block.parts.insert(part, (claim, proof, scope));
        }
        Ok(closers)
    }

    /// The closers an obtain raised inside a case, spent where it ends: the
    /// lemma that closes the cases wants each case over the scope the case
    /// opened.
    pub fn end_case(
        &mut self,
        block: &mut Block,
        closers: Vec<Closer>,
    ) -> Checked<Vec<Closer>> {
        let Some(opened) = block.case_opened_at else {
            return Ok(closers);
        };
        let inside = &closers[opened..];
        if let (false, Some(entered)) = (inside.is_empty(), block.entered) {
            if let Some((claim, proof, _where)) = block.parts.get(&entered).cloned() {
                let mut proof = proof;
                for close in inside.iter().rev() {
                    proof = self.close(close, proof, &claim)?;
                }
                block
                    .parts
                    .insert(entered, (claim, proof, block.scope.clone()));
            }
        }
        Ok(closers[..opened].to_vec())
    }

    /// A closed block is the result of the part of its parent it sits in,
    /// with what it was proved under.
    pub fn hand_up(done: &Block, blocks: &mut [Block]) {
        if let (Some(part), Some(parent)) = (done.owner.part, blocks.last_mut()) {
            parent.parts.insert(
                part,
                (
                    done.claim.clone(),
                    done.proof.clone().expect("a closed block's proof"),
                    done.outer.clone(),
                ),
            );
            if done.variable.is_some() {
                parent.variable = done.variable.clone();
            }
        }
    }

    /// What a block gives back, by the lemma its kind closes with.
    ///
    /// An `obtain` inside a block discharges where the block does, since the
    /// lemma that closes the block wants what the block holds and not what
    /// the obtain's scope holds.
    pub fn close_block(
        &mut self,
        block: &mut Block,
        facts: &Facts,
        closers: Vec<Closer>,
        deep: &str,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        let step = block.owner.clone();
        let head = step.just.head.to_string();
        let inside: Vec<Closer> =
            closers[block.opened_at.min(closers.len())..].to_vec();
        // A block gives back its scope and its names together.
        block.inner = self.bound_as.clone();
        self.frames.truncate(block.frame + 1);
        self.names = block.named.clone();
        self.bound_as = block.bound.clone();
        let mut closers = closers;
        let (claim, proof) = match head.as_str() {
            "contradiction" => {
                let made = self.close_contradiction(block, facts, &inside, deep)?;
                closers.truncate(block.opened_at);
                made
            }
            "fix" => {
                let last = self.last.clone().expect("a block's last step");
                let held = self.lines.get(&last).expect("the block's last line");
                let made = self.close_fix(block, &held, &inside)?;
                closers.truncate(block.opened_at);
                made
            }
            "cases" => {
                closers = self.end_case(block, closers)?;
                self.close_cases(block)?
            }
            _ => self.close_induction(block)?,
        };
        let number = number_of(&step);
        let proof = self.check_step(proof, &step, &number, true)?;
        block.claim = claim.clone();
        block.proof = Some(proof.clone());
        let outer = block.outside.copy();
        outer.set(claim.clone(), proof.clone());
        // A block's claim is a line like any other, which a later step may
        // rewrite: Cantor's x ∉ B, shown by cases, becomes x ∉ f(x).
        let said = self.said(&step)?;
        self.lines.set(
            number.clone(),
            Line {
                term: claim,
                proof,
                sentences: said,
            },
        );
        self.last = Some(number);
        Ok((block.outer.clone(), outer, closers))
    }

    /// A contradiction closes on its last step and the line that step
    /// contradicts: `pm2.21dd` takes the pair to the block's claim first, the
    /// obtains raised inside the block discharge that, and the supposition is
    /// dropped last.
    fn close_contradiction(
        &mut self,
        block: &Block,
        facts: &Facts,
        inside: &[Closer],
        deep: &str,
    ) -> Checked<(String, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let supposed = block.supposed.clone().unwrap_or_default();
        let Some(other) = self.contradicted.clone() else {
            return Err(
                self.defect(step.line, "the block's last step contradicts no line")
            );
        };
        let held = self.last.as_ref().and_then(|l| self.lines.get(l));
        let mut offered = vec![other];
        if let Some(h) = &held {
            offered.push(h.term.clone());
        }
        let Some((first, second, known)) = self.opposing(&offered, facts, deep) else {
            return Err(self.defect(
                step.line,
                "the last step and the line it contradicts are not a contradiction",
            ));
        };
        let claim = self.claim_of(&step.claim_text())?;
        let mut proof = pf!(self.b; deep, first, claim, known.get(&first).unwrap(), known.get(&second).unwrap(), "pm2.21dd");
        for close in inside.iter().rev() {
            proof = self.close(close, proof, &claim)?;
        }
        let lifted = pf!(self.b; scope, supposed, claim, proof, "ex");
        if claim == t!(supposed, "wn") {
            return Ok((
                claim.clone(),
                pf!(self.b; scope, supposed, lifted, "pm2.01d"),
            ));
        }
        if supposed == t!(claim, "wn") {
            return Ok((claim.clone(), pf!(self.b; scope, claim, lifted, "pm2.18d")));
        }
        Err(self.defect(
            step.line,
            "the block claims neither its supposition negated nor what its supposition denies",
        ))
    }

    /// A claim and its negation, among the parts of what the block holds.
    pub fn opposing(
        &self,
        lines: &[String],
        facts: &Facts,
        scope: &str,
    ) -> Option<(String, String, Facts)> {
        let known = facts.copy();
        for line in lines {
            if let Some(p) = known.get(line) {
                self.unpack(line, &p, scope, &known, 4);
            }
        }
        let seen: Vec<String> = lines
            .iter()
            .flat_map(|l| self.parts(l))
            .filter(|t| known.has(t))
            .collect();
        for one in &seen {
            for other in &seen {
                if *other == t!(one, "wn") {
                    return Some((one.clone(), other.clone(), known));
                }
            }
        }
        None
    }

    /// A fact and every conjunct inside it, the whole one first.
    pub fn parts(&self, term: &str) -> Vec<String> {
        let mut out = vec![term.to_string()];
        let node = self.to_term(term);
        if let Some(picks) = node.label().and_then(|l| lookup(rules::SPLIT, l)) {
            if picks.len() == node.children().len() {
                for child in node.children() {
                    out.extend(self.parts(&self.rpn(child)));
                }
            }
        }
        out
    }

    /// A fix closed by giving back everything it took: `ralrimiva` for what
    /// was proved under a fixed name, `ex` for what the block assumed, read
    /// off the claim the block states, in the order the openers widened the
    /// scope, and put back innermost first.
    fn close_fix(
        &mut self,
        block: &Block,
        held: &Line,
        inside: &[Closer],
    ) -> Checked<(String, Proof)> {
        let step = &block.owner;
        // Read with the variables the block had, not the ones given back.
        let kept = std::mem::replace(&mut self.bound_as, block.inner.clone());
        let claim = self.claim_of(&step.claim_text());
        self.bound_as = kept;
        let claim = claim?;
        let mut layers: Vec<(&'static str, String, Option<String>)> = Vec::new();
        let mut rest = self.to_term(&claim);
        for o in &step.openers {
            if o.kind == Intro::Let && rest.label() == Some("wral") {
                let kids = rest.children().to_vec();
                layers.push((
                    "ralrimiva",
                    self.rpn(&kids[1]),
                    Some(self.rpn(&kids[2])),
                ));
                rest = kids[0].clone();
            } else if o.kind == Intro::Let && rest.label() == Some("wal") {
                // `let X be a set` fixes a name over nothing, so the claim
                // says its body of every set there is and `alrimiv` gives
                // that back.
                let kids = rest.children().to_vec();
                layers.push(("alrimiv", self.rpn(&kids[1]), None));
                rest = kids[0].clone();
            } else if o.kind == Intro::Assume && rest.label() == Some("wi") {
                let kids = rest.children().to_vec();
                layers.push(("ex", self.rpn(&kids[0]), None));
                rest = kids[1].clone();
            } else if o.kind == Intro::Let {
                return Err(self.defect(
                    step.line,
                    "a fix that claims nothing of every such name",
                ));
            } else {
                return Err(self.defect(
                    step.line,
                    "a fix whose claim supposes nothing where the block assumes",
                ));
            }
        }
        // The scope each layer was taken at, which is what it is given back
        // to.
        let mut scopes = Vec::new();
        let mut scope = block.outer.clone();
        for (how, what, over) in &layers {
            scopes.push(scope.clone());
            scope = if *how == "ex" {
                t!(scope, what, "wa")
            } else {
                t!(
                    scope,
                    t!(
                        format!("{what} cv"),
                        over.as_deref().unwrap_or("cvv"),
                        "wcel"
                    ),
                    "wa"
                )
            };
        }
        // An `obtain` inside the block widened the scope past what the
        // openers widened it to, and discharges where the block does.
        let mut proof = held.proof.clone();
        let said = held.term.clone();
        for close in inside.iter().rev() {
            proof = self.close(close, proof, &said)?;
        }
        // The last line and the claim are written in different places, so a
        // name bound in both may be spelt two ways.
        let want = self.rpn(&rest);
        let Some(mut proof) = self.respelt(&proof, &said, &want, &scope)? else {
            return Err(self.defect(
                step.line,
                "the block does not reach what it claims of the name it fixed",
            ));
        };
        let mut said = want;
        for ((how, what, over), outer) in layers.iter().zip(scopes.iter()).rev() {
            match *how {
                "ex" => {
                    proof = pf!(self.b; outer, what, said, proof, "ex");
                    said = t!(what, said, "wi");
                }
                "alrimiv" => {
                    // `let X be a set` says X ∈ _V and the claim quantifies
                    // X over nothing, so that membership is dropped before
                    // the name is given back: every setvar is a set.
                    let member = t!(format!("{what} cv"), "cvv", "wcel");
                    let vex = self.b.ap("vex", &binds! {"x" => what}, &[]);
                    proof = pf!(self.b; outer, member, said, vex, proof, "mpan2");
                    proof = pf!(self.b; outer, said, what, proof, "alrimiv");
                    said = t!(said, what, "wal");
                }
                _ => {
                    let over = over.clone().unwrap_or_default();
                    proof = pf!(self.b; outer, said, what, over, proof, "ralrimiva");
                    said = t!(said, what, over, "wral");
                }
            }
        }
        Ok((claim, proof))
    }

    /// The cases and the disjunction that says one of them holds: `jaodan`
    /// makes one case of the first two over their disjunction, and so on
    /// down, and `mpjaodan` closes on the last.
    fn close_cases(&mut self, block: &Block) -> Checked<(String, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let parts: std::collections::BTreeSet<usize> =
            block.parts.keys().copied().collect();
        let assumed_parts: std::collections::BTreeSet<usize> =
            block.assumed.keys().copied().collect();
        if parts != assumed_parts {
            return Err(self.defect(step.line, "a case of the block proves nothing"));
        }
        let claim = self.claim_of(&step.claim_text())?;
        let order: Vec<usize> = assumed_parts.into_iter().collect();
        let mut assumed = Vec::new();
        for p in &order {
            let node = block.assumed[p].0.clone();
            assumed.push(self.term(&node)?);
        }
        let said: Vec<Proof> = order.iter().map(|p| block.parts[p].1.clone()).collect();
        let mut which = assumed[0].clone();
        let mut proof = said[0].clone();
        let last = assumed.len() - 1;
        for (one, shown) in assumed[1..last].iter().zip(said[1..last].iter()) {
            proof = self.b.ap(
                "jaodan",
                &binds! {"ph" => scope, "ps" => &which, "ch" => &claim, "th" => one},
                &[&proof, shown],
            );
            which = t!(which, one, "wo");
        }
        let cited = step.just.refs[0].clone();
        let disjunction = self.carried(&cited, &block.outside, &self.lines.clone());
        let cited_term = self.lines.get(&cited).map(|l| l.term).unwrap_or_default();
        if t!(which, assumed[last], "wo") != cited_term {
            return Err(self.defect(
                step.line,
                "the cases are not the disjunction the block cites, taken in order",
            ));
        }
        let proof = self.b.ap(
            "mpjaodan",
            &binds! {"ph" => scope, "ps" => &which, "ch" => &claim, "th" => &assumed[last]},
            &[&proof, &said[last], &disjunction],
        );
        Ok((claim, proof))
    }

    /// Induction closes with the lemma for the set it runs over. It wants the
    /// claim five ways and the text writes none of them, so the claim is
    /// read as a function of the name and instantiated, and each instance is
    /// tied to the general one by congruence.
    fn close_induction(&mut self, block: &Block) -> Checked<(String, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let keys: std::collections::BTreeSet<usize> =
            block.parts.keys().copied().collect();
        if keys != [0usize, 1].into_iter().collect() {
            return Err(self.defect(step.line, "induction wants a base and a step"));
        }
        let (base_claim, base, beneath) = block.parts[&0].clone();
        let (mut step_claim, mut stepped, mut under) = block.parts[&1].clone();
        let name = block.over.clone().unwrap_or_default();
        let general = format!("{} cv", block.base.clone().unwrap_or_default());
        let over = self.sets.get(&name).cloned();
        let found = over.as_deref().and_then(|o| lookup(rules::INDUCTION, o));
        let Some((lemma, begins)) = found else {
            let message = match &over {
                Some(o) => format!("nothing here inducts over {}", self.render(o)),
                None => format!("nothing says what {name} runs over"),
            };
            return Err(self.defect(step.line, message));
        };
        let over = over.unwrap_or_default();
        let start = match STARTING_AT.captures(&step.just.text) {
            Some(m) => {
                let node = self.read(&m[1])?;
                self.term(&node)?
            }
            None => begins.to_string(),
        };
        if start != begins {
            return Err(self.defect(
                step.line,
                format!(
                    "an induction over {} starts at {}, and the text says {}",
                    self.render(&over),
                    self.render(begins),
                    self.render(&start)
                ),
            ));
        }
        let variable = match &block.variable {
            Some(v) => v.clone(),
            None => self.spare_var()?,
        };
        let next_one = t!(format!("{variable} cv"), "c1", "caddc", "co");
        let claim_text = step.claim_text();
        let pattern = self.names_kept(|me| -> Checked<crate::formula::Node> {
            me.names.insert(name.clone(), general.clone());
            // Read as a sentence, so that a claim written as prose ends
            // where a reader ends it.
            let said = me.sentences(&claim_text);
            let text = if said.len() == 1 {
                said[0].clone()
            } else {
                claim_text.clone()
            };
            let node = me.read(&text)?;
            me.freeze(&node)
        })?;
        let named = self.names.get(&name).cloned().unwrap_or_default();
        let shapes = [
            start.clone(),
            format!("{variable} cv"),
            next_one,
            named.clone(),
        ];
        let mut instances = Vec::new();
        let mut ties = Vec::new();
        for value in &shapes {
            let here = t!(general, value, "wceq");
            let identity = pf!(self.b; here, "id");
            match self.rewrite(&pattern, &general, value, &here, &identity)? {
                Built((built, proof)) => {
                    instances.push(built);
                    ties.push(proof);
                }
                Declined(d) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "the claim is not about the induction variable: {}",
                            self.say(&d)
                        ),
                    ));
                }
            }
        }
        let (claimed, held, reached, whole) = (
            instances[0].clone(),
            instances[1].clone(),
            instances[2].clone(),
            instances[3].clone(),
        );
        let member = t!(
            named,
            self.sets.get(&name).cloned().unwrap_or_default(),
            "wcel"
        );
        let body = self.term(&pattern)?;

        // A part gives back what it claims, and what a `fix` claims is a
        // universal. `nn0indd` asks its step as a deduction, so the one is
        // turned into the other here, which is where the lemma is known. The
        // step is put into the lemma's spelling while it is still a
        // universal.
        let taken = self.to_term(&step_claim);
        if taken.label() == Some("wral") && taken.children()[0].label() == Some("wi") {
            let says = t!(held, reached, "wi");
            let wanted = t!(says, variable, over, "wral");
            let Some(respelt) = self.respelt(&stepped, &step_claim, &wanted, &under)?
            else {
                return Err(
                    self.defect(step.line, "the step does not reach the next instance")
                );
            };
            let inner = t!(under, t!(format!("{variable} cv"), over, "wcel"), "wa");
            stepped = pf!(self.b; under, says, variable, over, respelt, "r19.21bi");
            stepped = pf!(self.b; inner, held, reached, stepped, "imp");
            step_claim = reached.clone();
            under = t!(inner, held, "wa");
        }
        let base = self.respelt(&base, &base_claim, &claimed, &beneath)?;
        let stepped = self.respelt(&stepped, &step_claim, &reached, &under)?;
        let Some(stepped) = stepped else {
            return Err(
                self.defect(step.line, "the step does not reach the next instance")
            );
        };
        let Some(base) = base else {
            return Err(
                self.defect(step.line, "the base does not reach the first instance")
            );
        };
        let mut all: Vec<crate::mm::spell::Part> = Vec::new();
        let pieces = [
            scope.clone(),
            body,
            claimed,
            held,
            reached,
            whole.clone(),
            block.base.clone().unwrap_or_default(),
            variable,
            named,
        ];
        all.extend(pieces.iter().map(|p| crate::elab::part(p)));
        all.extend(ties.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(&base));
        all.push(crate::elab::part(&stepped));
        all.push(crate::elab::part(lemma));
        let run = self.b.proof(&all);
        // The lemma states the membership apart from the rest of the
        // antecedent, and the scope already holds it, so the two are
        // conjoined back.
        let Some(held_member) = block.outside.get(&member) else {
            return Err(
                self.defect(step.line, format!("nothing in scope says {member}"))
            );
        };
        let both = pf!(self.b; scope, scope, member, pf!(self.b; scope, "id"), held_member, "jca");
        Ok((
            whole.clone(),
            pf!(self.b; scope, t!(scope, member, "wa"), whole, both, run, "syl"),
        ))
    }

    /// Names introduced from an existence claim, which opens a scope.
    ///
    /// This is the step that changes the shape of every step after it: the
    /// kernel cannot hand a name out of an existential, so everything below
    /// is proved as the body of an implication and the existential is
    /// discharged at the very end.
    pub fn obtain(
        &mut self,
        step: &Step,
        number: &str,
        scope: &str,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        let got: Vec<String> = OBTAINED
            .captures(&step.just.text)
            .map(|m| m[1].split(',').map(|n| str::trim(n).to_string()).collect())
            .expect("an obtain names what it obtains");
        let named = OBTAIN_ITEM
            .captures(&step.just.text)
            .map(|m| m[1].to_string());
        let (mut ex, mut p_ex);
        match &named {
            None => {
                // The line already claims the existence, so there is no item
                // to instantiate and nothing of its own to rename.
                let where_ = step.just.refs.first().cloned();
                let held = where_.as_ref().and_then(|w| self.lines.get(w));
                let (Some(where_), Some(held)) = (where_, held) else {
                    return Err(self.defect(
                        step.line,
                        "an obtain that names neither an item nor a line claiming the existence",
                    ));
                };
                ex = held.term.clone();
                p_ex = self.carried(&where_, facts, &self.lines.clone());
                // Eliminating an existential puts the name it binds into the
                // scope, and the lemma that does it forbids that name in what
                // the scope already says. So the claim is respelt first, over
                // names nothing else holds.
                let standing: std::collections::BTreeSet<String> = scope
                    .split_whitespace()
                    .filter(|t| {
                        self.b
                            .sigs
                            .get(t)
                            .is_some_and(|s| s.kind == crate::mm::Kind::Float)
                    })
                    .map(String::from)
                    .collect();
                let binders: Vec<String> = self
                    .bound_in(&self.to_term(&ex))
                    .iter()
                    .map(|v| self.float_of(v))
                    .collect();
                let renames = got
                    .iter()
                    .zip(binders.iter())
                    .any(|(name, letter)| self.bound_as.get(name) != Some(letter));
                if binders.iter().any(|b| standing.contains(b)) || renames {
                    let fresh = self.renamed(&ex, got.len())?;
                    let apart =
                        self.renaming(&self.to_term(&ex), &self.to_term(&fresh))?;
                    let Some(apart) = apart else {
                        return Err(self.defect(
                            step.line,
                            "the existence this obtains from binds a name the scope already holds",
                        ));
                    };
                    let turned = pf!(self.b; t!(ex, fresh, "wb"), scope, apart, "a1i");
                    p_ex = pf!(self.b; scope, ex, fresh, p_ex, turned, "mpbid");
                    ex = fresh;
                }
            }
            Some(item_name)
                if item_prefix(item_name).is_some()
                    && self.item_cited(item_name).unfolds() =>
            {
                // The existence is the one the step's claim states, over
                // names nothing else holds, reached as a step claiming it
                // would reach it.
                let item = self.item_cited(item_name);
                let claimed = self.existence_claimed(step, &got)?;
                ex = self.renamed(&claimed, got.len())?;
                let lines = self.lines.clone();
                p_ex = match self.trying(
                    item,
                    step,
                    super::elaborate::Way::Unfolded,
                    &ex,
                    scope,
                    facts,
                    &lines,
                    None,
                )? {
                    Built(p) => p,
                    Declined(_) => {
                        return Err(self.defect(
                            step.line,
                            format!(
                                "nothing step {number} cites says {}",
                                self.render(&ex)
                            ),
                        ));
                    }
                };
            }
            Some(item_name) => {
                let cites = str::trim(
                    step.just.text.split_once(':').map(|(_, r)| r).unwrap_or(""),
                )
                .to_string();
                let item = self.item_cited(item_name);
                let claimed = self.names_kept(|me| -> Checked<String> {
                    for (name, value) in instantiation(&cites) {
                        let node = me.read(&value)?;
                        let term = me.term(&node)?;
                        me.names.insert(name, term);
                    }
                    // A name is a variable of the kernel whatever it is
                    // spelt with, and a spare stands for it as one does for
                    // a binder's name.
                    for name in &got {
                        let var = me.binder_var(name)?;
                        me.names.insert(name.clone(), format!("{var} cv"));
                    }
                    // A library item says its existential in its own names,
                    // and the step's lines say what those stand for.
                    let node = match item {
                        Item::Record(r) => me.item_sentence_here(
                            step,
                            r,
                            Some(&cites),
                            &Self::claimed_by(item),
                        )?,
                        Item::Theorem(_) => me.read(&Self::claimed_by(item))?,
                    };
                    me.term(&node)
                })?;
                // An item states its existential in its own names, and a
                // binder takes the variable its name is spelled with, so the
                // one obtained is renamed to a variable nothing else holds.
                ex = self.renamed(&claimed, got.len())?;
                p_ex = match self.cite_item(
                    step,
                    &ex,
                    scope,
                    facts,
                    item,
                    Some(&cites),
                )? {
                    Built(p) => p,
                    Declined(d) => {
                        panic!("an item cited for an obtain declined: {}", self.say(&d))
                    }
                };
            }
        }
        // What the line is obtained from is what it rests on; what it
        // introduces is sealed below with the same name.
        let p_ex = self.check_step(p_ex, step, number, false)?;

        // The existential says which names it introduces and where they run,
        // so the scope is read off it rather than off the text.
        let mut layers: Vec<(String, String)> = Vec::new();
        let mut rest = self.to_term(&ex);
        while layers.len() < got.len() {
            let kids = rest.children().to_vec();
            layers.push((self.rpn(&kids[1]), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        let body = self.rpn(&rest);
        let memberships: Vec<String> = layers
            .iter()
            .map(|(v, s)| t!(format!("{v} cv"), s, "wcel"))
            .collect();
        let mut member = memberships.join(" ");
        if layers.len() > 1 {
            member = t!(member, "wa");
        }
        for (name, (variable, over_term)) in got.iter().zip(layers.iter()) {
            self.names.insert(name.clone(), format!("{variable} cv"));
            self.sets.insert(name.clone(), over_term.clone());
        }
        // Read after the obtained names are bound, so a sentence naming one of
        // them is about the variable the existential introduced.
        let sentences = self.said(step)?;
        // The body is taken apart as deep as the sentences the claim wrote
        // for it, as any line saying several things is; the claim's other
        // sentences are the memberships.
        let deep = sentences.len().saturating_sub(got.len() + 1);
        // A point is a point as `let A be a point` says it is: a sort, which
        // a step rests on without citing the line and the checker does not
        // let it cite. A number obtained is cited for its membership, as a
        // requires line from the obtain.
        let points = got.iter().all(|name| {
            self.sorts_now
                .get(name)
                .is_some_and(|s| s.name() == Some("point"))
        });
        let members = if points {
            let sort = format!("{number}∈");
            self.sorts.insert(sort.clone());
            sort
        } else {
            number.to_string()
        };
        let (outer, held) = self.widen(scope, facts, &member, Some(&members));
        let (inner, lifted) = self.widen_to(&outer, &held, &body, Some(number), deep);
        self.lines.set(
            number,
            Line {
                term: body.clone(),
                proof: lifted.get(&body).expect("the body just laid down"),
                sentences,
            },
        );
        let discharge = if layers.len() == 1 {
            "rexlimdva"
        } else {
            "rexlimdvva"
        };
        let mut pushed: Vec<String> = layers.iter().map(|(v, _)| v.clone()).collect();
        pushed.extend(layers.iter().map(|(_, s)| s.clone()));
        let mut closers = closers;
        closers.push(Closer::Obtain(Rc::new(ObtainCloser {
            line: step.line,
            scope: scope.to_string(),
            ex,
            p_ex,
            body,
            outer,
            inner: inner.clone(),
            pushed,
            layers,
            discharge,
        })));
        Ok((inner, lifted, closers))
    }

    /// What a scope's closer makes of a proof and its goal where the scope
    /// ends.
    pub fn close(
        &mut self,
        closer: &Closer,
        proof: Proof,
        goal: &str,
    ) -> Checked<Proof> {
        match closer {
            Closer::Obtain(c) => self.close_obtain(c, proof, goal),
            Closer::Define(c) => {
                // The claim discharged here was read before the define was,
                // so it cannot name the variable; `exlimdv` forbids it.
                if goal.split_whitespace().any(|t| t == c.var.as_str()) {
                    return Err(self.defect(
                        c.line,
                        format!(
                            "what {} names is still named where its scope ends",
                            c.label
                        ),
                    ));
                }
                let inner = pf!(self.b; c.scope, c.said, goal, proof, "ex");
                let dropped =
                    pf!(self.b; c.scope, c.said, goal, c.var, inner, "exlimdv");
                Ok(pf!(self.b; c.scope, c.ex, goal, c.p_ex, dropped, "mpd"))
            }
        }
    }

    fn discharged(&self, c: &ObtainCloser, proof: &Proof, goal: &str) -> Proof {
        let inner = pf!(self.b; c.outer, c.body, goal, proof, "ex");
        let mut all: Vec<crate::mm::spell::Part> = vec![
            crate::elab::part(&c.scope),
            crate::elab::part(&c.body),
            crate::elab::part(goal),
        ];
        all.extend(c.pushed.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(&inner));
        all.push(crate::elab::part(c.discharge));
        let eliminated = self.b.proof(&all);
        pf!(self.b; c.scope, c.ex, goal, c.p_ex, eliminated, "mpd")
    }

    /// The goal may bind the letter an obtained name stands for, and the
    /// discharge keeps the name out of the goal, so the goal is renamed apart
    /// for it and back.
    fn close_obtain(
        &mut self,
        c: &ObtainCloser,
        proof: Proof,
        goal: &str,
    ) -> Checked<Proof> {
        let words: Vec<&str> = goal.split_whitespace().collect();
        let caught: Vec<&String> = c
            .layers
            .iter()
            .map(|(v, _)| v)
            .filter(|v| words.contains(&v.as_str()))
            .collect();
        if caught.is_empty() {
            return Ok(self.discharged(c, &proof, goal));
        }
        let whole = self.to_term(goal);
        let mut moved = Binding::new();
        for v in caught {
            let mut terms: Vec<&Term> = vec![&whole];
            terms.extend(moved.values());
            let Some(letter) = self.unheld(&terms) else {
                return Err(
                    self.defect(c.line, "no letter left to rename the goal apart with")
                );
            };
            let var = self.sig(v).statement[1].clone();
            moved.insert(var, letter);
        }
        let apart = whole.substitute(&moved);
        let Some(back) = self.renaming(&apart, &whole)? else {
            return Err(self.defect(
                c.line,
                "the goal renamed apart does not read back as the goal",
            ));
        };
        let there = self.rpn(&apart);
        let turned = self.b.ap(
            "sylibr",
            &binds! {"ph" => &c.inner, "ps" => goal, "ch" => &there},
            &[&proof, &back],
        );
        let made = self.discharged(c, &turned, &there);
        Ok(self.b.ap(
            "sylib",
            &binds! {"ph" => &c.scope, "ps" => &there, "ch" => goal},
            &[&made, &back],
        ))
    }

    /// Each `define` above line `before` as a name and its equation.
    ///
    /// A textbook's "let x₁ = min(b, c + δ/2)" introduces a number and says
    /// what it is, and the steps after it are about x₁. So a define is taken
    /// the way an `obtain` is: from `∃x x = E`, which `elisset` gives once E
    /// is a set, the scope is widened by `x = E` and the existential is
    /// discharged where the scope ends (`exlimdv`).
    ///
    /// The defines are read one at a time where they stand, each with the
    /// names the ones before it gave: what the theorem sees from outside it
    /// first, then its own, stopping at the first below `before`.
    pub fn define(
        &mut self,
        before: usize,
        scope: &str,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        let mut scope = scope.to_string();
        let mut facts = facts.clone();
        let mut closers = closers;
        // What the theorem sees from outside it comes first, before its own
        // first step: written out where it was defined, and from here on a
        // name like any the theorem defines itself.
        if !self.file_given {
            self.file_given = true;
            let written = file_definitions(self.thm, self.env());
            for (name, d, src) in self.visible_outside() {
                let Some(made) = written.get(&name) else {
                    continue;
                };
                let label = self.outside_label(&name, &d, src);
                let line = if src == self.thm.scope {
                    d.line
                } else {
                    self.thm.line
                };
                let body = self.outside_term(made)?;
                (scope, facts, closers) = self
                    .one_define(&label, line, &name, &body, &scope, &facts, closers)?;
            }
        }
        while self.unread < self.thm.defines.len() {
            let d = self.thm.defines[self.unread].clone();
            if d.line >= before {
                break;
            }
            self.unread += 1;
            let said = match define_parts(&d.text) {
                Built(said) => said,
                Declined(why) => {
                    return Err(self.defect(
                        d.line,
                        format!("define {}: {}", d.label, why.reason()),
                    ));
                }
            };
            for name in said.names() {
                if self.names.contains_key(&name) {
                    return Err(self.defect(d.line, format!("{name} is already named")));
                }
            }
            match &said {
                // Sequences by recursion are one define giving several names,
                // each the map to its part of the one recursion.
                DefineParts::Recursion(r) => {
                    let maps = self.recursion_terms(&d.label, r)?;
                    for (name, made) in maps {
                        (scope, facts, closers) = self.one_define(
                            &d.label, d.line, &name, &made, &scope, &facts, closers,
                        )?;
                    }
                }
                DefineParts::One(one) => {
                    // The rule is bracketed, since a map binds tighter than a
                    // rule by cases.
                    let body = match &one.param {
                        None => one.body.clone(),
                        Some(param) => format!(
                            "the map sending {param} ∈ {} to ({})",
                            one.domain.clone().unwrap_or_default(),
                            one.body
                        ),
                    };
                    let node = self.read(&body)?;
                    let term = self.term(&node)?;
                    let made = self.apart(&term)?;
                    (scope, facts, closers) = self.one_define(
                        &d.label, d.line, &one.name, &made, &scope, &facts, closers,
                    )?;
                }
            }
        }
        Ok((scope, facts, closers))
    }

    /// One define taken: its name a spare variable, its equation laid down,
    /// and its existential left to discharge where the scope ends.
    #[allow(clippy::too_many_arguments)]
    fn one_define(
        &mut self,
        label: &str,
        line: usize,
        name: &str,
        body: &str,
        scope: &str,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(String, Facts, Vec<Closer>)> {
        self.at = line;
        let body = body.to_string();
        let var = self.spare_var()?;
        let said = t!(format!("{var} cv"), body, "wceq");
        let ex = t!(said, var, "wex");
        let p_ex = match self.apply_lemma(
            "elisset",
            &self.to_term(&ex),
            scope,
            facts,
            None,
            false,
            None,
        )? {
            Built(p) => p,
            Declined(d) => {
                return Err(self.defect(
                    line,
                    format!(
                        "cannot show that what {label} names is a set: {}",
                        self.say(&d)
                    ),
                ));
            }
        };
        // That the body is a set is the define's own and rests on the
        // define.
        let p_ex = self.seal(p_ex, label);
        let (outer, held) = self.widen(scope, facts, &said, Some(label));
        self.names.insert(name.to_string(), format!("{var} cv"));
        self.definitions.insert(var.clone(), body);
        self.defined_by.insert(var.clone(), label.to_string());
        // What a term comes to in standard form now reads this name as its
        // body, and a form worked out before could hold the name as it stood.
        self.standards.clear();
        self.lines.set(
            label,
            Line {
                term: said.clone(),
                proof: held.get(&said).expect("the equation just laid down"),
                sentences: Vec::new(),
            },
        );
        let mut closers = closers;
        closers.push(Closer::Define(Rc::new(DefineCloser {
            scope: scope.to_string(),
            said,
            var,
            ex,
            p_ex,
            line,
            label: label.to_string(),
        })));
        Ok((outer, held, closers))
    }

    /// A term with each name an earlier `define` introduced replaced by what
    /// it names (`named_body`), and nothing else changed.
    pub fn written_out(&self, term: &Term) -> Term {
        if let Some(body) = self.named_body(term, &Vars::new()) {
            return self.written_out(&body);
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        Term::apply(
            term.label().unwrap_or(""),
            term.children()
                .iter()
                .map(|c| self.written_out(c))
                .collect(),
        )
    }

    /// Whether two statements differ only in the letters they bind: a set
    /// variable is bound where it stands directly under a constructor other
    /// than `cv`, and every other letter must be the same on both sides. A
    /// class variable stands directly under a constructor as an operand, as
    /// P does in P − Q, and is bound by nothing: read as bound, it would make
    /// |PQ| and |RS| one term renamed (`letters_bound` draws the same line).
    pub fn rebound(&self, stated: &str, claimed: &str) -> bool {
        let mut pairs: IndexMap<String, String> = IndexMap::new();
        let mut binders: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        fn alike(
            one: &Term,
            two: &Term,
            pairs: &mut IndexMap<String, String>,
            binders: &mut std::collections::BTreeSet<String>,
        ) -> bool {
            if one.variable().is_some() || two.variable().is_some() {
                let (Some(a), Some(b)) = (one.variable(), two.variable()) else {
                    return false;
                };
                return pairs.entry(a.to_string()).or_insert_with(|| b.to_string())
                    == b;
            }
            if one.label() != two.label()
                || one.children().len() != two.children().len()
            {
                return false;
            }
            if one.label() != Some("cv") {
                binders.extend(
                    one.children()
                        .iter()
                        .filter_map(|c| c.variable().map(String::from)),
                );
            }
            one.children()
                .iter()
                .zip(two.children())
                .all(|(a, b)| alike(a, b, pairs, binders))
        }
        if !alike(
            &self.to_term(stated),
            &self.to_term(claimed),
            &mut pairs,
            &mut binders,
        ) {
            return false;
        }
        let values: std::collections::BTreeSet<&String> = pairs.values().collect();
        values.len() == pairs.len()
            && pairs.iter().all(|(mine, theirs)| {
                mine == theirs
                    || (binders.contains(mine) && self.is_setvar(&self.float_of(mine)))
            })
    }

    /// The "there is" an obtain's claim states: the claim states each name's
    /// membership as a sentence of its own, which is where the name runs;
    /// the other sentences are what is said of it, in the order written.
    fn existence_claimed(&mut self, step: &Step, got: &[String]) -> Checked<String> {
        let mut domains: IndexMap<String, String> = IndexMap::new();
        let mut rest = Vec::new();
        for said in self.sentences(&step.claim_text()) {
            match MEMBER_OF.captures(&said) {
                Some(m)
                    if got.contains(&m[1].to_string())
                        && !domains.contains_key(&m[1]) =>
                {
                    domains.insert(m[1].to_string(), m[2].to_string());
                }
                _ => rest.push(said),
            }
        }
        let missing: Vec<&str> = got
            .iter()
            .filter(|n| !domains.contains_key(*n))
            .map(String::as_str)
            .collect();
        if !missing.is_empty() {
            return Err(self.defect(
                step.line,
                format!(
                    "step {} states no membership of {}",
                    fmt(&step.number),
                    missing.join(", ")
                ),
            ));
        }
        if rest.is_empty() {
            return Err(self.defect(
                step.line,
                format!(
                    "step {} states nothing of what it obtains",
                    fmt(&step.number)
                ),
            ));
        }
        self.names_kept(|me| -> Checked<String> {
            for name in got {
                let var = me.binder_var(name)?;
                me.names.insert(name.clone(), format!("{var} cv"));
            }
            let mut body = me.claim_of(&rest.join(". "))?;
            for name in got.iter().rev() {
                let var = me.binder_var(name)?;
                let node = me.read(&domains[name])?;
                let over = me.term(&node)?;
                body = t!(body, var, over, "wrex");
            }
            Ok(body)
        })
    }

    /// An existential rewritten to bind variables nothing else holds.
    pub fn renamed(&mut self, ex: &str, depth: usize) -> Checked<String> {
        let whole = self.to_term(ex);
        let mut term = whole.clone();
        let mut binding = Binding::new();
        for _ in 0..depth {
            if term.label() != Some("wrex") {
                break;
            }
            let fresh = self.spare_var()?;
            let var = term.children()[1].variable().unwrap_or("").to_string();
            binding.insert(var, self.var_of(&fresh));
            term = term.children()[0].clone();
        }
        Ok(self.rpn(&whole.substitute(&binding)))
    }

    /// A cited line's proof, said where the citing step sits: a line proved
    /// before a block opened holds inside it too, and the scope carries a
    /// copy that says so.
    pub fn carried(&self, cite: &str, facts: &Facts, lines: &Lines) -> Proof {
        let held = lines
            .get(cite)
            .unwrap_or_else(|| panic!("no line {cite} to carry"));
        facts.get(&held.term).unwrap_or(held.proof)
    }

    /// The variables an existential's own binders introduce, outermost first.
    pub fn bound_in(&self, term: &Term) -> Vec<String> {
        let mut out = Vec::new();
        let mut rest = term.clone();
        while matches!(rest.label(), Some("wrex") | Some("wreu")) {
            out.push(rest.children()[1].variable().unwrap_or("").to_string());
            rest = rest.children()[0].clone();
        }
        out
    }

    /// The innermost scope a lemma's disjointness conditions permit.
    ///
    /// `fsump1` forbids its summation variable in the antecedent, and the
    /// induction hypothesis is an equation between sums, so it holds that
    /// variable. The step is proved one frame out and carried back in.
    pub fn allowed(
        &self,
        sig: &Signature,
        binding: &Binding,
    ) -> (Route<String>, Option<usize>) {
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        let mut forbidden: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for (a, b) in &sig.disjoint {
            for (one, other) in [(a, b), (b, a)] {
                if kinds.get(other.as_str()) == Some(&"setvar") {
                    continue;
                }
                if let (Some(held), false) =
                    (binding.get(one), binding.contains_key(other))
                {
                    for n in held.names().iter() {
                        forbidden.insert(self.float_of(n));
                    }
                }
            }
        }
        for index in (0..self.frames.len()).rev() {
            let term = &self.frames[index].scope;
            if !term.split_whitespace().any(|t| forbidden.contains(t)) {
                return (Built(term.clone()), Some(index));
            }
        }
        (Route::no("no scope satisfies the lemma"), None)
    }

    /// What is known at one frame, which is what was known when it opened.
    pub fn frames_facts(&self, frame: usize, facts: &Facts) -> Facts {
        if frame == self.frames.len() - 1 {
            facts.clone()
        } else {
            self.frames[frame].facts.clone()
        }
    }

    /// Bring a proof from an outer frame back to the innermost one.
    pub fn carry(&self, proof: Proof, claim: &str, frame: usize) -> Proof {
        let mut proof = proof;
        for index in frame..self.frames.len().saturating_sub(1) {
            let outer = &self.frames[index].scope;
            let added = self.frames[index + 1].added.clone().unwrap_or_default();
            proof = pf!(self.b; outer, claim, added, proof, "adantr");
        }
        proof
    }

    /// The facts a lemma is answered from, what the step cites first: its
    /// justification's lines, or `refs` where a `requires` line names its
    /// own. Each line the step cites is taken apart on its own and laid over
    /// the scope's copies of the same claims, and first in order as well,
    /// because a lemma's open antecedent takes the first fact that fits.
    ///
    /// A lemma proved in an outer scope (`allowed`) is offered only what that
    /// scope holds.
    pub fn with_cited(
        &self,
        step: Option<&Step>,
        scope: &str,
        known: &Facts,
        refs: Option<&[String]>,
    ) -> Facts {
        let outer = !self.frames.is_empty()
            && scope != self.frames[self.frames.len() - 1].scope;
        let cited = Facts::new();
        let refs: Vec<String> = match refs {
            Some(r) => r.to_vec(),
            None => step.map(|s| s.just.refs.clone()).unwrap_or_default(),
        };
        for r in &refs {
            let Some(line) = self.lines.get(r) else {
                continue;
            };
            if outer && !known.has(&line.term) {
                continue;
            }
            let parts = Facts::new();
            parts.set(line.term.clone(), self.carried(r, known, &self.lines));
            let held = parts.get(&line.term).unwrap();
            self.unpack(&line.term, &held, scope, &parts, 4);
            for (k, v) in parts.entries() {
                cited.set(k, v);
            }
        }
        let out = cited.copy();
        for (k, v) in known.entries() {
            if !cited.has(&k) {
                out.set(k, v);
            }
        }
        out
    }

    /// Two lines paired, `jca`, the lines paired by what they claim.
    pub fn join(
        &mut self,
        step: &Step,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let lines = self.lines.clone();
        let wanted = self.claim_of(&step.claim_text())?;
        let held = Facts::new();
        for r in &step.just.refs {
            let line = lines.get(r).expect("a line joined");
            held.set(line.term.clone(), self.carried(r, facts, &lines));
        }
        // One line joined is that line restated.
        if step.just.refs.len() == 1 {
            return match held.get(&wanted) {
                Some(p) => Ok(Some(p)),
                None => Err(self
                    .defect(step.line, "the joined line is not what the step claims")),
            };
        }
        // Several lines joined are one conjunction, nested as the claim nests
        // it: each side is a line joined, or itself lines joined.
        fn joined(
            me: &Elaborator,
            held: &Facts,
            term: &str,
            scope: &str,
        ) -> Option<Proof> {
            if let Some(p) = held.get(term) {
                return Some(p);
            }
            let node = me.to_term(term);
            if node.label() != Some("wa") {
                return None;
            }
            let pair: Vec<String> = node.children().iter().map(|c| me.rpn(c)).collect();
            let first = joined(me, held, &pair[0], scope);
            let second = joined(me, held, &pair[1], scope);
            let (first, second) = (first?, second?);
            Some(pf!(me.b; scope, pair[0], pair[1], first, second, "jca"))
        }
        match joined(self, &held, &wanted, scope) {
            Some(p) => Ok(Some(p)),
            None => {
                Err(self
                    .defect(step.line, "the joined lines are not what the step claims"))
            }
        }
    }
}

/// What on the page a block's assumption is: its label where the text gives
/// one, and where it does not, the block's own step, since that is where a
/// reader finds it.
pub fn assumption(block: &Block, label: &str) -> String {
    if !label.is_empty() {
        return label.to_string();
    }
    format!("{} assumes", number_of(&block.owner))
}

/// The variables a binding's terms mention, for `fit`.
pub fn vars_of(terms: &[&Term]) -> Vars {
    let mut out = Vars::new();
    for t in terms {
        out.extend(t.names().iter().cloned());
    }
    out
}

/// Whether a fact fits a pattern under a binding.
pub fn fits(
    pattern: &Term,
    fact: &Term,
    binding: &Binding,
    variables: &Vars,
) -> Option<Binding> {
    fit(pattern, fact, binding, variables)
}
