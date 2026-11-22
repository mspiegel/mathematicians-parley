//! Running a theorem's steps.

use std::{mem, slice};

use super::*;
use crate::corpus::skeleton;

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
        left: &Rpn,
        ex: Option<&Rpn>,
        var: Option<&str>,
        over: Option<&Rpn>,
        scope: &Rpn,
        facts: &Facts,
        hint: Option<&Rpn>,
    ) -> Checked<Route<(Proof, Rpn)>> {
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
        let deduced = asks.first().and_then(Term::variable_symbol);
        if let Some(v) = &deduced {
            binding.insert(*v, self.to_term(scope));
            asks.remove(0);
        }
        // A lemma's left side need not fix everything it mentions, so what
        // the caller can say of the right side fixes the rest.
        // The fit is made as written, then as the standard form reads the
        // two, as `apply_lemma` fits an antecedent: the page's x ≠ c is
        // "not (x = c)" where a lemma writes `=/=`; and then with identity
        // elements dropped, as the checker reads a cited line
        // (`identities_dropped`), as written and in the standard form.
        // What is offered may be the facts a step names joined, a define's
        // equation among them, and then the right side is one of them.
        if let Some(offered) = hint.or(ex) {
            let offered = self.to_term(offered);
            let mut pieces = vec![offered.clone()];
            pieces.extend(super::super::matcher::conjuncts_of(&offered));
            let filled = pieces.iter().find_map(|piece| {
                fit(&reads.children()[1], piece, &binding, &variables)
                    .or_else(|| {
                        self.fits_as(
                            &reads.children()[1],
                            piece,
                            &variables,
                            Some(&binding),
                        )
                    })
                    .or_else(|| {
                        let bare =
                            self.identities_dropped(&reads.children()[1], &binding);
                        let held = self.without_identities(piece);
                        fit(&bare, &held, &binding, &variables).or_else(|| {
                            self.fits_as(&bare, &held, &variables, Some(&binding))
                        })
                    })
            });
            if let Some(filled) = filled {
                binding = filled;
            }
        }
        // A letter the lemma binds, which neither side fixed and which it
        // keeps apart from its context, takes a letter nothing holds: left
        // as the lemma's own, it may be the scope's, as a hypothesis saying
        // "for all x" makes it.
        if let Some(v) = &deduced {
            let setvars: BTreeSet<&str> = sig
                .floats
                .iter()
                .filter(|(kind, _)| kind == "setvar")
                .map(|(_, name)| name.as_str())
                .collect();
            let open: Vec<Symbol> = sig
                .disjoint
                .iter()
                .flat_map(|(a, b)| [(a, b), (b, a)])
                .filter(|(one, other)| {
                    *other == v
                        && setvars.contains(one.as_str())
                        && !binding.contains_key(one.as_str())
                })
                .map(|(one, _)| *one)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            if !open.is_empty() {
                let avoid: Vec<Term> = [self.to_term(scope), whole.clone()]
                    .into_iter()
                    .chain(binding.values().cloned())
                    .collect();
                if let Some(fresh) =
                    self.unheld_for(open, &avoid.iter().collect::<Vec<_>>())
                {
                    binding.extend(fresh);
                }
            }
        }
        // A slot neither side fixes is set.mm asking where to look for the
        // thing, and _V holds everything that is a set; a fixed function's
        // type is read off the line saying it.
        let keys = facts.keys();
        for slot in &asks {
            for piece in super::super::matcher::conjuncts_of(slot) {
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
                if !binding.contains_key(open) {
                    binding.insert(*open, Term::apply("cvv", Vec::new()));
                }
            }
        }
        let mut binding = self.instanced(&sig, binding);
        // The scope is the step's own, where what its requires lines say is
        // held. Where the lemma's disjointness conditions keep a letter
        // apart from it that the scope spells, a "for all t" a line in scope
        // says binding the t the step's claim binds too, that letter is moved
        // to one nothing holds, as a claim's are (`over_other_letters`), and
        // the side the step holds is renamed to it below. Only where no
        // letter can be moved so is the lemma applied at an outer scope, the
        // innermost its conditions allow (`allowed`), and what it gives
        // carried in to the step's.
        let (mut at, mut frame) = (scope.clone(), None);
        let mut moved = Binding::new();
        if let Some(v) = &deduced {
            let mut open = binding.clone();
            open.shift_remove(v);
            let (mut where_, mut index) = self.allowed(&sig, &open);
            let innermost = self.frames.len().checked_sub(1);
            if where_.is_declined() || index != innermost {
                let spelt: BTreeSet<&str> =
                    scope.tokens().iter().map(|t| t.as_str()).collect();
                let letters: Vec<Symbol> = sig
                    .disjoint
                    .iter()
                    .flat_map(|(a, b)| [(a, b), (b, a)])
                    .filter(|(_, other)| *other == v)
                    .filter_map(|(one, _)| open.get(one.as_str()))
                    .filter_map(Term::variable_symbol)
                    .filter(|l| spelt.contains(self.float_of(l).as_str()))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                let avoid: Vec<Term> = [self.to_term(scope), whole.clone()]
                    .into_iter()
                    .chain(open.values().cloned())
                    .collect();
                if let Some(m) = self
                    .unheld_for(letters, &avoid.iter().collect::<Vec<_>>())
                    .filter(|m| !m.is_empty())
                {
                    let apart: Binding =
                        open.iter().map(|(k, t)| (*k, t.substitute(&m))).collect();
                    let (there, at_index) = self.allowed(&sig, &apart);
                    if where_.is_declined() || at_index == innermost {
                        (moved, open, where_, index) = (m, apart, there, at_index);
                    }
                }
            }
            at = take!(where_);
            frame = index;
            binding = open;
            binding.insert(*v, self.to_term(&at));
        }
        let at_facts = match frame {
            Some(f) => self.frames_facts(f, facts),
            None => facts.clone(),
        };
        // A definition that introduces a name says which variable it takes:
        // the one its right side binds at its head, as the step's "there is"
        // does. One that does not leaves the lemma's own, which the match
        // fixed.
        let mut binds = self.spelt(&binding);
        let right = &reads.children()[1];
        let mut held = right
            .label()
            .filter(|l| lookup(rules::BOUND, l).is_some())
            .and_then(|_| right.children().get(1))
            .and_then(|v| v.variable().map(String::from));
        if let Some(h) = &held {
            if reads.children()[0].names().iter().any(|n| **n == **h) {
                held = None;
            }
        }
        if let (Some(v), Some(h)) = (var, &held) {
            binds.insert(h.clone(), t!(v));
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
            binding.insert(Symbol::of(h), var_term);
        }
        if let (Some(_), Some(f)) = (&deduced, frame) {
            let gives = self.rpn(&whole.children()[1].substitute(&binding));
            applied = self.carry(applied, &gives, f);
        }
        let given = self.rpn(&reads.children()[1].substitute(&binding));
        let near = if moved.is_empty() {
            left.clone()
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
        let proof = if near == *left {
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
            ex.clone(),
        )))
    }

    // --- the proof ------------------------------------------------------

    /// The theorem elaborated: its conclusion, its hypotheses, and the proof
    /// of the one from the other.
    pub fn run(&mut self) -> Checked<(Rpn, Vec<Rpn>, Proof)> {
        self.phrase_targets()?;
        // The statement is read with the definitions the theorem sees from
        // outside it, and those of its header, written out, which is what
        // set.mm states.
        self.from_outside = self.checked.statement_definitions.clone();
        let nodes = self.hypotheses()?;
        self.read_sorts();
        // A define by recursion in the statement is stated written out, as a
        // definition from outside is, in the hypotheses below it as in the
        // conclusion. Its rules may name a letter a `let` gives, which
        // `hypotheses` has named.
        let first = self.thm.steps.first().map(|s| s.line);
        for d in self.thm.defines.clone() {
            let Built(DefineParts::Recursion(given)) = define_parts(&d.text) else {
                continue;
            };
            if first.is_some_and(|f| d.line >= f) {
                continue;
            }
            for (name, made) in self.recursion_terms(&d.label, d.line, &given)? {
                self.from_outside
                    .insert(name, Defined::Term(Node::literal(&made)));
            }
        }
        let mut terms = Vec::new();
        for n in &nodes {
            terms.push(self.term(n)?);
        }
        // A theorem may assume nothing, and every step here is still an
        // implication out of the scope it sits in: the scope is truth,
        // discharged once at the end.
        let mut scope = terms.first().cloned().unwrap_or_else(|| t!("wtru"));
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
                self.unpack_all(extra, &held, &scope, &facts);
            }
        }
        for (node, term) in nodes.iter().zip(&terms) {
            if let Some(held) = self.held(&facts, term, &scope)? {
                self.know_chains(slice::from_ref(node), term, &held, &scope, &facts);
            }
        }
        let more = self.sethoods(&nodes, &terms, &scope, &facts)?;
        self.sorts.extend(more);
        self.introduced = IndexMap::new();
        self.note_introduced(&scope, &facts)?;

        // Each keeps the sentence it was read from, as a block's opening
        // line does, so a step may substitute into it.
        let lines = Lines::new();
        for ((h, t), node) in hypotheses.iter().zip(&terms).zip(&nodes) {
            let proof = self.held(&facts, t, &scope)?.expect("a hypothesis's fact");
            lines.set(
                h.label.clone().unwrap_or_default(),
                Line::new(t.clone(), proof, vec![node.clone()]),
            );
        }
        let goal = self.claim_of(&self.thm.stated())?;
        self.from_outside = IndexMap::new();
        // What the conclusion quantifies over is spoken for before anything
        // else takes a variable.
        self.reserved = goal
            .tokens()
            .iter()
            .filter(|t| {
                self.b
                    .sigs
                    .get(t.as_str())
                    .is_some_and(|s| s.statement[0] == "setvar")
            })
            .map(|t| String::from(*t))
            .collect();
        self.rules_read = IndexMap::new();
        self.open_outermost(&scope, &facts);
        self.lines = lines;
        let mut closers: Vec<Closer> = Vec::new();
        let mut blocks: Vec<Block> = Vec::new();
        let mut named_hypotheses = false;
        for (at, step) in self.thm.steps.clone().into_iter().enumerate() {
            // A block closes at the first step the checker's record does not
            // stand inside it (`CheckedTheorem::around`).
            let around: Vec<ByPart> = self
                .checked
                .around(at)
                .iter()
                .map(|p| ByPart {
                    owner: self.checked.blocks[p.block].owner,
                    part: p.part,
                })
                .collect();
            while blocks
                .last()
                .is_some_and(|b| !stands_open(self.thm, b, &around))
            {
                let mut done = blocks.pop().unwrap();
                closers = self.settle_claimed(&mut done, closers, None)?;
                (scope, facts, closers) =
                    self.close_block(&mut done, &facts, closers, &scope)?;
                self.line_built_as_stated(done.owner.line)?;
                self.contradicted_at(&done.owner, &scope, &facts)?;
                Self::hand_up(&done, &mut blocks);
            }
            // A step in a case sits under the case's assumption, and one in
            // an induction's step part under what that part opens with, where
            // the part is new.
            let inducts = |b: &Block| b.owner.just.head.is(Method::Induction);
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
                let by = block.owner.opening(Some(part)).by.cloned();
                let owner = block.owner.clone();
                blocks.push(block);
                // The part's `by` line opens its block where the part opens.
                if let (Some(by), Some(owner_at)) =
                    (by, CheckedTheorem::index_of(self.thm, &owner))
                {
                    let mut inner =
                        self.open_by_part(&owner, owner_at, &by, &scope, &facts)?;
                    inner.opened_at = closers.len();
                    scope = inner.scope.clone();
                    facts = inner.facts.clone();
                    blocks.push(inner);
                }
            }
            // Any define standing above this step, now that the block and
            // the case it sits in are open and the names it leans on are in
            // hand: a define written inside a case is the case's.
            (scope, facts, closers) =
                self.define(step.line, &scope, &facts, closers)?;
            if !named_hypotheses {
                named_hypotheses = true;
                self.hypotheses_named(&hypotheses, &nodes, &scope, &facts)?;
            }
            if !step.openers.is_empty() || !step.parts.is_empty() {
                let mut block = self.open_block(&step, &scope, &facts)?;
                block.opened_at = closers.len();
                scope = block.scope.clone();
                facts = block.facts.clone();
                blocks.push(block);
                // A block with no parts opens the block its `by` line names
                // under its own openers.
                if let Some(by) =
                    step.opening(None).by.filter(|_| step.parts.is_empty())
                {
                    let mut inner = self.open_by_part(&step, at, by, &scope, &facts)?;
                    inner.opened_at = closers.len();
                    scope = inner.scope.clone();
                    facts = inner.facts.clone();
                    blocks.push(inner);
                }
                continue;
            }
            self.in_contradiction = blocks
                .last()
                .is_some_and(|b| b.owner.just.head.is(Method::Contradiction));
            (scope, facts, closers) = self.take_step(&step, &scope, &facts, closers)?;
            self.line_built_as_stated(step.line)?;
            // A step contradicting a line closes a contradiction block on the
            // two of them, as its last pair.
            self.contradicted_at(&step, &scope, &facts)?;
            let denied = match step.impossible {
                true => Some(self.denial_of(&step, &scope, &facts)?),
                false => None,
            };
            // A part a `by` line opened a block in ends where that block
            // closes (`Elaborator::hand_up`).
            let in_part = blocks.last_mut().filter(|b| b.by_part.is_none());
            if let (Some(part), Some(block)) = (step.part, in_part) {
                self.end_part(block, part, &step, denied.clone(), &scope, &facts)?;
            }
            // A `proof` block whose assumption cannot hold ends on the step that
            // reaches the opposite of an earlier line, or on a closed claim
            // said to be impossible, as a case that cannot occur does: what
            // the block claims of the name it fixes is reached from the two,
            // and stands as the block's last line.
            // A part's `by proof` block holds steps of the part, which the
            // block closes as one with no parts.
            let fixing = blocks
                .last()
                .filter(|b| b.owner.just.head.is(Method::Proof))
                .filter(|b| step.part.is_none() || b.by_part.is_some())
                .map(|b| b.owner.clone());
            let closes_fixing = step.just.contradicting.is_some() || denied.is_some();
            if let (true, Some(owner)) = (closes_fixing, fixing) {
                let last = self.last.clone().expect("a step's number");
                let line = self.lines.get(&last).expect("the step's line");
                let held = self
                    .line_written(&last, &self.lines)
                    .expect("the step's line");
                let body = self.owed_goal(&owner)?;
                let made = match (&step.just.contradicting, denied) {
                    (Some(other), _) => {
                        self.by_opposites(&step, &held, other, &body, &scope, &facts)?
                    }
                    // The step's line and its denial, worked out above.
                    (None, Some(not)) => {
                        pf!(self.b; scope, held.claim, body, held.proof, not, "pm2.21dd")
                    }
                    (None, None) => continue,
                };
                self.lines.set(&last, line.restated(body, made));
            }
        }
        self.finish_proof(Finishing {
            blocks,
            closers,
            scope,
            facts,
            goal,
            terms,
        })
    }

    /// The theorem's proof once its last step is taken: the blocks still
    /// open closed, the last line carried to the statement, and each closer
    /// applied from the inside out.
    pub(super) fn finish_proof(
        &mut self,
        finishing: Finishing,
    ) -> Checked<(Rpn, Vec<Rpn>, Proof)> {
        let Finishing {
            mut blocks,
            mut closers,
            mut scope,
            mut facts,
            goal,
            terms,
        } = finishing;
        while let Some(mut done) = blocks.pop() {
            closers = self.settle_claimed(&mut done, closers, None)?;
            (scope, facts, closers) =
                self.close_block(&mut done, &facts, closers, &scope)?;
            self.line_built_as_stated(done.owner.line)?;
            self.contradicted_at(&done.owner, &scope, &facts)?;
            Self::hand_up(&done, &mut blocks);
        }

        let last = self.last.clone().expect("a proof of one step at least");
        let held = self
            .line_written(&last, &self.lines)
            .expect("the last line");
        let mut proof = held.proof;
        // The last line says it with the names, the statement with what they
        // name; the standard form reads the two as one.
        let said = held.claim;
        // Three points in no order, named in another order than the
        // statement's, are carried to its order as a cited line is.
        if said != goal && self.reorders(&said, &goal) {
            proof = match self.reached(&proof, &said, &goal, &scope, &facts)? {
                Some(p) => p,
                None => {
                    return Err(self.defect(
                        self.thm.line,
                        "the last step names the statement's points in an order \
                         the build cannot reach"
                            .to_string(),
                    ));
                }
            };
        } else if said != goal {
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
        self.built_as_stated(self.thm.line, &proof)?;
        Ok((goal, terms, proof))
    }

    /// The letters the theorem introduces that are sorts, and its `let`
    /// lines. A sort is stated once, like a declared type, and a step may
    /// rest on it without naming it. A define is not one: a step that uses
    /// what it says cites it, as it cites any line it uses.
    pub(super) fn read_sorts(&mut self) {
        let mut sorts: BTreeSet<String> = BTreeSet::new();
        let path = &self.thm.path;
        let mut lets: Vec<(Intro, Written, String)> = self
            .thm
            .hypotheses
            .iter()
            .map(|h| (h.kind, h.body(path), h.label.clone().unwrap_or_default()))
            .collect();
        for s in &self.thm.steps {
            // An induction hypothesis assumes its claim's statement, and is
            // no sort.
            for o in s.openers.iter().filter(|o| !o.is_hypothesis) {
                lets.push((o.kind, o.body(path), o.label.clone()));
            }
        }
        // A sort is what a set, a point, a polynomial, a function, a group or
        // a graph is introduced as; and a subgroup an `assume` says there is.
        for (kind, body, label) in &lets {
            if label.is_empty() {
                continue;
            }
            let sort = match kind {
                Intro::Let => matches!(
                    Introduction::read(body.clone()).form,
                    Form::Set(_)
                        | Form::Point(_)
                        | Form::Polynomial(_)
                        | Form::Function
                        | Form::FunctionBeing { .. }
                        | Form::Group { .. }
                        | Form::Graph(_)
                        | Form::GraphListed(_)
                ),
                // A line that does not read is reported where it is opened.
                _ => self.read_one(body).is_ok_and(|n| is_subgroup(&n)),
            };
            if sort {
                sorts.insert(label.clone());
            }
        }
        self.sorts = sorts;
        self.let_lines = lets
            .iter()
            .filter(|(kind, _, label)| *kind == Intro::Let && !label.is_empty())
            .map(|(_, _, label)| label.clone())
            .collect();
    }

    /// A block's part `part` ended by `step`, its last: the claim and proof
    /// the part ends on. A case that cannot occur gives the block's claim
    /// from its line and the line it contradicts, or from its line and that
    /// line shown false (`denied`).
    pub(super) fn end_part(
        &mut self,
        block: &mut Block,
        part: usize,
        step: &Step,
        denied: Option<Proof>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        let last = self.last.clone().expect("a step's number");
        let held = self
            .line_written(&last, &self.lines)
            .expect("the step's line");
        let (term, proof) = match (&step.just.contradicting, denied) {
            (Some(other), _) => {
                let claim = self.claim_of(&block.owner.claim)?;
                let made =
                    self.by_opposites(step, &held, other, &claim, scope, facts)?;
                (claim, made)
            }
            (None, Some(not)) => {
                let claim = self.claim_of(&block.owner.claim)?;
                let made =
                    pf!(self.b; scope, held.claim, claim, held.proof, not, "pm2.21dd");
                (claim, made)
            }
            (None, None) => (held.claim, held.proof),
        };
        // What the part's end asks that its last step's requires
        // lines say is in hand where the block closes on it.
        let ended = if step.requires.is_empty() {
            facts.clone()
        } else {
            self.supplied(Some(step), scope, facts)?
        };
        let mut end = PartEnd {
            claim: term,
            proof,
            scope: scope.clone(),
            facts: ended,
        };
        // A case ending on the claim written another way, |OP|² for
        // |PO|², is carried to the claim here, while the case's
        // letters and facts are in hand: at the block's close only
        // the block's are, and what a carrying lemma asks of its terms
        // would be proved there, under the narrower scope.
        if block.owner.just.head.is(Method::Cases) {
            let claim = self.claim_of(&block.owner.claim)?;
            if end.claim != claim {
                if let Some(carried) = self.direction_reached(&end, &claim)? {
                    end.claim = claim;
                    end.proof = carried;
                }
            }
        }
        block.parts.insert(part, end);
        Ok(())
    }

    /// The denial a step that says its claim is impossible proves: it is its
    /// own opposite. The claim is worked out, by `real arithmetic` where it
    /// holds a square root, π, e, a logarithm or an exponential and by
    /// `arithmetic` otherwise; one not found false is refused, and the denial
    /// is proved, which stands as the line it contradicts.
    pub(super) fn denial_of(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let last = self.last.clone().expect("a step's number");
        let held = self
            .line_written(&last, &self.lines)
            .expect("the step's line");
        let negated = t!(held.claim, "wn");
        let what = format!(
            "step {} says {} is impossible",
            step.number,
            step.claim_text()
        );
        let goal = self.to_term(&negated);
        let real = reals::beyond_arithmetic(&goal);
        let why = if real {
            match reals::decide_closed(&goal) {
                Built(surds::Verdict::Holds(true)) => None,
                Built(surds::Verdict::Holds(false)) => {
                    Some("which is true".to_string())
                }
                Built(surds::Verdict::Unworked(why)) => Some(format!("which {why}")),
                Built(surds::Verdict::Undecided(why)) => {
                    Some(format!("which {why}{}", reals::NOT_DECIDED_HERE))
                }
                Declined(_) => Some(format!("which {}", reals::UNREAD)),
            }
        } else {
            match field::decide_closed(&goal) {
                Built(Verdict::Holds(true)) => None,
                Built(Verdict::Holds(false)) => Some("which is true".to_string()),
                Built(Verdict::Unworked(why)) => Some(format!("which {why}")),
                Declined(_) => Some(
                    "which is not a fact about numerals alone that arithmetic decides"
                        .into(),
                ),
            }
        };
        if let Some(why) = why {
            return Err(self.defect(step.line, format!("{what}, {why}")));
        }
        let proof = if real {
            self.real_fact(&negated, scope, facts, &what)?
        } else {
            self.closed_fact(&negated, scope, facts, &what, None)?
        };
        self.know(facts, negated.clone(), proof.clone());
        if self.in_contradiction {
            self.contradicted = Some(Contradicted {
                claim: negated.clone(),
                proof: proof.clone(),
                reordered: None,
                says: Vec::new(),
            });
        }
        Ok(proof)
    }

    /// Every label in the proof of the line last kept is applied as its
    /// statement says (`Builder::fault`); a defect at `line` where one is
    /// not. It is the elaborator's own fault, not the page's, and is
    /// reported where it was built, which the verifier cannot say.
    pub(super) fn line_built_as_stated(&self, line: usize) -> Checked<()> {
        let Some(held) = self
            .last
            .as_ref()
            .and_then(|l| self.line_written(l, &self.lines))
        else {
            return Ok(());
        };
        self.built_as_stated(line, &held.proof)
    }

    /// `line_built_as_stated` of a proof in hand.
    pub(super) fn built_as_stated(&self, line: usize, proof: &Proof) -> Checked<()> {
        match self.b.fault(proof) {
            Some(fault) => Err(self.defect(
                line,
                format!("the elaborator built a step the kernel would refuse: {fault}"),
            )),
            None => Ok(()),
        }
    }

    /// ( scope -> claim ) from a step's line and the line it contradicts, the
    /// one a formula and the other, or a sentence of it, that formula negated
    /// (`pm2.21dd`), found as a contradiction block finds its pair.
    pub(super) fn by_opposites(
        &mut self,
        step: &Step,
        held: &ProvedClaim,
        other: &str,
        claim: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let lines = self.lines.clone();
        let Some(there) = self.line_written(other, &lines) else {
            return Err(
                self.unreached(step.line, format!("{other} is no line in scope"))
            );
        };
        let pair = Facts::new();
        self.know(&pair, held.claim.clone(), held.proof.clone());
        let carried = self.carried(other, facts, &lines);
        self.know(&pair, there.claim.clone(), carried);
        let offered = [held.claim.clone(), there.claim.clone()];
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
    pub(super) fn take_step(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        let number = number_of(step);
        let named = self.named(step, &number, false);
        self.resting_on(Some(named), |me| {
            me.one_step(step, &number, scope, facts, closers)
        })
    }

    pub(super) fn one_step(
        &mut self,
        step: &Step,
        number: &str,
        scope: &Rpn,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        let head = step.just.head.to_string();
        self.last = Some(number.to_string());
        self.at = step.line;
        self.step_now = CheckedTheorem::index_of(self.thm, step);
        self.note_said_sums()?;
        let resting = self.named(step, number, false);
        self.named_first(&step.just.refs, &resting, facts);
        if step.just.head.is(Method::Obtain) {
            return self.obtain(step, number, scope, facts, closers);
        }
        let sentences = step.claim.sentences();
        let Some(last) = sentences.last() else {
            return Err(
                self.unreached(step.line, format!("step {number} claims nothing"))
            );
        };
        let node = self.read(last)?;
        let term = self.claim_of(&step.claim)?;
        if self.said_back.is_some() {
            self.say_back(&sentences, step.line)?;
        }
        let Some(how) = self.method_for(step)? else {
            return Err(
                self.unreached(step.line, format!("no expansion for {}", repr(&head)))
            );
        };
        let lines = self.lines.clone();
        // The method is handed what the step may rest on, and nothing else.
        let named = self.in_hand(facts);
        let made =
            self.by_method_written(&how, step, &node, &term, scope, &named, &lines)?;
        // Every route the method had declined, so nothing here owns the
        // step: this elaborator's limit rather than a defect in the text.
        let proof = match made {
            Declined(d) => {
                return Err(self.defect(
                    step.line,
                    format!("no method owns this step: {}", self.say(&d)),
                ));
            }
            Built(None) => return Ok((scope.clone(), facts.clone(), closers)), // a join, which emits nothing
            Built(Some(p)) => p,
        };
        let said = self.said(step)?;
        let proof = self.check_step(proof, step, number, false)?;
        self.lines
            .set(number, Line::new(term.clone(), proof.clone(), said.clone()));
        self.know(facts, term.clone(), proof.clone());
        self.know_turned(facts, &term, &proof, scope);
        // A line saying several things says each of them, only as deep as
        // the sentences the text wrote, a chain of equations being the
        // equations between its neighbouring terms; and a chain says the
        // equation between any two of its terms.
        let parts = written_parts(&said);
        if parts > 1 {
            self.unpack(&term, &proof, scope, facts, parts - 1);
        }
        self.know_chains(&said, &term, &proof, scope, facts);
        Ok((scope.clone(), facts.clone(), closers))
    }

    /// A requires line whose reason is a method or an item, proved as the
    /// step it would be (`requires_as_step`): the same method, chosen the
    /// same way, by the same route a numbered step takes. The step's
    /// requires lines above it, which `supplied` has proved and put in hand,
    /// are lines it cites (R2), with what each says: `m·n ≥ 0: inequalities`
    /// reads it off `m·n ∈ ℕ` above as off a cited line saying so. Two terms
    /// differing is taken only from a line the requires line cites
    /// (`METHODS.md`), so a disequality above is not among them. `what`
    /// names the line in a message: a requires line of its step, or the
    /// reason under a let.
    pub fn as_a_step(
        &mut self,
        step: &Step,
        req: &Requires,
        what: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut at = requires_as_step(step, req)?;
        let lines = self.lines.copy();
        let labels = self.b.flabel.clone();
        for o in step.requires_above(req.line) {
            let node = self.read_one(&o.fact)?;
            let above = self.term(&node)?;
            let key = requirement(o.line);
            let sealed = self
                .held(facts, &above, scope)?
                .filter(|p| p.origin.contains(&key));
            let differing = linear::fact(&self.to_term(&above), &labels)
                .is_some_and(|f| f.how == linear::How::Ne);
            if let Some(proof) = sealed.filter(|_| !differing) {
                lines.set(key.clone(), Line::new(above, proof, vec![node]));
                at.just.refs.push(key);
            }
        }
        let node = self.read_one(&req.fact)?;
        let term = self.term(&node)?;
        let Some(how) = self.method_for(&at)? else {
            return Ok(Route::no(format!("no expansion for {}", repr(&req.how))));
        };
        let kept = mem::replace(&mut self.lines, lines.clone());
        // The line rests on what it names and nothing else the step names
        // (R2), as a requires line does.
        let allowed = self.reason_allows(step, req);
        let made = self.resting_on(Some(allowed), |me| {
            let named = me.in_hand(facts);
            me.by_method_written(&how, &at, &node, &term, scope, &named, &lines)
        });
        self.lines = kept;
        // What the step route says of the line it was given is said of the
        // requires line, whose step it is not.
        let made = made.map_err(|mut p| {
            if p.line.line == req.line {
                p.message = format!(
                    "{what}, read as a step citing what it cites: {}",
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
    pub(super) fn method_for(&mut self, step: &Step) -> Checked<Option<How>> {
        let head = step.just.head.to_string();
        let mut how: Option<How> = match &step.just.head {
            Head::Method(m) if EXPANDED.contains(m) => Some(How::Named(*m)),
            Head::Define => Some(How::Define),
            // A requires line naming a manipulation of its one line is a
            // linear fact of that line, which the proof of an inequalities
            // step proves; the checker has held it to its manipulation.
            Head::Manipulation(_) => Some(How::Named(Method::Inequalities)),
            _ => None,
        };
        // Whether a step unfolds what it cites is read from the record.
        let cited = match skeleton::item_kind(&head) {
            Some(_) => Some(self.item_cited(&head)?),
            None => None,
        };
        if how.is_none() && cited.is_some_and(|item| item.unfolds()) {
            let Some(Item::Record(item)) = cited else {
                panic!("{head} is a definition of the database");
            };
            // A definition stated as a biconditional is used by unfolding
            // it; one stated as an equation is used by citing the lemma that
            // proves it. With no target it is read off the lines the step
            // cites, or is a defect (`take_definition`).
            how = Some(if item.metamath_target().is_none() {
                How::TakeDefinition
            } else if item.conclusions.iter().any(|(text, _)| text.contains('↔')) {
                How::Reading(self.reading(item, step)?)
            } else {
                How::UnfoldEquation
            });
        }
        if how.is_none() && cited.is_some() {
            how = Some(How::Cite);
        }
        Ok(how)
    }

    /// A step's proof by the method its justification names, with its
    /// requires lines, as it is written or at a member of what it says
    /// "for all" of.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn by_method_written(
        &mut self,
        how: &How,
        step: &Step,
        node: &Node,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        // Said of every member: a step the checker read at a member of its
        // claim's "for all" is proved there and the claim generalised
        // (`CheckedTheorem::at_member`; `SYNTAX.md`, a step said of every
        // member). The requires lines are then about that member, and are
        // proved where it is in scope.
        let at_a_member = self.checked.at_member.contains_key(&step.just.line);
        // The claim says "for all" on the page, and not in its kernel form
        // only: "1 is an upper bound of [0, 1]" is a "for all" in set.mm's
        // words and none in the page's, and is cited whole.
        let whole = self.to_term(term);
        let universals = &self.item_library().ctx.universals;
        let says_for_all = universals.contains(&node.notation());
        if at_a_member
            && says_for_all
            && whole.variable().is_none()
            && whole.label() == Some("wral")
        {
            let letter = self.member_letter(step)?;
            let kids = whole.children();
            let (body, variable, over) =
                (kids[0].clone(), kids[1].clone(), kids[2].clone());
            // The member is fixed as the claim's own letter where neither the
            // scope nor a name holds it, and a spare otherwise, the claim then
            // proved over the spare and renamed back. Either is reserved, so
            // that no later step is handed it as a letter nothing holds; the
            // page's letter is bound to it only while the step is proved.
            let name = self.rpn(&variable).to_string();
            let scope_term = self.to_term(scope);
            let var = if scope.has(&name) || self.names_held().contains(&name) {
                match self.unheld(&[&scope_term, &body, &over]) {
                    Some(spare) => self.rpn(&spare).to_string(),
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
                let again = self.restated(&body, &t!(name, "cv"), &t!(var, "cv"));
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
                    let within = me.rpn(&me.to_term(&member).children()[1]);
                    let kept = me.member.replace(member);
                    // The member is introduced in its set as its block's let
                    // would introduce it (`introduced_in`).
                    let made = me.names_and_sets_kept(|me| {
                        if let Some((page, _)) = &letter {
                            me.names.insert(page.clone(), fixed.clone());
                            me.sets.insert(page.clone(), within.clone());
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
    pub(super) fn with_requires(
        &mut self,
        how: &How,
        step: &Step,
        node: &Node,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        let known = if step.requires.is_empty() {
            facts.empty_like()
        } else {
            self.supplied(Some(step), scope, facts)?
        };
        // What the step writes is its requires lines and the lines it cites:
        // a cited `N ∈ ℕ` says N ≠ 0 as surely as a requires line would
        // (`READERS.md`, what a membership says).
        let known = self.with_cited(Some(step), scope, &known, None)?;
        // An `obtain`'s memberships are in the scope under its name rather
        // than in its proved line, and are what it writes all the same.
        for r in &step.just.refs {
            for said in &self.line_sentences(r, &self.lines.clone()) {
                let term = self.term(said)?;
                if let Some(p) = self.held(facts, &term, scope)? {
                    self.know_default(&known, term, p);
                }
            }
        }
        self.writing(scope, &known, true, |me| {
            let lines = me.hypotheses_by_their_names(step, scope, facts, lines)?;
            me.by_method(how, step, node, term, scope, facts, &lines)
        })
    }

    /// The lines a step reads, each hypothesis of the theorem it names, in
    /// its `from` or as the line a substitute is put into, as it reads in
    /// the proof (`hypothesis_by_its_names`): the steps speak of a define's
    /// name where the statement writes the define out. A hypothesis the
    /// facts do not carry so is offered as it is held.
    pub(super) fn hypotheses_by_their_names(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Lines> {
        let into = step.just.into.as_ref().map(|p| p.named().to_string());
        let named: Vec<String> = step
            .just
            .refs
            .iter()
            .cloned()
            .chain(into)
            .filter(|r| self.is_hypothesis(r) && !self.hypothesis_defines(r).is_empty())
            .collect();
        let mut out: Option<Lines> = None;
        for r in named {
            if self.line_written(&r, lines).is_none() {
                continue;
            }
            let held = self.carried(&r, facts, lines);
            if let Built(carried) =
                self.hypothesis_by_its_names(&r, lines, &held, scope, facts, step)?
            {
                out.get_or_insert_with(|| lines.copy()).set(r, carried);
            }
        }
        Ok(out.unwrap_or_else(|| lines.clone()))
    }

    /// A step's proof by the method its justification names.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn by_method(
        &mut self,
        how: &How,
        step: &Step,
        node: &Node,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Option<Proof>>> {
        let made = match how {
            How::Named(m) => match m {
                Method::Algebra => self.algebra(step, term, scope, facts, lines)?,
                Method::Arithmetic => self.arithmetic(step, term, scope, facts)?,
                Method::RealArithmetic => {
                    self.real_arithmetic(step, term, scope, facts)?
                }
                // A chain is folded a link at a time, as a calculation's
                // links are, so that it rests on every line it cites. An
                // order with its converse is a linear fact of the two, which
                // the proof of an inequalities step proves; the checker has
                // held it to its own rule.
                Method::Transitivity => {
                    Built(self.transitivity_chain(step, term, scope, facts, lines)?)
                }
                Method::Inequalities | Method::Antisymmetry => {
                    self.inequalities(step, term, scope, facts, lines)?
                }
                Method::Membership => self.by_membership(step, term, scope, facts)?,
                Method::Inspection => self.inspection(step, term, scope, facts)?,
                Method::Substitute => {
                    self.substitute(step, node, term, scope, facts, lines)?
                }
                Method::Instantiate => {
                    self.instantiate(step, term, scope, facts, lines)?
                }
                Method::Calculation => {
                    self.calculation(step, term, scope, facts, lines)?
                }
                Method::Join | Method::Restate => {
                    return self.join(step, scope, facts).map(Built)
                }
                Method::Exhibit => {
                    self.exhibit(step, node, term, scope, facts, lines)?
                }
                _ => unreachable!("a method EXPANDED holds"),
            },
            How::Define => self.by_define(step, term, scope, facts)?,
            How::TakeDefinition => {
                self.take_definition(step, term, scope, facts, lines)?
            }
            How::Reading(Way::AsStated) => {
                self.cite(step, term, scope, facts, lines)?
            }
            How::Reading(Way::Conclude) => {
                self.conclude(step, term, scope, facts, lines)?
            }
            How::Reading(way) => {
                let item = self.item_cited(&step.just.head.to_string())?;
                self.trying(item, step, *way, term, scope, facts, lines)?
            }
            How::UnfoldEquation => self.unfold_equation(step, term, scope, facts)?,
            How::Cite => self.cite(step, term, scope, facts, lines)?,
        };
        Ok(made.map(Some))
    }

    // --- the methods ----------------------------------------------------
}
