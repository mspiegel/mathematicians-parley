//! Opening the outermost scope, blocks and cases.

use super::*;
use crate::checker::record::ReadAt;
use crate::elab;
use crate::notations::MEMBERSHIP;

impl<'a> Elaborator<'a> {
    /// The first frame: the theorem's hypotheses, and what they say.
    pub fn open_outermost(&mut self, scope: &Rpn, facts: &Facts) {
        self.frames = vec![Frame {
            scope: scope.clone(),
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
        scope: &Rpn,
        facts: &Facts,
        body: &Term,
        variable: &Term,
        over: &Term,
        prove: &mut Prove<'_, 'a>,
        implied: bool,
    ) -> Checked<Route<Proof>> {
        let name = self.rpn(variable);
        if !name.alone().is_some_and(|n| scope.has(n)) {
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
        let again = self.free_renamed(body, &name, &spare);
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

    /// `term` with each free `name` spelt `spare`. A class or a formula that
    /// binds `name` itself, which set.mm writes with the letter as a part of
    /// its own, keeps it: a map given for F in `A. n e. NN ( F ` n ) <_ C`,
    /// the map sending n ∈ ℕ to s(n), still sends n to s(n) when the outer n
    /// is spelt with another letter.
    pub(crate) fn free_renamed(&self, term: &Term, name: &Rpn, spare: &Rpn) -> Term {
        if term.variable().is_some() {
            return if self.rpn(term) == *name {
                self.to_term(spare)
            } else {
                term.clone()
            };
        }
        let binds_it = term.label() != Some("cv")
            && term.children().iter().any(|c| self.rpn(c) == *name);
        if binds_it {
            return term.clone();
        }
        term.with_children(
            term.children()
                .iter()
                .map(|c| self.free_renamed(c, name, spare))
                .collect(),
        )
    }

    /// `for_every` where the scope does not name the variable.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn generalised(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        body: &Term,
        name: &Rpn,
        over: &Term,
        prove: &mut Prove<'_, 'a>,
        implied: bool,
    ) -> Checked<Route<Proof>> {
        let where_ = self.rpn(over);
        let member = t!(name, "cv", where_, "wcel");
        let made = self.frames_kept(|me| -> Checked<Route<Proof>> {
            let (inner, lifted) = me.widen(scope, facts, &member, None);
            let lifted = if implied {
                let held = me
                    .held(&lifted, &member, &inner)?
                    .expect("the membership just laid down");
                let more = me.implied(&member, &held, &inner, &lifted)?;
                let out = lifted.copy();
                for (k, v) in more.entries() {
                    me.know(&out, k, v);
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
        scope: &Rpn,
        facts: &Facts,
        added: &Rpn,
        origin: Option<&str>,
    ) -> (Rpn, Facts) {
        self.widen_to(scope, facts, added, origin, 4)
    }

    /// `widen`, taking the assumption apart `depth` conjunctions deep: an
    /// `obtain` says as many things as its claim has sentences, and each is
    /// a fact a later step may cite on its own.
    pub fn widen_to(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        added: &Rpn,
        origin: Option<&str>,
        depth: usize,
    ) -> (Rpn, Facts) {
        let inner = t!(scope, added, "wa");
        let weaken = pf!(self.b; scope, added, "simpl");
        let lifted =
            facts.rebased(|k, v| pf!(self.b; inner, scope, k, weaken, v, "syl"));
        let mut here = pf!(self.b; scope, added, "simpr");
        if let Some(origin) = origin {
            here = self.seal(here, origin);
        }
        self.know(&lifted, added.clone(), here.clone());
        self.unpack(added, &here, &inner, &lifted, depth);
        // Each frame keeps what is known at it, because a step whose lemma
        // forbids an inner assumption is proved at an outer one. What is
        // known at the frame widened is what has been proved there up to
        // now, the lines written since it opened included.
        if let Some(widened) = self.frames.last_mut().filter(|f| f.scope == *scope) {
            widened.facts = facts.clone();
        }
        self.frames.push(Frame {
            scope: inner.clone(),
            added: Some(added.clone()),
            facts: lifted.clone(),
        });
        (inner, lifted)
    }

    /// A proof made under `at`, said under `scope`, if `scope` is `at`
    /// widened; None otherwise.
    pub fn lifted_to(
        &self,
        claim: &Rpn,
        proof: &Proof,
        at: &Rpn,
        scope: &Rpn,
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
            if self.rpn(&outer) == *at {
                reached = true;
                break;
            }
            node = outer;
        }
        if !reached {
            return None;
        }
        let mut here = at.clone();
        let mut proof = proof.clone();
        for added in chain.iter().rev() {
            let inner = t!(here, added, "wa");
            proof = pf!(self.b; inner, here, claim, pf!(self.b; here, added, "simpl"), proof, "syl");
            here = inner;
        }
        (here == *scope).then_some(proof)
    }

    /// A conjunctive goal, from whatever answers each of its parts; None
    /// where the goal is not one of these shapes, which is not a decline:
    /// the caller has its own way on and this had no opinion.
    pub fn conjoined(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
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
        let parts: Vec<Rpn> = wanted.children().iter().map(|c| self.rpn(c)).collect();
        let mut all: Vec<crate::mm::spell::Part> = vec![elab::part(scope)];
        all.extend(parts.iter().map(|p| elab::part(p)));
        all.extend(proofs.iter().map(|p| elab::part(p)));
        all.push(elab::part(join));
        Ok(Some(Built(self.b.proof(&all))))
    }

    /// An equation known also the other way round: a route that looks among
    /// the facts for `|U| = B` finds the line that wrote `2^k = |U|`. The
    /// way written stays the one held under its own spelling.
    pub fn know_turned(
        &mut self,
        facts: &Facts,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
    ) {
        let Some((turned, flip)) = self.turned_claim(term) else {
            return;
        };
        // Stored as written, not merely held under the same standard form:
        // a route that reads the facts one by one sees only what is written
        // there. A later proof of the equation is a later proof of it turned,
        // as a later proof of a claim replaces an earlier one, so that a step
        // takes the line it names and not an earlier one saying the same.
        let Sides { left, right } = self.equation_sides(term);
        let made = pf!(self.b; scope, left, right, proof.clone(), flip);
        self.know(facts, turned, made);
    }

    /// Each sentence a conjunction joins, and each group of them it nests
    /// together, known with its proof: `simpld` and `simprd` take it apart,
    /// as a line saying several sentences supplies each of them.
    pub fn know_conjuncts(
        &mut self,
        facts: &Facts,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
    ) {
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return;
        }
        let pair: Vec<Rpn> = node.children().iter().map(|c| self.rpn(c)).collect();
        let left = pf!(self.b; scope, pair[0], pair[1], proof.clone(), "simpld");
        let right = pf!(self.b; scope, pair[0], pair[1], proof.clone(), "simprd");
        self.know_conjuncts(facts, &pair[0], &left, scope);
        self.know(facts, pair[0].clone(), left);
        self.know_conjuncts(facts, &pair[1], &right, scope);
        self.know(facts, pair[1].clone(), right);
    }

    /// The equation between any two terms of each chain of equations the
    /// sentences `said` write, known with its proof, as a line claiming a
    /// chain supplies them (`SYNTAX.md`). `term` is the sentences joined
    /// from the left, as a claim of several reads, and `proof` proves it:
    /// each pair is taken from that proof, so a step naming the line rests
    /// on the line.
    pub fn know_chains(
        &mut self,
        said: &[Node],
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) {
        let Some((last, rest)) = said.split_last() else {
            return;
        };
        if rest.is_empty() {
            return self.know_chain(last, term, proof, scope, facts);
        }
        let Some(Halves {
            left,
            right,
            first,
            second,
        }) = self.halves(term, proof, scope)
        else {
            return;
        };
        self.know_chains(rest, &left, &first, scope, facts);
        self.know_chain(last, &right, &second, scope, facts);
    }

    /// `know_chains` of one sentence: a chain of equations, or a
    /// conjunction with chains in it.
    pub(super) fn know_chain(
        &mut self,
        said: &Node,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) {
        if said.spelling() == AND {
            let Some(Halves {
                left,
                right,
                first,
                second,
            }) = self.halves(term, proof, scope)
            else {
                return;
            };
            self.know_chain(&said.children[0], &left, &first, scope, facts);
            return self.know_chain(&said.children[1], &right, &second, scope, facts);
        }
        if said.notation() != EQUAL_CHAIN {
            return;
        }
        // The links joined from the left, ((t0 = t1 ∧ t1 = t2) ∧ t2 = t3),
        // each proved by taking the last off what remains; the terms are
        // read off the links, the kernel's own.
        let mut links: Vec<(Rpn, Proof)> = Vec::new();
        let (mut held, mut whole) = (term.clone(), proof.clone());
        for _ in 2..said.children.len() {
            let Some(Halves {
                left,
                right,
                first,
                second,
            }) = self.halves(&held, &whole, scope)
            else {
                return;
            };
            links.push((right, second));
            (held, whole) = (left, first);
        }
        links.push((held, whole));
        links.reverse();
        let mut terms: Vec<Rpn> = Vec::new();
        for (link, _) in &links {
            let equation = self.to_term(link);
            let [first, second] = equation.children() else {
                return;
            };
            if equation.label() != Some("wceq") {
                return;
            }
            if terms.is_empty() {
                terms.push(self.rpn(first));
            }
            terms.push(self.rpn(second));
        }
        let links: Vec<Proof> = links.into_iter().map(|(_, proof)| proof).collect();
        for i in 0..links.len() {
            let mut joined = links[i].clone();
            for j in i + 2..terms.len() {
                joined = self.b.ap(
                    "eqtrd",
                    &binds! {
                        "ph" => scope,
                        "A" => &terms[i],
                        "B" => &terms[j - 1],
                        "C" => &terms[j]
                    },
                    &[&joined, &links[j - 1]],
                );
                let pair = t!(terms[i], terms[j], "wceq");
                self.know(facts, pair.clone(), joined.clone());
                self.know_turned(facts, &pair, &joined, scope);
            }
        }
    }

    /// A conjunction's two sides with their proofs, `simpld` and `simprd`
    /// taking it apart; None for a term that is no conjunction.
    pub(super) fn halves(
        &self,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
    ) -> Option<Halves> {
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return None;
        }
        let left = self.rpn(&node.children()[0]);
        let right = self.rpn(&node.children()[1]);
        let first = pf!(self.b; scope, left, right, proof.clone(), "simpld");
        let second = pf!(self.b; scope, left, right, proof.clone(), "simprd");
        Some(Halves {
            left,
            right,
            first,
            second,
        })
    }

    /// How deep `term` is a conjunction: 0 for anything else, and one more
    /// than its deepest part for a conjunction. A fact taken apart this deep
    /// says each thing its "and"s join, however many there are.
    pub fn conjunction_depth(&self, term: &Rpn) -> usize {
        fn depth(node: &Term) -> usize {
            match node.label().and_then(|l| lookup(rules::SPLIT, l)) {
                Some(_) => 1 + node.children().iter().map(depth).max().unwrap_or(0),
                None => 0,
            }
        }
        depth(&self.to_term(term))
    }

    /// Each conjunct of a fact recorded as a fact of its own, through every
    /// "and" the fact is joined by.
    pub fn unpack_all(
        &mut self,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) {
        let depth = self.conjunction_depth(term) + 1;
        self.unpack(term, proof, scope, facts, depth);
    }

    /// The readings at a block's letter (`CheckedTheorem::read_at`) of the
    /// first step written below the line `below`: what the lines in scope
    /// say at the letters let there, as the `let` on that line opens.
    pub fn readings_below(&self, below: usize) -> Vec<ReadAt> {
        self.thm
            .steps
            .iter()
            .position(|s| s.line > below)
            .and_then(|i| self.checked.read_at.get(i))
            .cloned()
            .unwrap_or_default()
    }

    /// The readings at a block's letter of the step being elaborated
    /// (`CheckedTheorem::read_at`).
    pub fn step_readings(&self) -> Vec<ReadAt> {
        self.step_now
            .and_then(|i| self.checked.read_at.get(i))
            .cloned()
            .unwrap_or_default()
    }

    /// Record a block's `let x ∈ X` as a letter the lines cited inside the
    /// block are read at (`know_at_letters`), with the `let` line's
    /// reference. A `let` saying no membership records none.
    pub fn add_block_letter(
        &mut self,
        member: &Rpn,
        proof: &Proof,
        at: &Rpn,
        opened_by: &str,
    ) {
        let node = self.to_term(member);
        if node.label() != Some("wcel") || node.children().len() != 2 {
            return;
        }
        let letter = BlockLetter {
            letter: self.rpn(&node.children()[0]),
            set: self.rpn(&node.children()[1]),
            opened_by: opened_by.to_string(),
            member: member.clone(),
            proof: proof.clone(),
            at: at.clone(),
        };
        self.block_letters.push(letter);
    }

    /// What a line's sentence "for all a ∈ X, P(a)" says inside a block that
    /// opened with `let x ∈ X` (`SYNTAX.md`): P(x), known in `facts` with the
    /// line's own origin, so that it is what a step citing the line has.
    /// The letter is the one the checker read the line `line` at
    /// (`CheckedTheorem::read_at`) among `readings`, those of the step the
    /// reading is for, by the `let` line that lets it; where two blocks let
    /// letters of X, the checker reads it at neither. The instance known, if
    /// any.
    #[allow(clippy::too_many_arguments)]
    pub fn know_at_letters(
        &mut self,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
        line: &str,
        readings: &[ReadAt],
    ) -> Checked<Option<Rpn>> {
        let whole = self.to_term(term);
        if whole.label() != Some("wral") || whole.children().len() != 3 {
            return Ok(None);
        }
        let body = whole.children()[0].clone();
        let var = self.rpn(&whole.children()[1]).to_string();
        let domain = self.rpn(&whole.children()[2]);
        // The `let` lines whose letter the checker read this "for all" of
        // the line at. The line as elaborated may bind another letter than
        // the sentence read afresh: one claim with its bound variable
        // renamed.
        let mut lets: Vec<String> = Vec::new();
        for reading in readings.iter().filter(|r| r.line == line) {
            if lets.contains(&reading.opened_by.line) {
                continue;
            }
            let recorded = self.term(&reading.said)?;
            let same = recorded == *term
                || self
                    .renaming(&self.to_term(&recorded), &self.to_term(term))?
                    .is_some();
            if same {
                lets.push(reading.opened_by.line.clone());
            }
        }
        let fitting: Vec<BlockLetter> = self
            .block_letters
            .iter()
            .filter(|l| lets.contains(&l.opened_by))
            .cloned()
            .collect();
        let [letter] = fitting.as_slice() else {
            return Ok(None);
        };
        let Some(lifted) =
            self.lifted_to(&letter.member, &letter.proof, &letter.at, scope)
        else {
            return Ok(None);
        };
        // Where the block's set is the "for all"'s in another spelling, the
        // letter's membership of it as the line writes it, carried from its
        // own.
        let required = if letter.set == domain {
            lifted
        } else {
            let wider = self.to_term(&t!(letter.letter, domain, "wcel"));
            let held = Facts::new();
            self.know(&held, letter.member.clone(), lifted);
            match self.settle(&wider, scope, &held, 3, None, None)? {
                Built(p) => p,
                Declined(_) => return Ok(None),
            }
        };
        let at = letter.letter.clone();
        let member = match letter.set == domain {
            true => letter.member.clone(),
            false => t!(at, domain, "wcel"),
        };
        let mark = t!(var, "cv");
        // A body binding the block's letter itself would capture it.
        let named = self.to_term(&at).names();
        if at != mark && body.names().iter().any(|n| named.contains(n)) {
            return Ok(None);
        }
        let ph = self.rpn(&body);
        let (instance, made) = if at == mark {
            // The block's letter is the line's bound letter in the kernel, so
            // `rsp` reads the body as it stands.
            let read = self.b.ap(
                "rsp",
                &binds! {"ph" => &ph, "x" => &var, "A" => &domain},
                &[],
            );
            let turned = pf!(self.b; term, member, ph, read, "com12");
            let carried =
                pf!(self.b; scope, member, t!(term, ph, "wi"), required, turned, "syl");
            (
                ph.clone(),
                pf!(self.b; scope, term, ph, proof, carried, "mpd"),
            )
        } else {
            let Some((_, rule)) = rules::INSTANCES.iter().find(|(k, _)| *k == "wral")
            else {
                return Ok(None);
            };
            let ps = self.rpn(&self.restated(&body, &mark, &at));
            let tie = self.to_term(&t!(t!(mark, at, "wceq"), t!(ph, ps, "wb"), "wi"));
            let Built(asked) = self.prove_essential(&tie, scope, facts)? else {
                return Ok(None);
            };
            let mut binds = binds! {"ph" => &ph, "ps" => &ps, "x" => &var, "A" => &at};
            binds.insert(rule.domain_var.to_string(), domain.clone());
            let applied = self.b.ap(rule.lemma, &binds, &[&asked]);
            let carried = pf!(self.b; scope, member, t!(term, ps, "wi"), required, applied, "syl");
            (
                ps.clone(),
                pf!(self.b; scope, term, ps, proof, carried, "mpd"),
            )
        };
        let made = Proof {
            items: made.items,
            origin: proof.origin.clone(),
        };
        self.know(facts, instance.clone(), made);
        Ok(Some(instance))
    }

    /// Record each conjunct of a fact as a fact of its own.
    pub fn unpack(
        &mut self,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
        depth: usize,
    ) {
        self.unpack_as(term, proof, scope, facts, depth, true);
    }

    /// `unpack`, each conjunct recorded as the fact proved last where
    /// `latest`, and otherwise only as what the line the proof rests on gave.
    pub(super) fn unpack_as(
        &mut self,
        term: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
        depth: usize,
        latest: bool,
    ) {
        if depth == 0 {
            return;
        }
        if latest {
            self.know_turned(facts, term, proof, scope);
        }
        let node = self.to_term(term);
        let Some(picks) = node.label().and_then(|l| lookup(rules::SPLIT, l)) else {
            return;
        };
        if picks.len() != node.children().len() {
            return;
        }
        let kids: Vec<Rpn> = node.children().iter().map(|c| self.rpn(c)).collect();
        for (part, pick) in kids.iter().zip(picks.iter()) {
            // A part an earlier line said too stays as that line proved it,
            // and is kept as this line gives it for a step naming this one.
            let latest = latest && !self.holds(facts, part);
            let mut all: Vec<crate::mm::spell::Part> = vec![
                elab::part(scope),
                elab::part(term),
                elab::part(part),
                elab::part(proof),
            ];
            all.extend(kids.iter().map(|k| elab::part(k)));
            all.push(elab::part(*pick));
            all.push(elab::part("syl"));
            let made = self.b.proof(&all);
            if latest {
                self.know(facts, part.clone(), made.clone());
            } else {
                facts.store_for_line(part, made.clone());
            }
            self.unpack_as(part, &made, scope, facts, depth - 1, latest);
        }
    }

    /// A block's assumption is conjoined onto the antecedent. All four block
    /// forms do this; what differs is the lemma that closes them.
    pub fn open_block(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Block> {
        let mut block = Block {
            owner: step.clone(),
            outer: scope.clone(),
            outside: facts.clone(),
            frame: self.frames.len() - 1,
            scope: scope.clone(),
            facts: facts.clone(),
            supposed: None,
            over: None,
            base: None,
            variable: None,
            added: None,
            letters_at: self.block_letters.len(),
            opened: Vec::new(),
            // Taken before the block names anything, so that what it names is
            // what closing it gives back.
            named: self.names.clone(),
            bound: self.bound_as.clone(),
            inner: IndexMap::new(),
            lines: self.lines.copy(),
            assumed: IndexMap::new(),
            entered: None,
            case_opened_at: None,
            opened_at: 0,
            claim: Rpn::default(),
            proof: None,
            parts: IndexMap::new(),
            by_part: None,
        };
        match step.just.head.method() {
            Some(Method::Contradiction) => {
                let o = &step.openers[0];
                let node = self.hypothesis_node(o.kind, &o.body(&self.thm.path))?;
                let supposed = self.term(&node)?;
                let origin = assumption(&block, &o.label);
                let (inner, lifted) =
                    self.widen(scope, facts, &supposed, Some(&origin));
                if !o.label.is_empty() {
                    let proof = self
                        .held(&lifted, &supposed, &inner)?
                        .expect("the supposition just laid down");
                    self.lines.set(
                        o.label.clone(),
                        Line::new(supposed.clone(), proof, vec![node]),
                    );
                }
                block.supposed = Some(supposed);
                block.scope = inner;
                block.facts = lifted;
                self.contradicted = None;
            }
            Some(Method::Proof) => {
                // A `by` line's openers open the block it names
                // (`open_by_part`).
                for o in step.openers.iter().filter(|o| !o.after_by) {
                    let said = self.hypothesis_node(o.kind, &o.body(&self.thm.path))?;
                    if o.kind == Intro::Let {
                        // A fixed name is a variable of the kernel, not a
                        // class, and it must avoid whatever the notations
                        // bind.
                        let node = said.clone();
                        let name = node.leftmost().text.to_string();
                        let var = self.fixed_var(&name, &block.scope.clone())?;
                        self.names.insert(name.clone(), t!(var, "cv"));
                        block.variable = Some(var);
                        // `let X be a set` fixes a name over nothing, so
                        // there is no set to record.
                        if node.notation() == MEMBERSHIP {
                            let set = self.term(&node.children[1])?;
                            self.sets.insert(name, set);
                        }
                    }
                    let node = said;
                    let written = self.term(&node)?;
                    // `let f : X → Y` opens the block at a member of the
                    // functions from X to Y, which "for all f : X → Y" runs
                    // over and closing gives back; its type is read off the
                    // membership, as an obtained function's is (`elmapi`).
                    let function =
                        match (o.kind, node.notation(), node.children.as_slice()) {
                            (Intro::Let, FUNCTION_TYPE, [f, from, to]) => {
                                let set = FunctionSet {
                                    domain: self.term(from)?,
                                    codomain: self.term(to)?,
                                };
                                Some((self.term(f)?, set))
                            }
                            _ => None,
                        };
                    let added = match &function {
                        Some((named, set)) => {
                            let over = t!(&set.codomain, &set.domain, "cmap", "co");
                            self.sets
                                .insert(node.leftmost().text.to_string(), over.clone());
                            t!(named, over, "wcel")
                        }
                        None => written.clone(),
                    };
                    block.opened.push(added.clone());
                    let origin = assumption(&block, &o.label);
                    let (inner, lifted) = self.widen(
                        &block.scope.clone(),
                        &block.facts.clone(),
                        &added,
                        Some(&origin),
                    );
                    block.scope = inner;
                    block.facts = lifted;
                    let held = self
                        .held(&block.facts.clone(), &added, &block.scope.clone())?
                        .expect("the assumption just laid down");
                    let held = match &function {
                        Some((named, set)) => {
                            let law = self.b.ap(
                                "elmapi",
                                &binds! {"A" => named, "B" => &set.codomain, "C" => &set.domain},
                                &[],
                            );
                            let scope = block.scope.clone();
                            let typed =
                                pf!(self.b; &scope, added, written, held, law, "syl");
                            self.know(
                                &block.facts.clone(),
                                written.clone(),
                                typed.clone(),
                            );
                            typed
                        }
                        None => held,
                    };
                    if o.kind == Intro::Let && function.is_none() {
                        self.add_block_letter(
                            &added,
                            &held,
                            &block.scope.clone(),
                            &o.label,
                        );
                        self.let_sethood(
                            &o.label,
                            &node,
                            &written,
                            &block.scope.clone(),
                            &block.facts.clone(),
                        )?;
                        let readings = self.readings_below(o.line);
                        self.know_in_scope_at_letters(
                            &block.scope.clone(),
                            &block.facts,
                            &readings,
                        )?;
                    }
                    if !o.label.is_empty() {
                        self.lines
                            .set(o.label.clone(), Line::new(written, held, vec![node]));
                    }
                }
                self.note_introduced(&block.scope.clone(), &block.facts.clone())?;
            }
            Some(Method::Cases | Method::BothDirections) => {
                // Every other block opens one scope for all its children. A
                // `cases` opens one per part, so nothing is widened here and
                // the part is entered when its first child arrives; each
                // direction of a `both directions` is such a part.
                for o in step.openers.iter().filter(|o| !o.after_by) {
                    let node = self.hypothesis_node(o.kind, &o.body(&self.thm.path))?;
                    block
                        .assumed
                        .insert(o.part.unwrap_or(0), (node, o.label.clone()));
                }
            }
            Some(Method::Induction) => {
                // The letter the claim says "for all k ∈ X, …" of, as the
                // checker holds.
                let over = step
                    .just
                    .on
                    .clone()
                    .expect("an induction says what it is on");
                let base = self.spare_var()?;
                // The step part fixes a name of its own, and `nn0indd` wants
                // that one apart from this.
                self.taken.insert(base.clone());
                // The statement after "for all k ∈ X," is read three times:
                // here, at the step part's hypothesis, and at the close. Read
                // once now, the letters it binds are settled, and the block
                // keeps them, so the three readings are one formula.
                let general = t!(base, "cv");
                let claim = step.claim.clone();
                self.names_kept(|me| -> Checked<()> {
                    me.names.insert(over.clone(), general);
                    let node = me.claim_node(&claim)?;
                    me.freeze(&node.children[2])?;
                    Ok(())
                })?;
                block.bound = self.bound_as.clone();
                block.over = Some(over);
                block.base = Some(base);
            }
            _ => {
                let head = &step.just.head;
                return Err(self
                    .unreached(step.line, format!("no expansion for a {head} block")));
            }
        }
        Ok(block)
    }

    /// Open the scope one case of a `cases` block runs under.
    pub fn enter_case(
        &mut self,
        block: &mut Block,
        part: usize,
    ) -> Checked<(Rpn, Facts)> {
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
            let proof = self
                .held(&block.facts.clone(), &assumed, &block.scope.clone())?
                .expect("the case just laid down");
            self.lines.set(label, Line::new(assumed, proof, vec![node]));
        }
        Ok((block.scope.clone(), block.facts.clone()))
    }

    /// A claim of one sentence, read; a defect where it is several.
    pub(super) fn claim_node(&mut self, claim: &Written) -> Checked<Node> {
        self.read_one(claim)
    }

    /// Open the scope one part of an induction runs under. The base part runs
    /// under the block's own scope. The step part fixes the claim's letter as
    /// a `proof` block does, `let k ∈ X`, and assumes the claim's statement at it,
    /// the induction hypothesis, each laid down with its label.
    pub fn enter_induction_part(
        &mut self,
        block: &mut Block,
        part: usize,
    ) -> Checked<(Rpn, Facts)> {
        if block.entered == Some(part) {
            return Ok((block.scope.clone(), block.facts.clone()));
        }
        // Each part starts from the names and bound letters the block opened
        // with, as the block's close reads its claim with them: a letter the
        // base part fixed is not the one the statement binds.
        self.frames.truncate(block.frame + 1);
        self.names = block.named.clone();
        self.bound_as = block.bound.clone();
        self.block_letters.truncate(block.letters_at);
        block.scope = block.outer.clone();
        block.facts = block.outside.clone();
        block.entered = Some(part);
        let openers: Vec<_> = block
            .owner
            .openers
            .iter()
            .filter(|o| o.part == Some(part) && !o.after_by)
            .cloned()
            .collect();
        // The first `let` fixes the claim's letter; a second, over the parts
        // of a set, the member the step adds.
        let mut lets = 0;
        for o in openers {
            let said = match o.is_hypothesis {
                true => None,
                false => Some(self.hypothesis_node(o.kind, &o.body(&self.thm.path))?),
            };
            if let (Intro::Let, Some(node)) = (o.kind, &said) {
                let name = node.leftmost().text.to_string();
                let var = self.fixed_var(&name, &block.scope.clone())?;
                self.names.insert(name.clone(), t!(var, "cv"));
                if lets == 0 {
                    block.variable = Some(var);
                } else {
                    block.added = Some(var);
                }
                lets += 1;
                let set = self.term(&node.children[1])?;
                self.sets.insert(name, set);
            }
            // The induction hypothesis is the claim's statement at the letter
            // just fixed, read as the close reads the statement, so that the
            // two are one formula with one choice of bound letters.
            // What the line says is kept as the page's tree, which a citation
            // of it is matched against (`citing`); its term is the frozen one.
            let (node, added) = match said {
                None => {
                    let claim = self.claim_node(&block.owner.claim)?;
                    let frozen = self.freeze(&claim.children[2])?;
                    let added = self.term(&frozen)?;
                    (claim.children[2].clone(), added)
                }
                Some(said) => {
                    let added = self.term(&said)?;
                    (said, added)
                }
            };
            let origin = assumption(block, &o.label);
            let (inner, lifted) = self.widen(
                &block.scope.clone(),
                &block.facts.clone(),
                &added,
                Some(&origin),
            );
            block.scope = inner;
            block.facts = lifted;
            let proof = self
                .held(&block.facts.clone(), &added, &block.scope.clone())?
                .expect("the assumption just laid down");
            if o.kind == Intro::Let && !o.is_hypothesis {
                self.add_block_letter(&added, &proof, &block.scope.clone(), &o.label);
                self.let_sethood(
                    &o.label,
                    &node,
                    &added,
                    &block.scope.clone(),
                    &block.facts.clone(),
                )?;
                let readings = self.readings_below(o.line);
                self.know_in_scope_at_letters(
                    &block.scope.clone(),
                    &block.facts,
                    &readings,
                )?;
            }
            self.lines
                .set(o.label.clone(), Line::new(added, proof, vec![node]));
        }
        self.note_introduced(&block.scope.clone(), &block.facts.clone())?;
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
            let claim = self.claim_of(&block.owner.claim)?;
            let assumed = self.term(&block.assumed[&part].0)?;
            let mut proof = self
                .held(&facts, &assumed, &scope)?
                .expect("the case just laid down");
            if assumed != claim {
                // The claim written another way, `b = a` for `a = b`.
                let alike = self.same(
                    &self.to_term(&assumed),
                    &self.to_term(&claim),
                    &scope,
                    &facts,
                    Some(&block.owner),
                )?;
                let Built(alike) = alike else {
                    return Err(self.defect(
                        o.line,
                        "the case's assumption is not the block's claim",
                    ));
                };
                proof = pf!(self.b; scope, assumed, claim, proof, alike, "mpbid");
            }
            block.parts.insert(
                part,
                PartEnd {
                    claim,
                    proof,
                    scope,
                    facts,
                },
            );
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
            if let Some(end) = block.parts.get(&entered).cloned() {
                let mut proof = end.proof;
                for close in inside.iter().rev() {
                    proof = self.close(close, proof, &end.claim)?;
                }
                block.parts.insert(
                    entered,
                    PartEnd {
                        claim: end.claim,
                        proof,
                        scope: block.scope.clone(),
                        facts: block.facts.clone(),
                    },
                );
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
                PartEnd {
                    claim: done.claim.clone(),
                    proof: done.proof.clone().expect("a closed block's proof"),
                    scope: done.outer.clone(),
                    facts: done.outside.clone(),
                },
            );
        }
    }

    /// The line a contradiction block closes on, where `step` is the block's
    /// last step as the checker's record has it (`record::Block::last`) and
    /// names a line it contradicts: a step taken alone, or one owning a
    /// block, `1.1. x > 0, cases, from H2, contradicting S`, its claim shown
    /// by its cases. Any other step's `contradicting` closes nothing here.
    pub fn contradicted_at(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        let Some(other) = &step.just.contradicting else {
            return Ok(());
        };
        let Some(at) = CheckedTheorem::index_of(self.thm, step) else {
            return Ok(());
        };
        // The step ends a part that closes by contradiction: the owner's
        // own method, or the part's `by` method.
        let ends = self.checked.places[at].is_some_and(|p| {
            let owner = &self.thm.steps[self.checked.blocks[p.block].owner];
            self.checked.last_in(p.block, p.part) == Some(at)
                && owner.closing(p.part) == Some(Method::Contradiction)
        });
        if !ends {
            return Ok(());
        }
        let lines = self.lines.clone();
        let Some(line) = self.line_written(other, &lines) else {
            return Ok(());
        };
        let proof = self.carried(other, facts, &lines);
        let mine = self.line_written(&number_of(step), &lines);
        let reordered = match mine {
            Some(own) => {
                let theirs = ProvedClaim {
                    claim: line.claim.clone(),
                    proof: proof.clone(),
                };
                match self.reordered_against(&theirs, &own, scope, facts)? {
                    Some(found) => Some(found),
                    None => self.reordered_against(&own, &theirs, scope, facts)?,
                }
            }
            None => None,
        };
        let says = self
            .line_says(other, scope, facts, &lines)?
            .entries()
            .into_iter()
            .filter(|(claim, _)| *claim != line.claim)
            .map(|(claim, proof)| ProvedClaim { claim, proof })
            .collect();
        self.contradicted = Some(Contradicted {
            claim: line.claim,
            proof,
            reordered,
            says,
        });
        Ok(())
    }

    /// `said` carried to the order of its points that `denial` denies, where
    /// `denial` is the negation of the same claim about the same three
    /// points named otherwise; None for any other pair.
    pub(super) fn reordered_against(
        &mut self,
        said: &ProvedClaim,
        denial: &ProvedClaim,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<ProvedClaim>> {
        let denied = self.to_term(&denial.claim);
        if denied.label() != Some("wn") {
            return Ok(None);
        }
        let inner = self.rpn(&denied.children()[0]);
        if inner == said.claim || !self.reorders(&said.claim, &inner) {
            return Ok(None);
        }
        let known = facts.copy();
        self.know(&known, said.claim.clone(), said.proof.clone());
        Ok(self.held(&known, &inner, scope)?.map(|proof| ProvedClaim {
            claim: inner,
            proof,
        }))
    }
}
