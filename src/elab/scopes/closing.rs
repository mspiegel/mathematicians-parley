//! Closing blocks, cases and inductions.

use super::*;

impl<'a> Elaborator<'a> {
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
        deep: &Rpn,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        let step = block.owner.clone();
        let inside: Vec<Closer> =
            closers[block.opened_at.min(closers.len())..].to_vec();
        // What a `proof` block owes names what the block fixed, so it is
        // read before the block gives its names back.
        let owed = if step.just.head.is(Method::Proof) {
            Some(self.owed_goal(&step)?)
        } else {
            None
        };
        // A block gives back its scope and its names together.
        block.inner = self.bound_as.clone();
        self.frames.truncate(block.frame + 1);
        self.names = block.named.clone();
        self.bound_as = block.bound.clone();
        self.block_letters.truncate(block.letters_at);
        let mut closers = closers;
        let (claim, proof) = match step.just.head.method() {
            Some(Method::Contradiction) => {
                let made = self.close_contradiction(block, facts, &inside, deep)?;
                closers.truncate(block.opened_at);
                made
            }
            Some(Method::Proof) => {
                let last = self.last.clone().expect("a block's last step");
                let held = self
                    .line_written(&last, &self.lines)
                    .expect("the block's last line");
                let owed = owed.expect("a proof block's goal");
                let made = self.close_proof_block(block, &held, &inside, &owed)?;
                closers.truncate(block.opened_at);
                made
            }
            Some(Method::Cases) => {
                closers = self.end_case(block, closers)?;
                self.close_cases(block)?
            }
            Some(Method::BothDirections) => {
                closers = self.end_case(block, closers)?;
                self.close_both(block)?
            }
            _ => {
                closers = self.end_case(block, closers)?;
                self.close_induction(block)?
            }
        };
        let number = number_of(&step);
        // A block a part's `by` line opened is no step: what it proves is
        // its part's end, which `hand_up` gives the block around it, or for
        // a block with no parts the line that block closes on.
        if let Some(by) = block.by_part {
            block.claim = claim.clone();
            block.proof = Some(proof.clone());
            let outer = block.outside.copy();
            self.know(&outer, claim.clone(), proof.clone());
            self.lines.restore(&block.lines);
            if by.part.is_none() {
                let key = format!("{number} by");
                self.lines
                    .set(key.clone(), Line::new(claim, proof, Vec::new()));
                self.last = Some(key);
            }
            return Ok((block.outer.clone(), outer, closers));
        }
        let proof = self.check_step(proof, &step, &number, true)?;
        block.claim = claim.clone();
        block.proof = Some(proof.clone());
        let outer = block.outside.copy();
        self.know(&outer, claim.clone(), proof.clone());
        // A block's claim is a line like any other, which a later step may
        // rewrite: Cantor's x ∉ B, shown by cases, becomes x ∉ f(x). The
        // block's own lines end with it.
        let said = self.said(&step)?;
        self.lines.restore(&block.lines);
        self.lines
            .set(number.clone(), Line::new(claim, proof, said));
        self.last = Some(number);
        Ok((block.outer.clone(), outer, closers))
    }

    /// A contradiction closes on its last step and the line that step
    /// contradicts: `pm2.21dd` takes the pair to the block's claim first, the
    /// obtains raised inside the block discharge that, and the supposition is
    /// dropped last.
    pub(super) fn close_contradiction(
        &mut self,
        block: &Block,
        facts: &Facts,
        inside: &[Closer],
        deep: &Rpn,
    ) -> Checked<(Rpn, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let supposed = block.supposed.clone().unwrap_or_default();
        let Some(other) = self.contradicted.clone() else {
            return Err(
                self.unreached(step.line, "the block's last step contradicts no line")
            );
        };
        let held = self
            .last
            .as_ref()
            .and_then(|l| self.line_written(l, &self.lines));
        // The line named is known by its own proof.
        let facts = facts.copy();
        self.know(&facts, other.claim.clone(), other.proof);
        let mut offered = vec![other.claim];
        if let Some(h) = &held {
            offered.push(h.claim.clone());
        }
        // One of the two carried to the order of points its denial names,
        // while the block's scope held (`contradicted_at`).
        if let Some(carried) = other.reordered {
            self.know(&facts, carried.claim.clone(), carried.proof);
            offered.push(carried.claim);
        }
        for said in other.says {
            self.know(&facts, said.claim.clone(), said.proof);
            offered.push(said.claim);
        }
        let Some((first, second, known)) = self.opposing(&offered, &facts, deep)?
        else {
            return Err(self.defect(
                step.line,
                "the last step and the line it contradicts are not a contradiction",
            ));
        };
        let claim = self.block_claim(step)?;
        let one = self
            .held(&known, &first, deep)?
            .expect("a claim `opposing` found held");
        let two = self
            .held(&known, &second, deep)?
            .expect("a claim `opposing` found held");
        let mut proof = pf!(self.b; deep, first, claim, one, two, "pm2.21dd");
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
        let ends = Supposed {
            supposed: &supposed,
            claim: &claim,
            lifted: &lifted,
        };
        if let Built(proof) = self.supposed_otherwise(&ends, scope, &known)? {
            return Ok((claim.clone(), proof));
        }
        Err(self.defect(
            step.line,
            "the block claims neither its supposition negated nor what its supposition denies",
        ))
    }

    /// ( scope -> claim ) where the block supposes what its claim denies, or
    /// denies what its claim says, written another way, as the checker reads
    /// the two alike: a ≠ 1 from `suppose 1 = a`. The spellings' equivalence
    /// (`same`) carries the supposition to the claim's spelling, and the
    /// contradiction closes there.
    pub(super) fn supposed_otherwise(
        &mut self,
        ends: &Supposed,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let Supposed {
            supposed,
            claim,
            lifted,
        } = *ends;
        let (claim_term, supposed_term) = (self.to_term(claim), self.to_term(supposed));
        // Reductio: the claim is ¬X, and the block supposed X written
        // otherwise.
        if claim_term.label() == Some("wn") {
            let x = self.rpn(&claim_term.children()[0]);
            let alike = take!(self.same(
                &supposed_term,
                &claim_term.children()[0],
                scope,
                known,
                None
            )?);
            let not_supposed = t!(supposed, "wn");
            let neg = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => supposed, "ch" => &x},
                &[&alike],
            );
            let turned = self.b.ap(
                "imbi2d",
                &binds! {"ph" => scope, "ps" => &not_supposed, "ch" => claim, "th" => supposed},
                &[&neg],
            );
            let denying = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(supposed, not_supposed, "wi"),
                "ch" => t!(supposed, claim, "wi")},
                &[lifted, &turned],
            );
            let denied = self.b.ap(
                "pm2.01d",
                &binds! {"ph" => scope, "ps" => supposed},
                &[&denying],
            );
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => &not_supposed, "ch" => claim},
                &[&denied, &neg],
            )));
        }
        // Indirect proof: the block supposed ¬Y, and the claim is Y written
        // otherwise.
        if supposed_term.label() == Some("wn") {
            let y = self.rpn(&supposed_term.children()[0]);
            let alike = take!(self.same(
                &supposed_term.children()[0],
                &claim_term,
                scope,
                known,
                None
            )?);
            let turned = self.b.ap(
                "imbi2d",
                &binds! {"ph" => scope, "ps" => &y, "ch" => claim, "th" => supposed},
                &[&alike],
            );
            let back = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(supposed, y, "wi"),
                "ch" => t!(supposed, claim, "wi")},
                &[lifted, &turned],
            );
            let got =
                self.b
                    .ap("pm2.18d", &binds! {"ph" => scope, "ps" => &y}, &[&back]);
            return Ok(Built(self.b.ap(
                "mpbid",
                &binds! {"ph" => scope, "ps" => &y, "ch" => claim},
                &[&got, &alike],
            )));
        }
        Ok(Route::no(
            "the claim is no supposition denied, written any way",
        ))
    }

    /// A claim and its negation, among the parts of what the block holds.
    pub fn opposing(
        &mut self,
        lines: &[Rpn],
        facts: &Facts,
        scope: &Rpn,
    ) -> Checked<Option<(Rpn, Rpn, Facts)>> {
        let known = facts.copy();
        for line in lines {
            if let Some(p) = self.held(&known, line, scope)? {
                self.unpack_all(line, &p, scope, &known);
            }
        }
        let parts: Vec<Rpn> = lines.iter().flat_map(|l| self.parts(l)).collect();
        let seen: Vec<Rpn> = parts
            .into_iter()
            .filter(|t| self.holds(&known, t))
            .collect();
        for one in &seen {
            for other in &seen {
                if *other == t!(one, "wn") {
                    return Ok(Some((one.clone(), other.clone(), known)));
                }
            }
        }
        // The two may deny one another written different ways, `a = b` and
        // `b ≠ a`: the fact is carried to the spelling its denial has.
        for one in &seen {
            for other in &seen {
                let denied = self.to_term(other);
                if denied.label() != Some("wn") {
                    continue;
                }
                let inner = self.rpn(&denied.children()[0]);
                if inner == *one {
                    continue;
                }
                let alike = self.same(
                    &self.to_term(one),
                    &denied.children()[0],
                    scope,
                    &known,
                    None,
                )?;
                let Built(alike) = alike else {
                    continue;
                };
                let held = self
                    .held(&known, one, scope)?
                    .expect("a fact just seen held");
                let carried = pf!(self.b; scope, one, inner, held, alike, "mpbid");
                self.know(&known, inner.clone(), carried);
                return Ok(Some((inner, other.clone(), known)));
            }
        }
        Ok(None)
    }

    /// An existence over `depth` names whose body is an equation, with the
    /// equation turned around; None where the body is no equation.
    pub fn existence_turned(&self, ex: &Rpn, depth: usize) -> Option<Rpn> {
        let whole = self.to_term(ex);
        let mut layers: Vec<Term> = Vec::new();
        let mut rest = whole;
        for _ in 0..depth {
            if rest.label() != Some("wrex") {
                return None;
            }
            layers.push(rest.clone());
            rest = rest.children()[0].clone();
        }
        let (turned, _) = self.turned_claim(&self.rpn(&rest))?;
        let mut body = self.to_term(&turned);
        for layer in layers.iter().rev() {
            let kids = layer.children();
            body = Term::apply("wrex", vec![body, kids[1].clone(), kids[2].clone()]);
        }
        Some(self.rpn(&body))
    }

    /// A fact and every conjunct inside it, the whole one first.
    pub fn parts(&self, term: &Rpn) -> Vec<Rpn> {
        let mut out = vec![term.clone()];
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
    /// What the `proof` block `owner` opens owes, as the checker's record has
    /// it (`record::Block::owes`): its claim with what its openers take off
    /// it taken off. It is read with the names in force where it is asked,
    /// which are the block's own while the block is open.
    pub(crate) fn owed_goal(&mut self, owner: &Step) -> Checked<Rpn> {
        if let Some(by) = self.by_part_of(owner) {
            return self.owed_end(by, owner.line);
        }
        let owed = CheckedTheorem::index_of(self.thm, owner)
            .and_then(|i| self.checked.block_of(i))
            .and_then(|b| b.owes.first())
            .and_then(|o| o.claim.first())
            .cloned();
        let Some(node) = owed else {
            return Err(self.unreached(
                owner.line,
                "the checker's record says nothing this proof block owes",
            ));
        };
        self.term(&node)
    }

    /// The block a part's `by` line names, opened where the part has opened
    /// (`Step::by_lines`): `owner`, the step whose part it is, stands at
    /// `at` in the theorem. The block's owner stands in for that step, with
    /// the `by` method and the openers after the line, in the part.
    pub fn open_by_part(
        &mut self,
        owner: &Step,
        at: usize,
        by: &PartBy,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Block> {
        let openers = owner
            .opening(by.part)
            .inner
            .into_iter()
            .map(|o| Opener {
                part: None,
                after_by: false,
                ..o.clone()
            })
            .collect();
        let standing = Step {
            just: Justification {
                head: Head::Method(by.method),
                refs: Vec::new(),
                contradicting: None,
                ..owner.just.clone()
            },
            requires: Vec::new(),
            parts: Vec::new(),
            openers,
            line: by.line,
            part: by.part,
            note: None,
            part_notes: IndexMap::new(),
            by_lines: Vec::new(),
            impossible: false,
            ..owner.clone()
        };
        let mut block = self.open_block(&standing, scope, facts)?;
        block.by_part = Some(ByPart {
            owner: at,
            part: by.part,
        });
        Ok(block)
    }

    /// The part a block opened by a `by` line serves, where `owner` stands
    /// in for its step (`open_by_part`): the stand-in is at the `by` line,
    /// which no step of the theorem is.
    pub(super) fn by_part_of(&self, owner: &Step) -> Option<ByPart> {
        self.thm.steps.iter().enumerate().find_map(|(at, s)| {
            s.by_lines
                .iter()
                .find(|b| b.line == owner.line)
                .map(|b| ByPart {
                    owner: at,
                    part: b.part,
                })
        })
    }

    /// What the checker's record says part `by` of its block owes
    /// (`record::Owed`), or a fault at `line` where it says nothing.
    pub(super) fn owed_part(&self, by: ByPart, line: usize) -> Checked<record::Owed> {
        self.checked
            .block_of(by.owner)
            .and_then(|b| b.owes.iter().find(|o| o.part == by.part))
            .cloned()
            .ok_or_else(|| {
                self.unreached(line, "the checker's record says nothing this part owes")
            })
    }

    /// What the last step of a part proved `by proof` ends on: what the part
    /// owes with the block's openers taken off (`record::Owed::ends`).
    pub(super) fn owed_end(&mut self, by: ByPart, line: usize) -> Checked<Rpn> {
        let owed = self.owed_part(by, line)?;
        match owed.ends.first() {
            Some(node) => self.term(node),
            None => {
                Err(self.unreached(line, "a part proved by contradiction owes no end"))
            }
        }
    }

    /// What a block claims: its owner's claim as written, or for a block a
    /// part's `by` line opened, what the part owes.
    pub(crate) fn block_claim(&mut self, owner: &Step) -> Checked<Rpn> {
        match self.by_part_of(owner) {
            Some(by) => {
                let owed = self.owed_part(by, owner.line)?;
                match owed.claim.as_slice() {
                    [one] => self.term(one),
                    _ => {
                        Err(self
                            .unreached(owner.line, "a part owing several sentences"))
                    }
                }
            }
            None => self.claim_of(&owner.claim),
        }
    }

    /// What a `proof` block's claim says under each of its openers, outermost
    /// first: what the block gives back as it closes. What is left once each
    /// is taken off is what the block owes (`owed_goal`).
    pub(crate) fn opener_layers(
        &mut self,
        step: &Step,
        claim: &Rpn,
    ) -> Checked<Vec<OpenerLayer>> {
        let mut layers: Vec<OpenerLayer> = Vec::new();
        let mut rest = self.to_term(claim);
        for o in step.openers.iter().filter(|o| !o.after_by) {
            if o.kind == Intro::Let && rest.label() == Some("wral") {
                let kids = rest.children().to_vec();
                layers.push(OpenerLayer {
                    how: "ralrimiva",
                    what: self.rpn(&kids[1]),
                    over: Some(self.rpn(&kids[2])),
                });
                rest = kids[0].clone();
            } else if o.kind == Intro::Let && rest.label() == Some("wal") {
                // `let X be a set` fixes a name over nothing, so the claim
                // says its body of every set there is and `alrimiv` gives
                // that back.
                let kids = rest.children().to_vec();
                layers.push(OpenerLayer {
                    how: "alrimiv",
                    what: self.rpn(&kids[1]),
                    over: None,
                });
                rest = kids[0].clone();
            } else if o.kind == Intro::Assume && rest.label() == Some("wi") {
                let kids = rest.children().to_vec();
                layers.push(OpenerLayer {
                    how: "ex",
                    what: self.rpn(&kids[0]),
                    over: None,
                });
                rest = kids[1].clone();
            } else if o.kind == Intro::Let {
                return Err(self.unreached(
                    step.line,
                    "a proof block that claims nothing of every such name",
                ));
            } else {
                return Err(self.unreached(
                    step.line,
                    "a proof block whose claim supposes nothing where the block assumes",
                ));
            }
        }
        Ok(layers)
    }

    /// `owed` is what the block owes (`owed_goal`), which its last line is
    /// carried to before what each opener took off is given back.
    pub(super) fn close_proof_block(
        &mut self,
        block: &Block,
        held: &ProvedClaim,
        inside: &[Closer],
        owed: &Rpn,
    ) -> Checked<(Rpn, Proof)> {
        let step = &block.owner;
        // Read with the variables the block had, not the ones given back.
        let kept = std::mem::replace(&mut self.bound_as, block.inner.clone());
        let claim = self.block_claim(step);
        self.bound_as = kept;
        let claim = claim?;
        let layers = self.opener_layers(step, &claim)?;
        // The scope each layer was taken at, which is what it is given back
        // to. An assumption widened the scope as the block writes it, which
        // may be the claim's supposition said another way, `g(t) = g(s)`
        // for `g(s) = g(t)`; its steps were proved under that.
        let mut scopes = Vec::new();
        let mut scope = block.outer.clone();
        for (i, OpenerLayer { how, what, over }) in layers.iter().enumerate() {
            scopes.push(scope.clone());
            scope = if *how == "ex" {
                t!(scope, block.opened.get(i).unwrap_or(what), "wa")
            } else {
                t!(
                    scope,
                    t!(
                        what,
                        "cv",
                        over.clone().unwrap_or_else(|| t!("cvv")),
                        "wcel"
                    ),
                    "wa"
                )
            };
        }
        // An `obtain` inside the block widened the scope past what the
        // openers widened it to, and discharges where the block does.
        let mut proof = held.proof.clone();
        let said = held.claim.clone();
        for close in inside.iter().rev() {
            proof = self.close(close, proof, &said)?;
        }
        // The last line and the claim are written in different places, so a
        // name bound in both may be spelt two ways. A block a part's `by`
        // line opened claims what its last line says where that is what the
        // part owes said another way, L(p) for L(p + 0): the part's close
        // carries it there, as it carries a step's claim (`close_induction`,
        // `direction_reached`).
        let want = owed.clone();
        let (mut proof, mut said, as_said) =
            match self.respelt(&proof, &said, &want, &scope)? {
                Some(proof) => (proof, want, false),
                None if block.by_part.is_some() => (proof, said, true),
                None => {
                    return Err(self.defect(
                        step.line,
                        "the block does not reach what it claims of the name it fixed",
                    ))
                }
            };
        for (i, (OpenerLayer { how, what, over }, outer)) in
            layers.iter().zip(scopes.iter()).enumerate().rev()
        {
            match *how {
                "ex" => {
                    // Given back as written, and then as the claim supposes
                    // it, where the two are one claim said two ways.
                    let written = block.opened.get(i).unwrap_or(what);
                    proof = pf!(self.b; outer, written, said, proof, "ex");
                    if written != what {
                        let Built(alike) = self.same(
                            &self.to_term(what),
                            &self.to_term(written),
                            outer,
                            &block.outside,
                            Some(step),
                        )?
                        else {
                            return Err(self.defect(
                                step.line,
                                "the block assumes other than what its claim supposes",
                            ));
                        };
                        proof = pf!(self.b; outer, what, written, said, alike, proof, "sylbid");
                    }
                    said = t!(what, said, "wi");
                }
                "alrimiv" => {
                    // `let X be a set` says X ∈ _V and the claim quantifies
                    // X over nothing, so that membership is dropped before
                    // the name is given back: every setvar is a set.
                    let member = t!(what, "cv", "cvv", "wcel");
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
        if as_said {
            return Ok((said, proof));
        }
        Ok((claim, proof))
    }

    /// The cases and the disjunction that says one of them holds: `jaodan`
    /// makes one case of the first two over their disjunction, and so on
    /// down, and `mpjaodan` closes on the last.
    /// "A ↔ B" from its two directions, each a case over its assumption:
    /// the first gives ( ( scope ∧ A ) → B ), the second ( ( scope ∧ B ) →
    /// A ), and `impbida` joins them.
    pub(super) fn close_both(&mut self, block: &Block) -> Checked<(Rpn, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let both = [0usize, 1];
        if !both
            .iter()
            .all(|p| block.parts.contains_key(p) && block.assumed.contains_key(p))
        {
            return Err(
                self.unreached(step.line, "a direction of the block proves nothing")
            );
        }
        let claim = self.claim_of(&step.claim)?;
        let left = self.term(&block.assumed[&0].0)?;
        let right = self.term(&block.assumed[&1].0)?;
        // Each direction ends on the side it does not assume as the text
        // writes it, which may rename a bound letter: a part ending on a
        // proof block fixing t says the side over the block's own t.
        let allowed = Some(self.named(step, &number_of(step), true));
        let forward = self.resting_on(allowed.clone(), |me| {
            me.direction_reached(&block.parts[&0], &right)
        })?;
        let backward = self
            .resting_on(allowed, |me| me.direction_reached(&block.parts[&1], &left))?;
        let (Some(forward), Some(backward)) = (forward, backward) else {
            return Err(self.unreached(
                step.line,
                "a direction does not end on the side it does not assume",
            ));
        };
        let joined = t!(left, right, "wb");
        let mut proof = self.b.ap(
            "impbida",
            &binds! {"ph" => scope, "ps" => &left, "ch" => &right},
            &[&forward, &backward],
        );
        if claim != joined {
            // The sides assumed as the claim writes them, or another way,
            // `c² = a² + b²` for `a² + b² = c²`.
            let alike = self.same(
                &self.to_term(&joined),
                &self.to_term(&claim),
                scope,
                &block.outside,
                Some(step),
            )?;
            let Built(alike) = alike else {
                return Err(self.defect(
                    step.line,
                    "the directions do not assume the two sides of the claim, in order",
                ));
            };
            proof = pf!(self.b; scope, joined, claim, proof, alike, "mpbid");
        }
        Ok((claim, proof))
    }

    /// The proof a part ends on, of what `want` says: a direction's side it
    /// does not assume, or a case's claim. Its own where it says `want` as
    /// written, and otherwise carried there (`reached`); None where it says
    /// something else.
    pub fn direction_reached(
        &mut self,
        end: &PartEnd,
        want: &Rpn,
    ) -> Checked<Option<Proof>> {
        if end.claim == *want {
            return Ok(Some(end.proof.clone()));
        }
        let facts = self.in_hand(&end.facts);
        self.reached(&end.proof, &end.claim, want, &end.scope, &facts)
    }

    pub(super) fn close_cases(&mut self, block: &Block) -> Checked<(Rpn, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        let parts: std::collections::BTreeSet<usize> =
            block.parts.keys().copied().collect();
        let assumed_parts: std::collections::BTreeSet<usize> =
            block.assumed.keys().copied().collect();
        if parts != assumed_parts {
            return Err(self.unreached(step.line, "a case of the block proves nothing"));
        }
        let claim = self.claim_of(&step.claim)?;
        let order: Vec<usize> = assumed_parts.into_iter().collect();
        let mut assumed = Vec::new();
        for p in &order {
            let node = block.assumed[p].0.clone();
            assumed.push(self.term(&node)?);
        }
        // A case may end on the claim written another way, `x ≠ y` for
        // `y ≠ x`, as the checker reads it; it is carried to the claim.
        let mut said: Vec<Proof> = Vec::new();
        for p in &order {
            let Some(shown) = self.direction_reached(&block.parts[p], &claim)? else {
                return Err(self
                    .unreached(step.line, "a case does not end on the block's claim"));
            };
            said.push(shown);
        }
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
        // The line split is the first the step cites that is not a define;
        // a define cited beside it reads its name, as the checker takes it.
        let cited = step
            .just
            .refs
            .iter()
            .find(|r| !self.thm.defines.iter().any(|d| d.label == **r))
            .unwrap_or(&step.just.refs[0])
            .clone();
        let mut disjunction = self.carried(&cited, &block.outside, &self.lines.clone());
        let cited_term = self
            .line_written(&cited, &self.lines)
            .map(|l| l.claim)
            .unwrap_or_default();
        let wanted = t!(which, assumed[last], "wo");
        // Inside a block, a "for all" line is the disjunction read at the
        // block's letter (`line_says`), as the checker takes it.
        let lines = self.lines.clone();
        let read_at = self.line_says(&cited, scope, &block.outside, &lines)?;
        let at_letter = read_at
            .entries()
            .into_iter()
            .find(|(said, _)| *said == wanted);
        if let Some((_, proof)) = at_letter {
            disjunction = proof;
        } else if wanted != cited_term {
            // A case may write its disjunct another way, `0 = b(k)` for
            // `b(k) = 0`; the line is carried across to the cases' spelling.
            let alike = self.same(
                &self.to_term(&cited_term),
                &self.to_term(&wanted),
                scope,
                &block.outside,
                Some(step),
            )?;
            let Built(alike) = alike else {
                return Err(self.defect(
                    step.line,
                    "the cases are not the disjunction the block cites, taken in order",
                ));
            };
            disjunction =
                pf!(self.b; scope, cited_term, wanted, disjunction, alike, "mpbid");
        }
        let proof = self.b.ap(
            "mpjaodan",
            &binds! {"ph" => scope, "ps" => &which, "ch" => &claim, "th" => &assumed[last]},
            &[&proof, &said[last], &disjunction],
        );
        Ok((claim, proof))
    }

    /// Induction closes with the lemma for the set it runs over. It wants the
    /// claim's statement five ways and the text writes three of them, so the
    /// statement is read as a function of the letter and instantiated, and
    /// each instance is tied to the general one by congruence.
    ///
    /// The claim is "for all k ∈ X, P(k)". The base part ends on P at the
    /// start; the step part fixes k, assumes P(k) and ends on P(k + 1), which
    /// is the lemma's step as it asks it, `((ph ∧ k ∈ X) ∧ P(k)) → P(k + 1)`.
    /// The lemma is applied at the step part's k, and `ralrimiva` says it of
    /// every k.
    pub(super) fn close_induction(&mut self, block: &Block) -> Checked<(Rpn, Proof)> {
        let step = &block.owner;
        let scope = &block.outer;
        // A base part and a step part, as the checker holds.
        let PartEnd {
            claim: base_claim,
            proof: base,
            scope: beneath,
            facts: outside,
        } = block
            .parts
            .get(&0)
            .expect("an induction's base part")
            .clone();
        let PartEnd {
            claim: step_claim,
            proof: stepped,
            scope: under,
            facts: inside,
        } = block
            .parts
            .get(&1)
            .expect("an induction's step part")
            .clone();
        let name = block.over.clone().unwrap_or_default();
        let general = t!(block.base.clone().unwrap_or_default(), "cv");
        let Some(variable) = block.variable.clone() else {
            return Err(self.unreached(
                step.line,
                format!("the step part of the induction does not fix {name}"),
            ));
        };
        let claim = self.claim_of(&step.claim)?;
        let over = self.rpn(&self.to_term(&claim).children()[2]);
        // Over the parts of a set X, `gfinind` closes it from ∅ and Y ∪ {a};
        // over numbers, the set's lemma from its first element and k + 1.
        let parent = self.parts_over(&over);
        let (lemma, start, next_one) = match (&parent, &block.added) {
            (Some(_), Some(added)) => (
                "gfinind",
                t!("c0"),
                t!(variable, "cv", added, "cv", "csn", "cun"),
            ),
            (Some(_), None) => {
                return Err(self.unreached(
                    step.line,
                    "the step part of the induction adds no member",
                ));
            }
            (None, _) => {
                let Some((lemma, begins)) =
                    lookup(rules::INDUCTION, over.alone().unwrap_or_default())
                else {
                    return Err(self.unreached(
                        step.line,
                        format!("nothing here inducts over {}", self.render(&over)),
                    ));
                };
                // The start the page writes is the set's first element, as
                // the checker holds (`check_induction_runs`).
                (lemma, t!(begins), t!(variable, "cv", "c1", "caddc", "co"))
            }
        };
        let written = step.claim.clone();
        // The statement after "for all k ∈ X,", with k the general name.
        let pattern = self.names_kept(|me| -> Checked<crate::formula::Node> {
            me.names.insert(name.clone(), general.clone());
            let node = me.claim_node(&written)?;
            me.freeze(&node.children[2])
        })?;
        // The lemma is applied at the claim's own letter, which `nn0indd`
        // keeps apart only from its x, and `ralrimiva` then gives the claim as
        // written. The step part's letter is the lemma's y.
        // A hypothesis binding the claim's letter, "for all m ∈ ℕ₀, m ≥ 0",
        // keeps it out of `ralrimiva`'s reach, so the claim is proved over a
        // letter of its own and read back as written.
        let written_bound = self.rpn(&self.to_term(&claim).children()[1]);
        let apart = if written_bound.alone().is_some_and(|b| scope.has(b)) {
            let whole_claim = self.to_term(&claim);
            let Some(letter) = self.unheld(&[&self.to_term(scope), &whole_claim])
            else {
                return Err(self.defect(
                    step.line,
                    "no letter left to prove the induction's claim apart from what the theorem assumes",
                ));
            };
            let var = self
                .sig(written_bound.alone().unwrap_or_default())
                .statement[1];
            let moved = Binding::from([(var, letter)]);
            Some(self.rpn(&whole_claim.substitute(&moved)))
        } else {
            None
        };
        let target = apart.clone().unwrap_or_else(|| claim.clone());
        let bound = self.rpn(&self.to_term(&target).children()[1]);
        if bound.alone().is_some_and(|b| scope.has(b)) {
            return Err(self.defect(
                step.line,
                format!(
                    "the induction's letter {name} is used in what the theorem assumes"
                ),
            ));
        }
        let named = t!(bound, "cv");
        let shapes = [start.clone(), t!(variable, "cv"), next_one, named.clone()];
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
        let body = self.term(&pattern)?;
        // The step part's scope is the block's with k ∈ X and the induction
        // hypothesis conjoined, in that order, which is the antecedent the
        // lemma asks its step under.
        // Over the parts of X it ends with the member added, a ∈ X ∖ Y.
        let member = t!(variable, "cv", over, "wcel");
        let mut asked = t!(t!(scope, member, "wa"), held, "wa");
        if let (Some(parent), Some(added)) = (&parent, &block.added) {
            let outside = t!(added, "cv", parent, variable, "cv", "cdif", "wcel");
            asked = t!(asked, outside, "wa");
        }
        if under != asked {
            return Err(self.unreached(
                step.line,
                "the step part does not assume the claim's statement at its letter",
            ));
        }
        // Each part ends on its instance as the text writes it, which may
        // rename a bound letter or leave out an identity element (`SYNTAX.md`).
        // What an identity element asks, x ∈ ℂ, is answered from what the
        // induction's own lines name and nothing else in scope.
        let allowed = Some(self.named(step, &number_of(step), true));
        let base = self.resting_on(allowed.clone(), |me| {
            let outside = me.in_hand(&outside);
            me.reached(&base, &base_claim, &claimed, &beneath, &outside)
        })?;
        let stepped = self.resting_on(allowed, |me| {
            let inside = me.in_hand(&inside);
            me.reached(&stepped, &step_claim, &reached, &under, &inside)
        })?;
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
        // `( ( scope ∧ k ∈ X ) → P(k) )`, and so P of every k in X.
        let run = match (&parent, &block.added) {
            (Some(parent), Some(added)) => {
                let finite = t!(parent, "cfn", "wcel");
                let known = self.supplied(Some(step), scope, &block.outside)?;
                let Some(finite) = self.held(&known, &finite, scope)? else {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "nothing the induction's requires lines say gives {}",
                            self.render(&finite)
                        ),
                    ));
                };
                let x = t!(block.base.clone().unwrap_or_default());
                self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "ps" => &body, "ch" => &claimed,
                    "th" => &held, "ta" => &reached, "et" => &whole, "x" => &x,
                    "y" => &t!(variable), "z" => &t!(added), "w" => &bound,
                    "A" => parent},
                    &[
                        &ties[0], &ties[1], &ties[2], &ties[3], &base, &stepped,
                        &finite,
                    ],
                )
            }
            _ => {
                let mut all: Vec<crate::mm::spell::Part> = Vec::new();
                let pieces = [
                    scope.clone(),
                    body,
                    claimed,
                    held,
                    reached,
                    whole.clone(),
                    t!(block.base.clone().unwrap_or_default()),
                    t!(variable),
                    named,
                ];
                all.extend(pieces.iter().map(|p| crate::elab::part(p)));
                all.extend(ties.iter().map(|p| crate::elab::part(p)));
                all.push(crate::elab::part(&base));
                all.push(crate::elab::part(&stepped));
                all.push(crate::elab::part(lemma));
                self.b.proof(&all)
            }
        };
        let every = t!(whole, bound, over, "wral");
        if every != target {
            return Err(self.defect(
                step.line,
                "the induction does not reach its claim over the claim's letter",
            ));
        }
        let proved = pf!(self.b; scope, whole, bound, over, run, "ralrimiva");
        let Some(apart) = apart else {
            return Ok((claim, proved));
        };
        let Some(back) = self.renaming(&self.to_term(&apart), &self.to_term(&claim))?
        else {
            return Err(self.defect(
                step.line,
                "the claim proved apart does not read back as the claim",
            ));
        };
        let carried = self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &apart, "ch" => &claim},
            &[&proved, &back],
        );
        Ok((claim, carried))
    }
}
