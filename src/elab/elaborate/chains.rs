//! Calculations, chains and congruences.

use std::mem;

use super::*;

impl<'a> Elaborator<'a> {
    /// Use the lemma of the sentence the checker read the citation as
    /// taking (`cited_labels`), the way `way` says; a defect the way found
    /// on its own account is not the lemma declining, and goes past.
    #[allow(clippy::too_many_arguments)]
    pub fn trying(
        &mut self,
        item: Item<'a>,
        step: &Step,
        way: Way,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let mut declines = Vec::new();
        let lemmas = match item {
            Item::Record(r) => self.cited_labels(step, r)?,
            Item::Theorem(_) => Vec::new(),
        };
        for lemma in lemmas {
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
            return Ok(Route::no(format!(
                "{} has no metamath-proof",
                qualified(item)
            )));
        }
        Ok(Route::no(declines.join("; ")))
    }

    /// Which of four ways a biconditional definition reaches a claim: the
    /// way the checker read the citation (`Concluded::way`), with the whole
    /// biconditional claimed as it stands, its right side stated first
    /// unfolded from it and its left side stated first read back to it. A
    /// lemma that is no biconditional is applied as it
    /// stands, and a left side whose right side is a "there is" no line the
    /// step cites says is shown from a witness.
    pub fn reading(&mut self, item: &'a Record, step: &Step) -> Checked<Way> {
        let Some(lemma) = self.cited_labels(step, item)?.into_iter().next() else {
            return Ok(Way::Conclude);
        };
        let mut whole = self.statement(&lemma);
        while whole.label() == Some("wi") {
            whole = whole.children()[1].clone();
        }
        if whole.label() != Some("wb") {
            return Ok(Way::Conclude);
        }
        let cited = self.cited_here(step, &item.qualified())?;
        let ways: BTreeSet<citing::Way> =
            cited.concluded.iter().map(|c| c.way).collect();
        let way = match ways.into_iter().collect::<Vec<_>>().as_slice() {
            [one] => *one,
            _ => {
                return Err(self.defect(
                    step.line,
                    format!(
                        "the checker reads the sentences {} concludes here more than one way, and one lemma is applied one way",
                        item.qualified()
                    ),
                ))
            }
        };
        Ok(match way {
            citing::Way::AsWritten => Way::AsStated,
            citing::Way::Forward => Way::Unfolded,
            citing::Way::Backward => {
                let there_is = whole.children()[1].label() == Some("wrex");
                let said = step.just.refs.iter().any(|r| {
                    self.line_written(r, &self.lines)
                        .is_some_and(|l| self.to_term(&l.claim).label() == Some("wrex"))
                });
                if there_is && !said {
                    Way::Conclude
                } else {
                    Way::Equivalent
                }
            }
        })
    }

    /// A definition with no target, read off a line the step cites that
    /// already says what the step claims, as `same` reads two claims: whole
    /// or as one of its conjuncts, taken apart to the depth of a congruence's
    /// six; over other bound letters; or with a defined name it writes read as
    /// what it names, where the step cites the define. Nothing builds it
    /// otherwise, and nothing is taken as stated.
    pub(super) fn take_definition(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let supplied = self.supplied(Some(step), scope, facts)?;
        let held = self.with_cited(Some(step), scope, &supplied, None)?;
        let want = self.to_term(term);
        for r in &step.just.refs {
            let parts = self.line_supplies(r, scope, facts, lines)?;
            for (said, proof) in parts.entries() {
                // A part that is the claim leaves `same` nothing to carry.
                if said == *term {
                    return Ok(Built(proof));
                }
                let across =
                    self.same(&self.to_term(&said), &want, scope, &held, Some(step))?;
                if let Built(across) = across {
                    return Ok(Built(
                        pf!(self.b; scope, said, term, proof, across, "mpbid"),
                    ));
                }
                // Or the claim with its identity elements dropped, as the
                // checker reads it: a ≡ 0 (mod 4) is 4 ∥ (a − 0) in the
                // kernel, and the step says 4 divides a.
                if let Some(tidy) = self.tidied(&proof, &said, term, scope, &held)? {
                    return Ok(Built(tidy));
                }
            }
        }
        let Item::Record(item) = self.item_cited(&step.just.head.to_string())? else {
            panic!("a definition of the database");
        };
        Err(self.defect(
            step.line,
            format!(
                "{}:{} has no metamath-proof, and nothing step {} cites says {}",
                item_kind(Item::Record(item)),
                item.qualified(),
                step.number,
                self.render(term)
            ),
        ))
    }

    /// A definition stated as an equation, one clause per `then` group: the
    /// clause is chosen by which lemma's conclusion is what the step claims.
    /// None reaching it is a defect, since the database named these lemmas.
    pub(super) fn unfold_equation(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let head = step.just.head.to_string();
        let Item::Record(item) = self.item_cited(&head)? else {
            panic!("a definition of the database");
        };
        let labels: Vec<String> =
            targets::lemma_entries(item.metamath_target_or_empty())
                .into_iter()
                .map(String::from)
                .collect();
        let seed = self.filling(step, item)?;
        match self
            .by_clause_or_instance(item, &labels, term, scope, facts, step, &seed)?
        {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "no clause of {head} gives what step {} claims: {}",
                    step.number,
                    self.say(&d)
                ),
            )),
        }
    }

    /// Each hypothesis line read again once the names its statement wrote
    /// out are in scope. The statement says `x ∈ {1, 2}` where the page
    /// writes `let x ∈ B` for a define B, and the steps say it with the name,
    /// so a step citing the line is given it as the steps read it: the two
    /// readings are joined by `same`, as the last line and the conclusion
    /// are. A line the two read alike is left as it is.
    pub(super) fn hypotheses_named(
        &mut self,
        hypotheses: &[Hypothesis],
        nodes: &[Node],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        for (h, node) in hypotheses.iter().zip(nodes) {
            let Some(label) = h.label.clone().filter(|l| !l.is_empty()) else {
                continue;
            };
            let (Some(line), Some(written)) = (
                self.lines.get(&label),
                self.line_written(&label, &self.lines),
            ) else {
                continue;
            };
            let named = self.term(node)?;
            if named == written.claim {
                continue;
            }
            let Some(held) = self.held(facts, &written.claim, scope)? else {
                continue;
            };
            let alike = self.same(
                &self.to_term(&written.claim),
                &self.to_term(&named),
                scope,
                facts,
                None,
            )?;
            let Built(alike) = alike else {
                continue;
            };
            let proof = pf!(self.b; scope, written.claim, named, held, alike, "mpbid");
            let proof = self.seal(proof, &label);
            self.know(facts, named.clone(), proof.clone());
            self.lines.set(label, line.restated(named, proof));
        }
        Ok(())
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

    /// A proof of `B = A` from one of `A = B`.
    pub(super) fn turned_equation(
        &mut self,
        scope: &Rpn,
        a: &Rpn,
        b: &Rpn,
        proof: &Proof,
    ) -> Proof {
        self.b.ap(
            "eqcomd",
            &binds! {"ph" => scope, "A" => a, "B" => b},
            &[proof],
        )
    }

    /// A chain (`METHODS.md`, transitivity), folded a line at a time by the
    /// lemmas a calculation's links fold by (`rules::folding`,
    /// `rules::order_folding`), so that the proof rests on every line the
    /// step cites. An order is held low side first, `_ > _` as `_ < _`
    /// turned, so a link going down is the same link going up, and a chain
    /// going down is its links going up taken from the last. An equation
    /// meets its neighbours from either side and is turned by `eqcomd` where
    /// it meets them from the other; what is reached is carried to the claim
    /// as the page writes it by `same`, as any method's claim is.
    pub(super) fn transitivity_chain(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Proof> {
        let mut links = Vec::new();
        let chosen = self
            .checked
            .links
            .get(&step.just.line)
            .map(|chain| chain.links.clone())
            .unwrap_or_default();
        for (i, r) in step.just.refs.iter().enumerate() {
            let held = self
                .line_written(r, lines)
                .expect("a line the checker found in scope");
            let carried = self.carried(r, facts, lines);
            // The relation the checker read the line as giving the chain:
            // the line's own, or one of several it says.
            let (link, proof) = match chosen.get(i) {
                Some(link) => {
                    let part = self.term(&link.said)?;
                    let define = self.thm.defines.iter().any(|d| d.label == *r);
                    if part == held.claim {
                        (part, carried)
                    } else if define {
                        // A define in the chain is the equation it makes
                        // between its neighbours, as a link citing it reads.
                        let Built(proof) = self.define_makes(
                            step,
                            &part,
                            link.define_facing,
                            scope,
                            facts,
                        )?
                        else {
                            return Err(self.defect(
                                step.line,
                                format!(
                                    "{} is not what {r} makes it",
                                    self.render(&part)
                                ),
                            ));
                        };
                        (part, proof)
                    } else {
                        let apart =
                            facts.with(&self.line_says(r, scope, facts, lines)?);
                        let Some(proof) = self.held(&apart, &part, scope)? else {
                            return Err(self.defect(
                                step.line,
                                format!(
                                    "{r} says {}, which the build does not take out of it",
                                    self.render(&part)
                                ),
                            ));
                        };
                        (part, proof)
                    }
                }
                None => (held.claim.clone(), carried),
            };
            let said = self.to_term(&link);
            let kids = said.children();
            let relation = match said.label() {
                Some("wceq") => None,
                _ => Some(self.rpn(&kids[2]).to_string()),
            };
            links.push(ChainRun {
                left: self.rpn(&kids[0]),
                right: self.rpn(&kids[1]),
                relation,
                proof,
            });
        }
        // A term a join asks to be real is settled from the step's requires
        // lines, offered to the membership lookup, as for an inequalities
        // step.
        let known = self.supplied(Some(step), scope, facts)?;
        let up = self.writing(scope, &known, false, |me| {
            me.folded_up(step, scope, &known, lines, links.clone())
        })?;
        // The chain goes the way that starts from the claim's low side: an
        // order claim's ends may be one term, ∠A > ∠A from ∠A > 90° and
        // 90° > ∠A, which the links folded up from 90° would reach as
        // 90° < 90°.
        let run = match up {
            Some(run) if self.starts_low(&run, term) => run,
            up => {
                links.reverse();
                let down = self.writing(scope, &known, false, |me| {
                    me.folded_up(step, scope, &known, lines, links)
                })?;
                // Folded up, the chain may start from a term the claim writes
                // with an identity element left out, n·1 for n, which is
                // carried to the claim below; folded down it is taken only
                // where it starts at the claim's low side as written.
                match (down, up) {
                    (Some(run), _) if self.starts_low(&run, term) => run,
                    (_, Some(run)) => run,
                    (Some(run), None) => run,
                    (None, None) => {
                        return Err(self.defect(
                            step.line,
                            "the lines the step chains do not meet",
                        ))
                    }
                }
            }
        };
        let reached = match &run.relation {
            None => t!(&run.left, &run.right, "wceq"),
            Some(r) => t!(&run.left, &run.right, r, "wbr"),
        };
        if reached == *term {
            return Ok(run.proof);
        }
        if run.relation.is_none() && t!(&run.right, &run.left, "wceq") == *term {
            return Ok(self.turned_equation(scope, &run.left, &run.right, &run.proof));
        }
        // An identity element goes without saying (`SYNTAX.md`): n·1 ≤ n² is
        // the claim n ≤ n².
        if let Some(tidy) = self.tidied(&run.proof, &reached, term, scope, facts)? {
            return Ok(tidy);
        }
        // An equation is the claim either way round, the identity dropped
        // from the side the claim writes it on.
        if run.relation.is_none() {
            let turned = self.turned_equation(scope, &run.left, &run.right, &run.proof);
            let reached_turned = t!(&run.right, &run.left, "wceq");
            if let Some(tidy) =
                self.tidied(&turned, &reached_turned, term, scope, facts)?
            {
                return Ok(tidy);
            }
        }
        let alike = match self.same(
            &self.to_term(&reached),
            &self.to_term(term),
            scope,
            facts,
            Some(step),
        )? {
            Built(p) => p,
            Declined(d) => {
                return Err(self.defect(
                    step.line,
                    format!(
                        "the chain reaches {}, which is not the claim: {}",
                        self.render(&reached),
                        self.say(&d)
                    ),
                ))
            }
        };
        Ok(pf!(self.b; scope, reached, term, run.proof, alike, "mpbid"))
    }

    /// Whether a folded chain starts where the claim `term` does: an order's
    /// low side, held first; any equation, which is turned to the claim.
    pub(super) fn starts_low(&self, run: &ChainRun, term: &Rpn) -> bool {
        let claim = self.to_term(term);
        match (claim.label(), claim.children()) {
            (Some("wbr"), [low, ..]) => self.rpn(low) == run.left,
            _ => true,
        }
    }

    /// The links of a chain folded in the order given, each going up from
    /// where the one before ends; None where one does not begin there.
    pub(super) fn folded_up(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        links: Vec<ChainRun>,
    ) -> Checked<Option<ChainRun>> {
        let mut links = links.into_iter();
        let Some(mut run) = links.next() else {
            return Ok(None);
        };
        for mut link in links {
            // A middle term the checker reads as one and the page writes two
            // ways, |AB| and |BA|, is joined by the equation proving them one,
            // folded in as a link of its own.
            if let Some(bridge) =
                self.middle_joined(step, scope, facts, &mut run, &mut link)?
            {
                let Some(joined) =
                    self.folded_link(step, scope, facts, lines, run, bridge)?
                else {
                    return Ok(None);
                };
                run = joined;
            }
            let meets = |t: &Rpn| *t == link.left || *t == link.right;
            if run.relation.is_none() && !meets(&run.right) && meets(&run.left) {
                run.proof =
                    self.turned_equation(scope, &run.left, &run.right, &run.proof);
                mem::swap(&mut run.left, &mut run.right);
            }
            if link.relation.is_none()
                && link.left != run.right
                && link.right == run.right
            {
                link.proof =
                    self.turned_equation(scope, &link.left, &link.right, &link.proof);
                mem::swap(&mut link.left, &mut link.right);
            }
            if link.left != run.right {
                return Ok(None);
            }
            let Some(joined) =
                self.folded_link(step, scope, facts, lines, run, link)?
            else {
                return Ok(None);
            };
            run = joined;
        }
        Ok(Some(run))
    }

    /// Where no end of `link` is written as an end of `run` is, the
    /// equation between one end of each that the checker reads as one term
    /// (`alike`), each turned so that the equation goes from where `run`
    /// ends to where `link` begins; an order is not turned. None where an end
    /// is written alike, or no two ends read as one.
    pub(super) fn middle_joined(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        run: &mut ChainRun,
        link: &mut ChainRun,
    ) -> Checked<Option<ChainRun>> {
        let ends_run = [&run.left, &run.right];
        if ends_run
            .iter()
            .any(|e| **e == link.left || **e == link.right)
        {
            return Ok(None);
        }
        let run_turns = run.relation.is_none();
        let link_turns = link.relation.is_none();
        let pairs = [(false, false), (false, true), (true, false), (true, true)];
        for (turn_run, turn_link) in pairs {
            if (turn_run && !run_turns) || (turn_link && !link_turns) {
                continue;
            }
            let from = if turn_run { &run.left } else { &run.right };
            let to = if turn_link { &link.right } else { &link.left };
            let (from_term, to_term) = (self.to_term(from), self.to_term(to));
            let Built(proof) =
                self.alike(&from_term, &to_term, scope, facts, Some(step))?
            else {
                continue;
            };
            let bridge = ChainRun {
                left: from.clone(),
                right: to.clone(),
                relation: None,
                proof,
            };
            if turn_run {
                run.proof =
                    self.turned_equation(scope, &run.left, &run.right, &run.proof);
                mem::swap(&mut run.left, &mut run.right);
            }
            if turn_link {
                link.proof =
                    self.turned_equation(scope, &link.left, &link.right, &link.proof);
                mem::swap(&mut link.left, &mut link.right);
            }
            return Ok(Some(bridge));
        }
        Ok(None)
    }

    /// `run` and then `link`, which begins where `run` ends, folded into one
    /// by the lemma for their two relations; None where no lemma folds them.
    pub(super) fn folded_link(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        run: ChainRun,
        link: ChainRun,
    ) -> Checked<Option<ChainRun>> {
        {
            let (left, right, nxt) = (&run.left, &run.right, &link.right);
            let (proof, relation) = match (&run.relation, &link.relation) {
                (None, None) => (
                    self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => left, "B" => right, "C" => nxt},
                        &[&run.proof, &link.proof],
                    ),
                    None,
                ),
                (Some(above), Some(below)) => {
                    let Some(fold) = rules::order_folding(above, below) else {
                        return Ok(None);
                    };
                    // Each of the three terms is real, which the page says
                    // once or not at all (`READERS.md`), and is settled as
                    // any other membership a step needs.
                    let mut real = Vec::new();
                    for t in [left, right, nxt] {
                        let wanted = self.to_term(&t!(t, "cr", "wcel"));
                        match self.settle(&wanted, scope, facts, 3, Some(step), Some(lines))? {
                            Built(p) => real.push(p),
                            Declined(d) => {
                                return Err(self.defect(
                                    step.line,
                                    format!(
                                        "step {} chains {}, and nothing it writes or cites says it is a number: {}",
                                        step.number,
                                        self.render(t),
                                        self.say(&d)
                                    ),
                                ))
                            }
                        }
                    }
                    let lemma = fold.lemma;
                    (
                        pf!(self.b; scope, left, right, nxt,
                            real[0], real[1], real[2], run.proof, link.proof, lemma),
                        Some(fold.folded.to_string()),
                    )
                }
                (above, below) => {
                    let (first, second) = (
                        if above.is_some() { "wbr" } else { "wceq" },
                        if below.is_some() { "wbr" } else { "wceq" },
                    );
                    let fold = rules::folding(first, second).expect(
                        "an equation folds into an order and an order into an equation",
                    );
                    let relation = above.clone().or(below.clone());
                    let r = relation.clone().expect("one of the two is an order");
                    (
                        pf!(self.b; scope, left, right, nxt, r, run.proof, link.proof, fold),
                        relation,
                    )
                }
            };
            Ok(Some(ChainRun {
                left: run.left,
                right: link.right,
                relation,
                proof,
            }))
        }
    }

    /// ( scope -> left e. RR* ) and ( scope -> right e. RR* ), from the
    /// proof that the link relates them: an order relates only extended
    /// reals (`rules::ORDER_FIELD`, `brel`).
    pub(super) fn extended_ends(
        &mut self,
        scope: &Rpn,
        link: &OrderLink,
    ) -> (Proof, Proof) {
        let field = lookup(rules::ORDER_FIELD, link.relation)
            .expect("a chain folds only the orders `rules::ORDER_FOLDING` lists");
        let (a, b) = (link.left, link.right);
        let (a_in, b_in) = (t!(a, "cxr", "wcel"), t!(b, "cxr", "wcel"));
        let both = t!(a_in, b_in, "wa");
        let within = self.b.ap(field, &binds! {}, &[]);
        let ends = self.b.ap(
            "brel",
            &binds! {"A" => a, "B" => b, "R" => link.relation, "C" => "cxr", "D" => "cxr"},
            &[&within],
        );
        let pair = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(a, b, link.relation, "wbr"), "ch" => &both},
            &[link.proof, &ends],
        );
        let parts = binds! {"ph" => scope, "ps" => &a_in, "ch" => &b_in};
        (
            self.b.ap("simpld", &parts, &[&pair]),
            self.b.ap("simprd", &parts, &[&pair]),
        )
    }

    pub(super) fn calculation(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let Some(chain) = chain(&step.just, &self.thm.path) else {
            return Err(self.unreached(step.line, "a calculation writes no chain"));
        };
        // A chain going down is composed as the same links going up, which
        // concludes the same formula: t₀ ≥ t₂ is t₂ ≤ t₀ (`Chain::upward`).
        let chain = chain?;
        let falling = chain.falls();
        let chain = chain.upward();
        let mut defines: BTreeSet<String> =
            self.thm.defines.iter().map(|d| d.label.clone()).collect();
        for v in self.visible_outside() {
            defines.insert(self.outside_label(&v.name, &v.define, v.scope));
        }
        // What a line claims: the term before it, its relation, the term it
        // reaches and the modulus it says, as one formula; and the term it
        // reaches, which the next line goes on from.
        let link =
            |me: &Self, from: &Node, line: &ChainLine| -> Checked<(Node, Node)> {
                let to = me.read_one(&line.term)?;
                let modulus = match &line.modulus {
                    Some(n) => Some(me.read_one(n)?),
                    None => None,
                };
                let at = (line.term.path(), line.line);
                let (g, sorts) = (me.g, &me.sorts_now);
                let claim =
                    related(g, sorts, &line.relation, from, &to, modulus.as_ref(), at)?;
                Ok((claim, to))
            };
        let start = self.read_one(&chain.start)?;
        let (first, mut rest) = link(self, &start, &chain.lines[0])?;
        let first_term = self.term(&first)?;
        let whole = self.to_term(&first_term);
        // A congruence joins the two terms whose difference its modulus
        // divides, and the chain goes on from the second.
        let mut modulus: Option<Rpn> = None;
        let mut equated: Option<Equated> = None;
        let (left, mut right) = match self.congruence_sides(&whole) {
            Some(Congruence {
                modulus: n,
                left,
                right,
            }) => {
                modulus = Some(n);
                (left, right)
            }
            None => (
                self.rpn(&whole.children()[0]),
                self.rpn(&whole.children()[1]),
            ),
        };
        let Some(mut said) = whole.label().map(str::to_string) else {
            return Ok(Route::no("the claim is a letter, not a relation"));
        };
        let mut reached = first_term.clone();
        let mut relation = if said == "wbr" {
            self.rpn(&whole.children()[2]).to_string()
        } else {
            String::new()
        };
        let mut proof = self.link_held(
            step,
            &chain.lines[0],
            &whole,
            &chain.lines[0].quoted(&chain.start),
            scope,
            facts,
            lines,
            &defines,
            falling,
        )?;
        for (before, line) in chain.lines.iter().zip(&chain.lines[1..]) {
            let (node, added) = link(self, &rest, line)?;
            let written = line.quoted(&before.term);
            let joined_term = self.term(&node)?;
            let joined = self.to_term(&joined_term);
            let Some(joined_label) = joined.label().map(str::to_string) else {
                return Ok(Route::no(
                    "a line of the chain is a letter, not a relation",
                ));
            };
            let joined_congruence = self.congruence_sides(&joined);
            if modulus.is_some() || joined_congruence.is_some() {
                let ordered = (modulus.is_none() && said == "wbr")
                    || (joined_congruence.is_none() && joined_label == "wbr");
                if ordered {
                    return Err(self.unreached(
                        step.line,
                        "a congruence and an order join into nothing",
                    ));
                }
                let (n, from, to) = match &joined_congruence {
                    Some(c) => {
                        (Some(c.modulus.clone()), c.left.clone(), c.right.clone())
                    }
                    None => (
                        None,
                        self.rpn(&joined.children()[0]),
                        self.rpn(&joined.children()[1]),
                    ),
                };
                if from != right {
                    return Err(self.unreached(
                        step.line,
                        "a link that reads the other way round from the one above it",
                    ));
                }
                if modulus.is_some() && n.is_none() {
                    return Err(self.unreached(
                        step.line,
                        "a chain that has become a congruence does not go back to =",
                    ));
                }
                if let (Some(a), Some(b)) = (&modulus, &n) {
                    if a != b {
                        return Err(self.unreached(
                            step.line,
                            "a chain's congruences are modulo one number",
                        ));
                    }
                }
                let held = self.link_held(
                    step, line, &joined, &written, scope, facts, lines, &defines,
                    falling,
                )?;
                let m = modulus.clone().or(n.clone()).expect("a congruence");
                if modulus.is_none() && said == "wceq" {
                    equated = Some(Equated {
                        term: right.clone(),
                        proof: proof.clone(),
                    });
                }
                proof = self.congruence_joined(
                    Joining {
                        modulus: &m,
                        left: &left,
                        middle: &right,
                        right: &to,
                        before: proof,
                        before_congruent: modulus.is_some(),
                        after: held,
                        equated: equated.as_ref(),
                    },
                    scope,
                    facts,
                )?;
                modulus = Some(m.clone());
                right = to;
                rest = added;
                reached = t!(m, t!(left, right, "cmin", "co"), "cdvds", "wbr");
                continue;
            }
            if said == "wbr" && joined_label == "wbr" {
                let next_relation = self.rpn(&joined.children()[2]).to_string();
                let Some(fold) = rules::order_folding(&relation, &next_relation) else {
                    return Err(self.unreached(
                        step.line,
                        format!(
                            "no transitivity folds {relation} into {next_relation}"
                        ),
                    ));
                };
                if self.rpn(&joined.children()[0]) != right {
                    return Err(self.unreached(
                        step.line,
                        "a link that reads the other way round from the one above it",
                    ));
                }
                let nxt = self.rpn(&joined.children()[1]);
                let held = self.link_held(
                    step, line, &joined, &written, scope, facts, lines, &defines,
                    falling,
                )?;
                // A calculation only joins (`SYNTAX.md`), so it asks no
                // membership: the links fold in ℝ*, where each order puts
                // the terms it relates.
                let before = OrderLink {
                    left: &left,
                    right: &right,
                    relation: &relation,
                    proof: &proof,
                };
                let after = OrderLink {
                    left: &right,
                    right: &nxt,
                    relation: &next_relation,
                    proof: &held,
                };
                let (first, middle) = self.extended_ends(scope, &before);
                let (_, last) = self.extended_ends(scope, &after);
                proof = pf!(self.b; scope, left, right, nxt,
                    first, middle, last, proof, held, fold.extended);
                right = nxt;
                rest = added;
                relation = fold.folded.to_string();
                reached = t!(left, right, relation, "wbr");
                continue;
            }
            let Some(fold) = rules::folding(&said, &joined_label) else {
                return Err(self.unreached(
                    step.line,
                    format!("no transitivity folds {said} into {joined_label}"),
                ));
            };
            if self.rpn(&joined.children()[0]) != right {
                return Err(self.unreached(
                    step.line,
                    "a link that reads the other way round from the one above it",
                ));
            }
            let nxt = self.rpn(&joined.children()[1]);
            if joined_label == "wbr" {
                relation = self.rpn(&joined.children()[2]).to_string();
            }
            let held = self.link_held(
                step, line, &joined, &written, scope, facts, lines, &defines, falling,
            )?;
            proof = pf!(self.b; scope, left, right, nxt, relation, proof, held, fold);
            right = nxt;
            rest = added;
            said = if said == "wceq" && joined_label == "wceq" {
                "wceq".to_string()
            } else {
                "wbr".to_string()
            };
            reached = if said == "wceq" {
                t!(left, right, "wceq")
            } else {
                t!(left, right, relation, "wbr")
            };
        }
        if reached == *term {
            return Ok(Built(proof));
        }
        let alike = take!(self.same(
            &self.to_term(&reached),
            &self.to_term(term),
            scope,
            facts,
            Some(step)
        )?);
        Ok(Built(
            pf!(self.b; scope, reached, term, proof, alike, "mpbid"),
        ))
    }

    /// A congruence's modulus and the two terms whose difference it divides,
    /// `n ∥ (a − b)` read as a ≡ b (mod n); None for any other term.
    pub(super) fn congruence_sides(&self, term: &Term) -> Option<Congruence> {
        if term.variable().is_some() || term.label() != Some("wbr") {
            return None;
        }
        let kids = term.children();
        if kids.len() != 3 || kids[2].label() != Some("cdvds") {
            return None;
        }
        let difference = &kids[1];
        let parts = difference.children();
        if difference.variable().is_some()
            || difference.label() != Some("co")
            || parts.len() != 3
            || parts[2].label() != Some("cmin")
        {
            return None;
        }
        Some(Congruence {
            modulus: self.rpn(&kids[0]),
            left: self.rpn(&parts[0]),
            right: self.rpn(&parts[1]),
        })
    }

    /// ( scope -> left ≡ right (mod n) ), from a chain's proof up to the
    /// middle term, an equation or a congruence modulo n, and its next link,
    /// a congruence modulo n: a chain that has become a congruence does not
    /// go back to = (`GRAMMAR.md`). An equation before is carried into the
    /// difference the link's modulus divides (`oveq1d`); two congruences are
    /// added, n dividing both differences and so their sum, which is the
    /// whole difference (`dvds2addd`, `npncand`).
    pub(super) fn congruence_joined(
        &mut self,
        j: Joining,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let Joining {
            modulus: n,
            left,
            middle,
            right,
            before,
            before_congruent,
            after,
            equated,
        } = j;
        let differ = |a: &Rpn, b: &Rpn| t!(a, b, "cmin", "co");
        let whole = differ(left, right);
        // The first term an integer as the term its equations reach is, where
        // the step's own lines say that one is: the line the chain names,
        // and no other the scope holds for its parts.
        let mut through: Option<(Proof, Proof)> = None;
        if let (true, Some(e)) = (before_congruent, equated) {
            if let Built(inside) = self.part(&e.term, &t!("cz"), scope, facts)? {
                let integer = self.b.ap(
                    "eqeltrd",
                    &binds! {"ph" => scope, "A" => left, "B" => &e.term, "C" => "cz"},
                    &[&e.proof, &inside],
                );
                let complex = self.b.ap(
                    "zcnd",
                    &binds! {"ph" => scope, "A" => left},
                    &[&integer],
                );
                through = Some((integer, complex));
            }
        }
        Ok(if !before_congruent {
            // left = middle, and n divides middle − right.
            let moved = self.b.ap(
                "oveq1d",
                &binds! {"ph" => scope, "A" => left, "B" => middle, "C" => right, "F" => "cmin"},
                &[&before],
            );
            self.b.ap(
                "breqtrrd",
                &binds! {"ph" => scope, "A" => n, "R" => "cdvds",
                "B" => differ(middle, right), "C" => &whole},
                &[&after, &moved],
            )
        } else {
            let (first, second) = (differ(left, middle), differ(middle, right));
            let first_integer = match &through {
                Some((integer, _)) => {
                    let middle_integer = self.membership(middle, "cz", scope, facts)?;
                    self.b.ap(
                        "zsubcld",
                        &binds! {"ph" => scope, "A" => left, "B" => middle},
                        &[integer, &middle_integer],
                    )
                }
                None => self.membership(&first, "cz", scope, facts)?,
            };
            let integers = [
                self.membership(n, "cz", scope, facts)?,
                first_integer,
                self.membership(&second, "cz", scope, facts)?,
            ];
            let summed = self.b.ap(
                "dvds2addd",
                &binds! {"ph" => scope, "K" => n, "M" => &first, "N" => &second},
                &[&integers[0], &integers[1], &integers[2], &before, &after],
            );
            let left_complex = match &through {
                Some((_, complex)) => complex.clone(),
                None => self.membership(left, "cc", scope, facts)?,
            };
            let numbers = [
                left_complex,
                self.membership(middle, "cc", scope, facts)?,
                self.membership(right, "cc", scope, facts)?,
            ];
            let cancelled = self.b.ap(
                "npncand",
                &binds! {"ph" => scope, "A" => left, "B" => middle, "C" => right},
                &[&numbers[0], &numbers[1], &numbers[2]],
            );
            self.b.ap(
                "breqtrd",
                &binds! {"ph" => scope, "A" => n, "R" => "cdvds",
                "B" => t!(first, second, "caddc", "co"), "C" => &whole},
                &[&summed, &cancelled],
            )
        })
    }
}
