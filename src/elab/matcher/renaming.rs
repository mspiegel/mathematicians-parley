//! Renaming, tidying and reaching.

use super::*;

impl<'a> Elaborator<'a> {
    /// The two as one claim, spelt with different bound variables:
    /// `cbvrexvw` is set.mm saying those are one claim. Closed, and lifted
    /// by closed lemmas, since none of this wants a scope.
    pub fn renaming(&mut self, given: &Term, want: &Term) -> Checked<Option<Proof>> {
        if self.rpn(given) == self.rpn(want) {
            return Ok(None); // nothing is spelt differently
        }
        if given.label() != want.label()
            || given.children().len() != want.children().len()
        {
            return Ok(None);
        }
        let Some(label) = given.label().map(str::to_string) else {
            return Ok(None);
        };
        if let Some((same_lemma, cross)) = lookup(rules::BOUND, &label) {
            let (body, variable, other, renamed, over);
            if given.children().len() == 3 {
                body = given.children()[0].clone();
                variable = given.children()[1].clone();
                over = Some(given.children()[2].clone());
                other = want.children()[0].clone();
                renamed = want.children()[1].clone();
                let runs = want.children()[2].clone();
                if self.rpn(over.as_ref().unwrap()) != self.rpn(&runs) {
                    // The domains may be one class spelt with other bound
                    // letters inside. The domain is carried across first,
                    // and the rest renamed.
                    let lemma = lookup(rules::DOMAIN, &label);
                    let same_class = self.class_alpha(over.as_ref().unwrap(), &runs)?;
                    let (Some(lemma), Some(same_class)) = (lemma, same_class) else {
                        return Ok(None);
                    };
                    let moved = Term::apply(
                        &label,
                        vec![body.clone(), variable.clone(), runs.clone()],
                    );
                    let Some(first) =
                        self.by_lemma(lemma, given, &moved, &[&same_class])
                    else {
                        return Ok(None);
                    };
                    if self.rpn(&moved) == self.rpn(want) {
                        return Ok(Some(first));
                    }
                    let Some(rest) = self.renaming(&moved, want)? else {
                        return Ok(None);
                    };
                    return Ok(Some(self.b.ap(
                        "bitri",
                        &binds! {"ph" => self.rpn(given), "ps" => self.rpn(&moved), "ch" => self.rpn(want)},
                        &[&first, &rest],
                    )));
                }
            } else {
                body = given.children()[0].clone();
                variable = given.children()[1].clone();
                other = want.children()[0].clone();
                renamed = want.children()[1].clone();
                over = None;
            }
            let x = self.rpn(&variable);
            let mut binds =
                binds! {"ph" => self.rpn(&body), "ps" => self.rpn(&other), "x" => &x};
            if let Some(over) = &over {
                binds.insert("A".to_string(), self.rpn(over));
            }
            let bound = |me: &Self, said: &Rpn| -> Rpn {
                match &over {
                    Some(runs) => t!(said, x, me.rpn(runs), label),
                    None => t!(said, x, label),
                }
            };
            if variable.variable() == renamed.variable() {
                let Some(inner) = self.renaming(&body, &other)? else {
                    return Ok(None);
                };
                return Ok(Some(self.b.ap(same_lemma, &binds, &[&inner])));
            }
            // The cross lemma keeps the new letter apart from the old body
            // and the old letter apart from the new: a class inside that
            // binds either is moved to a spare letter first, on its side,
            // and the three renamings joined.
            let y = self.rpn(&renamed);
            let (Some(x_name), Some(y_name)) =
                (variable.variable(), renamed.variable())
            else {
                return Ok(None);
            };
            let (x_name, y_name) = (x_name.to_string(), y_name.to_string());
            let caught = self.rpn(&body).tokens().iter().any(|t| *t == y.to_string())
                || self
                    .rpn(&other)
                    .tokens()
                    .iter()
                    .any(|t| *t == x.to_string());
            if caught {
                let Some(spare) = self.unheld(&[given, want]) else {
                    return Ok(None);
                };
                let given_moved = inner_moved(given, &y_name, &spare);
                let want_moved = inner_moved(want, &x_name, &spare);
                if self.rpn(&given_moved) == self.rpn(given)
                    && self.rpn(&want_moved) == self.rpn(want)
                {
                    return Ok(None);
                }
                let mut made: Option<Proof> = None;
                let from = self.rpn(given);
                for (one, two) in [
                    (given.clone(), given_moved.clone()),
                    (given_moved.clone(), want_moved.clone()),
                    (want_moved.clone(), want.clone()),
                ] {
                    if self.rpn(&one) == self.rpn(&two) {
                        continue;
                    }
                    let Some(step) = self.renaming(&one, &two)? else {
                        return Ok(None);
                    };
                    let to = self.rpn(&two);
                    made = Some(match made {
                        None => step,
                        Some(sofar) => self.b.ap(
                            "bitri",
                            &binds! {"ph" => &from, "ps" => self.rpn(&one), "ch" => &to},
                            &[&sofar, &step],
                        ),
                    });
                }
                return Ok(made);
            }
            // The cross lemma changes one binder and wants a hypothesis
            // relating the two bodies at x = y, which a body still spelt two
            // ways inside is not. So the bodies are made to agree first, over
            // this binder as it stands, and only then is it changed.
            let here = self.free_renamed(&other, &y, &x);
            let mut middle = binds.clone();
            middle.insert("ph".to_string(), self.rpn(&here));
            let at = t!(
                t!(x, "cv", y, "cv", "wceq"),
                t!(middle["ph"], binds["ps"], "wb"),
                "wi"
            );
            let Built(said) = self.prove_essential(
                &self.to_term(&at),
                &Rpn::default(),
                &Facts::new(),
            )?
            else {
                return Ok(None);
            };
            let mut crossed = middle.clone();
            crossed.insert("y".to_string(), y.clone());
            let changed = self.b.ap(cross, &crossed, &[&said]);
            if middle["ph"] == binds["ph"] {
                return Ok(Some(changed));
            }
            let Some(inner) = self.renaming(&body, &here)? else {
                return Ok(None);
            };
            let mut agreeing = binds.clone();
            agreeing.insert("ps".to_string(), middle["ph"].clone());
            let agreed = self.b.ap(same_lemma, &agreeing, &[&inner]);
            return Ok(Some(self.b.ap(
                "bitri",
                &binds! {"ph" => bound(self, &binds["ph"]), "ps" => bound(self, &middle["ph"]), "ch" => self.rpn(want)},
                &[&agreed, &changed],
            )));
        }
        let spelt: Vec<Rpn> = given.children().iter().map(|c| self.rpn(c)).collect();
        let other: Vec<Rpn> = want.children().iter().map(|c| self.rpn(c)).collect();
        // Both halves of an implication may be spelt differently at once. The
        // lifters each change one side and hold the other, so the sides are
        // changed one at a time and the halfway claim is what joins the two.
        let mut here = spelt.clone();
        let start = applied(&spelt, &label, None);
        let mut proof: Option<Proof> = None;
        for slot in (0..spelt.len()).filter(|&i| spelt[i] != other[i]) {
            // A connective carries a renamed statement, and a predicate over
            // classes a class renamed inside it (`class_alpha`); either
            // lemma is applied by matching what it states to the claim
            // before and after, whatever else the constructor takes.
            let (lemma, inner) = if let Some(lemma) = rules::renamed(&label, slot) {
                (
                    lemma,
                    self.renaming(&given.children()[slot], &want.children()[slot])?,
                )
            } else if let Some(lemma) = rules::PREDICATE_LIFT
                .iter()
                .find(|(l, s, _)| *l == label && *s == slot)
                .map(|(_, _, lemma)| *lemma)
            {
                (
                    lemma,
                    self.class_alpha(&given.children()[slot], &want.children()[slot])?,
                )
            } else {
                return Ok(None);
            };
            let Some(inner) = inner else {
                return Ok(None);
            };
            let was = applied(&here, &label, None);
            let mut next = here.clone();
            next[slot] = other[slot].clone();
            let now = applied(&next, &label, None);
            let Some(step) = self.by_lemma(
                lemma,
                &self.to_term(&was),
                &self.to_term(&now),
                &[&inner],
            ) else {
                return Ok(None);
            };
            here = next;
            proof = Some(match proof {
                None => step,
                Some(p) => self.b.ap(
                    "bitri",
                    &binds! {"ph" => &start, "ps" => &was, "ch" => applied(&here, &label, None)},
                    &[&p, &step],
                ),
            });
        }
        Ok(proof)
    }

    /// A proof of a claim, made a proof of the literal instance it is with
    /// identity elements dropped (`Row::Identity`): L(p) ≤ L(p) carried to
    /// L(p) ≤ L(p + 0). None where the two differ in anything else.
    pub fn tidied(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if said == want {
            return Ok(Some(proof.clone()));
        }
        let (from, to) = (self.to_term(said), self.to_term(want));
        let across = self.congruence(
            &from,
            &to,
            scope,
            facts,
            None,
            &Leaf::Rows(vec![Row::Identity]),
        )?;
        Ok(match across {
            Built(across) => {
                Some(pf!(self.b; scope, said, want, proof, across, "mpbid"))
            }
            Declined(_) => None,
        })
    }

    /// A proof of what a part of a block ends on, made a proof of the
    /// instance it is written for: the page's claim with its identity
    /// elements dropped, renamed to the instance's bound letters, and
    /// carried to the instance as it stands (`SYNTAX.md`). None where they
    /// differ in anything else.
    pub fn reached(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        // A claim written as its instance, letters renamed or not, is the
        // instance, and no element is dropped from it to be put back.
        if let Some(p) = self.respelt(proof, said, want, scope)? {
            return Ok(Some(p));
        }
        // A claim about three points in no order, its points named in
        // another order than the instance's, is the instance reordered.
        if self.reorders(said, want) {
            let known = facts.copy();
            self.know(&known, said.clone(), proof.clone());
            return self.held_reordered(&known, want, scope);
        }
        // A claim writing a defined function's rule where the instance
        // applies the function, ∏(x ∈ L) f(x) for ∏(y ∈ L) g(y), is the
        // instance with the function read where it is applied, which asks
        // the facts that each point is in the define's domain. Where they
        // do not say so, the ways below are tried.
        if self.one_read_through(said, want) {
            if let Built(alike) =
                self.same(&self.to_term(said), &self.to_term(want), scope, facts, None)?
            {
                return Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")));
            }
        }
        // A claim naming a part of the instance by a define the step cites,
        // `for all u ∈ H` where H names {s ∪ {a} : s ∈ V}, is the instance
        // with the name read as what it names (`same`).
        if self.one_with_names_read(said, want) {
            let alike = self.same(
                &self.to_term(said),
                &self.to_term(want),
                scope,
                facts,
                None,
            )?;
            return Ok(match alike {
                Built(alike) => {
                    Some(pf!(self.b; scope, said, want, proof, alike, "mpbid"))
                }
                Declined(_) => None,
            });
        }
        // Each line the part may rest on is read in its parts as well, as a
        // cited line is: "a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀" says b(0) ∈ ℕ₀, in a table
        // of the part's own.
        let known = facts.copy();
        for (line, held) in known.entries() {
            self.unpack_all(&line, &held, scope, &known);
        }
        let facts = &known;
        let said_bare = self.rpn(&self.without_identities(&self.to_term(said)));
        let want_bare = self.rpn(&self.without_identities(&self.to_term(want)));
        let Some(bare) = self.tidied(proof, said, &said_bare, scope, facts)? else {
            return Ok(None);
        };
        // The bare instance is the bare claim respelt, or, where the claim
        // names a part of it by a define the step cites, the bare claim with
        // the name read as what it names: `f = t(0) + …` for the instance
        // Σ(k = 0 to n) t(k) = t(0) + … with (m + 1) − 0 written m + 1.
        let renamed = match self.respelt(&bare, &said_bare, &want_bare, scope)? {
            Some(renamed) => renamed,
            None if self.one_with_names_read(&said_bare, &want_bare) => {
                let Built(alike) = self.same(
                    &self.to_term(&said_bare),
                    &self.to_term(&want_bare),
                    scope,
                    facts,
                    None,
                )?
                else {
                    return Ok(None);
                };
                pf!(self.b; scope, &said_bare, &want_bare, &bare, alike, "mpbid")
            }
            None => return Ok(None),
        };
        self.tidied(&renamed, &want_bare, want, scope, facts)
    }

    /// Whether two claims that differ are one once each defined name the
    /// proof may read is read as what it names (`names_read`), up to the
    /// letters they bind.
    pub fn one_with_names_read(&mut self, said: &Rpn, want: &Rpn) -> bool {
        if said == want {
            return false;
        }
        let one = self.names_read(&self.to_term(said), None);
        let other = self.names_read(&self.to_term(want), None);
        let (one, other) = (self.rpn(&one), self.rpn(&other));
        one == other || self.rebound(&one, &other)
    }

    /// Whether two terms are one once each is read through, a defined
    /// function read where it is applied as well as where it stands alone:
    /// an instance ∏(y ∈ L) g(y), with g the map x ∈ L ↦ f(x) a define
    /// makes, and a claim ∏(x ∈ L) f(x). `same` is what proves it, under
    /// whatever it asks of the scope.
    pub fn one_read_through(&mut self, said: &Rpn, want: &Rpn) -> bool {
        if said == want {
            return false;
        }
        // Only where the instance applies a defined function: without one
        // there is nothing for this reading to add to the others.
        let one = self.read_through(&self.to_term(said), true, None);
        let plain = self.read_through(&self.to_term(said), false, None);
        if self.rpn(&one) == self.rpn(&plain) {
            return false;
        }
        let other = self.read_through(&self.to_term(want), true, None);
        let (one, other) = (self.rpn(&one), self.rpn(&other));
        one == other || self.rebound(&one, &other)
    }

    /// The term with every identity element dropped where it stands, parts
    /// first.
    pub fn without_identities(&self, term: &Term) -> Term {
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        let kids: Vec<Term> = term
            .children()
            .iter()
            .map(|c| self.without_identities(c))
            .collect();
        let mut out = term.with_children(kids);
        while let Some(kept) = self.identity_dropped(&out) {
            out = kept;
        }
        out
    }

    /// A proof of a claim, made a proof of it spelt another way: what is
    /// proved is the same claim, and `same` is what says so, asking nothing
    /// of the scope.
    pub fn respelt(
        &mut self,
        proof: &Proof,
        said: &Rpn,
        want: &Rpn,
        scope: &Rpn,
    ) -> Checked<Option<Proof>> {
        if said == want {
            return Ok(Some(proof.clone()));
        }
        // The same equation the other way round, as a block's last line may
        // claim what the block says turned (`SYNTAX.md`, an equation either
        // way round is the same claim).
        if let Some((turned, flip)) = self.turned_claim(said) {
            if turned == *want {
                let Sides { left, right } = self.equation_sides(said);
                return Ok(Some(pf!(self.b; scope, left, right, proof.clone(), flip)));
            }
        }
        let alike = self.same(
            &self.to_term(said),
            &self.to_term(want),
            scope,
            &Facts::new(),
            None,
        )?;
        let Built(alike) = alike else {
            return Ok(None);
        };
        Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")))
    }

    /// `renaming` by way of letters neither statement holds: every letter
    /// the first statement binds where the second binds another, under a
    /// statement's binder or a class's, is moved to one nothing holds, and
    /// the statement is renamed from there, where nothing can be caught. The
    /// letters are only looked at, not taken.
    ///
    /// A letter both bind at the same place stays: a sequence by recursion
    /// written out binds letters inside it, which the two statements share,
    /// and set.mm has no lemma carrying a renaming through a sequence.
    pub fn renaming_apart(&mut self, said: &Rpn, want: &Rpn) -> Checked<Option<Proof>> {
        let mut letters: Vec<Symbol> = Vec::new();
        // Letters both bind at the same place, and the letters the second
        // binds where the first binds another: a shared letter that is also
        // one the renaming goes to is moved too, as the map given for F in
        // `A. i e. NN ( ( n e. NN |-> B ) ` i ) <_ C` is when i goes to n.
        let mut shared: Vec<Symbol> = Vec::new();
        let mut targets: Vec<Symbol> = Vec::new();
        let mut rest = vec![(self.to_term(said), Some(self.to_term(want)))];
        while let Some((node, theirs)) = rest.pop() {
            // Where the two are built alike, each part is compared with the
            // other's part in its place; below a place where they are not,
            // no letter of the first is bound where the second binds it.
            let theirs = theirs.filter(|t| {
                t.label() == node.label() && t.children().len() == node.children().len()
            });
            // What a binder binds is the set variable it takes as an
            // operand, wherever the binder puts it.
            let binder = node.label().is_some_and(|l| {
                lookup(rules::BOUND, l).is_some()
                    || lookup(rules::CLASS_BOUND, l).is_some()
            });
            for (at, kid) in node.children().iter().enumerate() {
                let other = theirs.as_ref().map(|t| t.children()[at].clone());
                rest.push((kid.clone(), other.clone()));
                if !binder {
                    continue;
                }
                let Some(letter) = kid.variable_symbol() else {
                    continue;
                };
                if self.typecode(self.rpn(kid).alone().unwrap_or_default()) != "setvar"
                {
                    continue;
                }
                let theirs = other.and_then(|o| o.variable_symbol());
                if theirs == Some(letter) {
                    shared.push(letter);
                    continue;
                }
                if let Some(theirs) = theirs {
                    targets.push(theirs);
                }
                if !letters.contains(&letter) {
                    letters.push(letter);
                }
            }
        }
        for letter in shared {
            if targets.contains(&letter) && !letters.contains(&letter) {
                letters.push(letter);
            }
        }
        if letters.is_empty() {
            return Ok(None); // it binds nothing, so it is not the other respelt
        }
        let Some(moved) =
            self.unheld_for(letters, &[&self.to_term(said), &self.to_term(want)])
        else {
            return Ok(None);
        };
        let middle = self.to_term(said).substitute(&moved);
        let there = self.renaming(&self.to_term(said), &middle)?;
        let back = self.renaming(&middle, &self.to_term(want))?;
        let (Some(there), Some(back)) = (there, back) else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "bitri",
            &binds! {"ph" => said, "ps" => self.rpn(&middle), "ch" => want},
            &[&there, &back],
        )))
    }

    /// A set variable no name in the proof holds and none of `terms` spells,
    /// or None when there is none left. Looked at, not taken.
    pub fn unheld(&self, terms: &[&Term]) -> Option<Term> {
        let mut held = self.names_held();
        held.extend(self.reserved.iter().cloned());
        held.extend(self.bound_as.values().cloned());
        for t in terms {
            held.extend(self.rpn(t).tokens().iter().map(|t| t.to_string()));
        }
        let free = self.spare.iter().find(|v| !held.contains(*v))?;
        Some(self.var_of(free))
    }

    /// Each of `letters` with a letter of its own from `unheld`: none that
    /// `terms` spells or that another of them was given. None when too few
    /// are left. Looked at, not taken.
    pub fn unheld_for(
        &self,
        letters: impl IntoIterator<Item = Symbol>,
        terms: &[&Term],
    ) -> Option<Binding> {
        let mut moved = Binding::new();
        for letter in letters {
            let fresh = {
                let mut seen: Vec<&Term> = terms.to_vec();
                seen.extend(moved.values());
                self.unheld(&seen)?
            };
            moved.insert(letter, fresh);
        }
        Some(moved)
    }

    /// ( scope -> wanted ) from a fact saying it over other bound letters,
    /// carried by `renaming`; None where no fact does.
    pub(super) fn fact_respelt(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let want = self.rpn(wanted);
        for (said, proof) in facts.entries() {
            if said == want {
                return Ok(Some(proof));
            }
            let held = self.to_term(&said);
            if held.label() != wanted.label() {
                continue;
            }
            let Some(across) = self.renaming_apart(&said, &want)? else {
                // Or read the same in standard form.
                let Built(alike) = self.same(&held, wanted, scope, facts, None)? else {
                    continue;
                };
                return Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")));
            };
            let turned = pf!(self.b; t!(said, want, "wb"), scope, across, "a1i");
            return Ok(Some(pf!(self.b; scope, said, want, proof, turned, "mpbid")));
        }
        Ok(None)
    }

    /// Every token the scopes of the open frames spell.
    pub(super) fn frames_spell(&self) -> BTreeSet<String> {
        self.frames
            .iter()
            .flat_map(|f| {
                f.scope
                    .tokens()
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// `binding` with a letter nothing in the proof holds, for each set
    /// variable the lemma keeps apart from its scope and the claim did not
    /// fix: always, and not only where the frames spell the lemma's own, so
    /// that which letter a line happened to bind decides nothing
    /// (`ELABORATION.md`, "Where a step is proved").
    pub(super) fn letters_unheld(&self, sig: &Signature, binding: Binding) -> Binding {
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        let mut apart: BTreeSet<Symbol> = BTreeSet::new();
        for (a, b) in &sig.disjoint {
            for (one, other) in [(a, b), (b, a)] {
                if kinds.get(one.as_str()) != Some(&"setvar") {
                    continue;
                }
                // Kept apart from a class the claim leaves open, which the
                // scope may spell; or from another letter the claim has
                // fixed, which a cited line may bind as well: a lemma about a
                // product may keep its x from the product's k, and a line
                // saying "for all r ∈ S" would hand x the r the product fixed
                // as k.
                let from_class = !binding.contains_key(other)
                    && !matches!(kinds.get(other.as_str()), None | Some(&"setvar"));
                let from_fixed = kinds.get(other.as_str()) == Some(&"setvar")
                    && binding.contains_key(other);
                // Or from a class the claim has fixed as one that binds a
                // letter inside it: ffnfv's x kept apart from F, F the map
                // sending x ∈ ℝ to F(x), is not the map's x.
                let from_binding_class =
                    !matches!(kinds.get(other.as_str()), None | Some(&"setvar"))
                        && binding.get(other).is_some_and(|v| self.binds_a_letter(v));
                if from_class || from_fixed || from_binding_class {
                    apart.insert(*one);
                }
            }
        }
        let mut out = binding;
        let open: Vec<Symbol> =
            apart.into_iter().filter(|v| !out.contains_key(v)).collect();
        let moved = {
            let frames: Vec<Term> =
                self.frames.iter().map(|f| self.to_term(&f.scope)).collect();
            let mut terms: Vec<&Term> = frames.iter().collect();
            terms.extend(out.values());
            self.unheld_for(open, &terms)
        };
        if let Some(moved) = moved {
            out.extend(moved);
        }
        out
    }

    /// The claim proved with its bound letters moved off what the frames
    /// spell, and spelt back; `why` where it binds none of those.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn over_other_letters(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
        why: Decline,
    ) -> Checked<Route<Proof>> {
        let held = self.names_held();
        let spelt = self.frames_spell();
        let mut letters: BTreeSet<Symbol> = BTreeSet::new();
        let mut rest = vec![goal.clone()];
        while let Some(node) = rest.pop() {
            if let Some(letter) = node.variable_symbol() {
                let said = self.rpn(&node);
                let said = said.alone().unwrap_or_default();
                if self.typecode(said) == "setvar"
                    && !held.contains(said)
                    && spelt.contains(said)
                {
                    letters.insert(letter);
                }
                continue;
            }
            rest.extend(node.children().iter().cloned());
        }
        if letters.is_empty() {
            return Ok(Declined(why));
        }
        let frames: Vec<Term> =
            self.frames.iter().map(|f| self.to_term(&f.scope)).collect();
        let mut terms: Vec<&Term> = vec![goal];
        terms.extend(frames.iter());
        let Some(moved) = self.unheld_for(letters, &terms) else {
            return Ok(Declined(why));
        };
        let other = goal.substitute(&moved);
        // What the citation fixed of the claim is fixed of it over the new
        // letters too: a set-builder's letter the seed names moves with it.
        let seed: Option<Binding> =
            seed.map(|s| s.iter().map(|(k, v)| (*k, v.substitute(&moved))).collect());
        let proof = take!(self.apply_lemma(
            label,
            &other,
            scope,
            facts,
            step,
            crossing,
            seed.as_ref()
        )?);
        let back = self.respelt(&proof, &self.rpn(&other), &self.rpn(goal), scope)?;
        Ok(match back {
            Some(p) => Built(p),
            None => Declined(why),
        })
    }

    /// A lemma that binds two letters apart, where the claim binds one: the
    /// sum on the right is renamed to a letter nothing holds, the lemma
    /// proves that, and `cbvsumv` says the two sums are one.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn letters_apart(
        &mut self,
        label: &str,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        crossing: bool,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wceq") || goal.children()[1].label() != Some("csu") {
            return Ok(Route::no(format!(
                "{label} binds two letters apart where the claim binds one, and the claim is not an equation with a sum on its right"
            )));
        }
        let (left, right) = (goal.children()[0].clone(), goal.children()[1].clone());
        let (limits, summand, index) = (
            right.children()[0].clone(),
            right.children()[1].clone(),
            right.children()[2].clone(),
        );
        let Some(index_letter) = index.variable().map(Symbol::of) else {
            return Ok(Route::no(format!(
                "{label} binds two letters apart where the claim binds one, and the sum's index is no letter"
            )));
        };
        let Some(letter) = self.unheld(&[goal]) else {
            return Ok(Route::no("no letter left to rename a sum with"));
        };
        let mut put = Binding::new();
        put.insert(index_letter, letter.clone());
        let moved = summand.substitute(&put);
        let renamed =
            Term::apply("csu", vec![limits.clone(), moved.clone(), letter.clone()]);
        let first = take!(self.apply_lemma(
            label,
            &Term::apply("wceq", vec![left.clone(), renamed.clone()]),
            scope,
            facts,
            step,
            crossing,
            seed
        )?);
        let tie = Term::apply(
            "wi",
            vec![
                Term::apply(
                    "wceq",
                    vec![
                        Term::apply("cv", vec![letter.clone()]),
                        Term::apply("cv", vec![index.clone()]),
                    ],
                ),
                Term::apply("wceq", vec![moved.clone(), summand.clone()]),
            ],
        );
        let tie = take!(self.prove_essential(&tie, scope, facts)?);
        let same_sum = self.b.ap(
            "cbvsumv",
            &binds! {"j" => self.rpn(&letter), "k" => self.rpn(&index), "A" => self.rpn(&limits),
            "B" => self.rpn(&moved), "C" => self.rpn(&summand)},
            &[&tie],
        );
        let (was, now) = (self.rpn(&renamed), self.rpn(&right));
        let carried = pf!(self.b; t!(was, now, "wceq"), scope, same_sum, "a1i");
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => self.rpn(&left), "B" => &was, "C" => &now},
            &[&first, &carried],
        )))
    }

    // --- one lemma ------------------------------------------------------

    /// A lemma's existential taken apart, and the claim's put back: the
    /// lemma's existential is proved, weakened where it says exactly one,
    /// eliminated, and the claim introduced at the variables it gave up.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn through_existential(
        &mut self,
        label: &str,
        reads: &Term,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
        seed: Option<&Binding>,
    ) -> Checked<Route<Proof>> {
        if goal.label() != Some("wrex")
            || !matches!(reads.label(), Some("wrex") | Some("wreu"))
        {
            return Ok(Route::no(format!(
                "{label} and the claim are not both \"there is\""
            )));
        }
        let own = self.bound_in(reads);
        let unfixed = match seed {
            None => true,
            Some(seed) => reads
                .names()
                .iter()
                .any(|n| !seed.contains_key(&**n) && !own.iter().any(|b| **b == **n)),
        };
        if unfixed {
            return Ok(Route::no(format!("nothing fixes the variables of {label}")));
        }
        let seed = seed.unwrap();
        let mut ground = reads.substitute(seed);
        // The lemma's binders become names in the open, so they must be
        // variables nothing else holds, and the claim's own binders are
        // among what is held.
        let taken = self.bound_in(goal);
        let mut swap = Binding::new();
        for name in self.bound_in(&ground) {
            let mut fresh = self.spare_var()?;
            while taken.contains(&self.sig(&fresh).statement[1]) {
                fresh = self.spare_var()?;
            }
            swap.insert(name, self.var_of(&fresh));
        }
        ground = ground.substitute(&swap);
        let mut strong = take!(self.apply_lemma(
            label,
            &ground,
            scope,
            facts,
            step,
            false,
            Some(seed)
        )?);
        if ground.label() == Some("wreu") {
            let weaker = Term::apply("wrex", ground.children().to_vec());
            let kids: Vec<Rpn> =
                ground.children().iter().map(|c| self.rpn(c)).collect();
            let law = self.b.ap(
                "reurex",
                &binds! {"ph" => &kids[0], "x" => &kids[1], "A" => &kids[2]},
                &[],
            );
            strong = pf!(self.b; scope, self.rpn(&ground), self.rpn(&weaker), strong, law, "syl");
            ground = weaker;
        }
        let mut layers: Vec<(Rpn, Rpn)> = Vec::new();
        let mut rest = ground.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            layers.push((self.rpn(&kids[1]), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        let body = self.rpn(&rest);
        let memberships: Vec<Rpn> =
            layers.iter().map(|(v, s)| t!(v, "cv", s, "wcel")).collect();
        let mut member =
            Rpn::joined(&memberships.iter().map(Rpn::tokens).collect::<Vec<_>>());
        if layers.len() > 1 {
            member = t!(member, "wa");
        }
        let made = self.frames_kept(|me| {
            let (outer, held) = me.widen(scope, facts, &member, None);
            let (inner, lifted) = me.widen(&outer, &held, &body, None);
            me.introduced(goal, &inner, &lifted)
                .map(|r| r.map(|p| (outer, p)))
        })?;
        let (outer, made) = take!(made);
        let want = self.rpn(goal);
        let discharge = if layers.len() == 1 {
            "rexlimdva"
        } else {
            "rexlimdvva"
        };
        let mut pushed: Vec<Rpn> = layers.iter().map(|(v, _)| v.clone()).collect();
        pushed.extend(layers.iter().map(|(_, s)| s.clone()));
        let lifted = pf!(self.b; outer, body, want, made, "ex");
        let mut all: Vec<crate::mm::spell::Part> = vec![
            crate::elab::part(scope),
            crate::elab::part(&body),
            crate::elab::part(&want),
        ];
        all.extend(pushed.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(&lifted));
        all.push(crate::elab::part(discharge));
        let eliminated = self.b.proof(&all);
        Ok(Built(
            pf!(self.b; scope, self.rpn(&ground), want, strong, eliminated, "mpd"),
        ))
    }
}
