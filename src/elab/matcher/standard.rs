//! The standard form, applied maps and their proofs.

use super::*;

impl<'a> Elaborator<'a> {
    /// A map's rule with every setvar it binds, but the map's own, renamed to
    /// letters nothing holds when it is first asked for: one spelling per
    /// map, so that the rule at any value reads one way wherever it is read.
    pub(super) fn rule_apart(&mut self, f: &Term) -> Term {
        let key = self.rpn(f);
        if let Some(found) = self.rules_read.get(&key) {
            return found.clone();
        }
        let (bound, mut rule) = (f.children()[0].clone(), f.children()[2].clone());
        // The map's own letter, where it binds one, is the rule's to keep.
        let own = bound.variable().map(Symbol::of);
        let mut letters: Vec<Symbol> = self
            .letters_bound(&rule)
            .into_iter()
            .filter(|v| Some(*v) != own)
            .collect();
        letters.sort_by_key(|v| {
            self.b.float_order(&self.float_of(v)).unwrap_or(usize::MAX)
        });
        for letter in letters {
            let label = self.float_of(&letter);
            if !self.is_setvar(&label) {
                continue;
            }
            let Some(fresh) = self.unheld(&[&rule, f]) else {
                break;
            };
            let mut put = Binding::new();
            put.insert(letter, fresh);
            rule = rule.substitute(&put);
        }
        self.rules_read.insert(key, rule.clone());
        rule
    }

    /// The rules of `rules::STANDARD` set.mm has. A rule that asks something
    /// first holds only where that is so, which a standard form cannot know;
    /// such a rule is `conditional`, and is used only where it closes a
    /// difference the walk has found.
    pub fn rewrites(&mut self, conditional: bool) -> Rc<[Rewrite]> {
        if self.rewrite_rules.is_none() {
            let [plain, asking] = self.standard_rules();
            self.rewrite_rules = Some([plain.into(), asking.into()]);
        }
        Rc::clone(&self.rewrite_rules.as_ref().unwrap()[conditional as usize])
    }

    /// The rules of `rules::STANDARD` set.mm has, those that ask nothing
    /// first and those that do (`rewrites`).
    pub fn standard_rules(&self) -> [Vec<Rewrite>; 2] {
        let mut plain = Vec::new();
        let mut asking = Vec::new();
        for (label, side) in rules::STANDARD {
            if !self.b.sigs.contains_key(label) {
                continue;
            }
            let says = self.statement(label);
            let mut body = says.clone();
            while body.label() == Some("wi") {
                body = body.children()[1].clone();
            }
            let s = *side as usize;
            let rule = Rewrite {
                label: label.to_string(),
                given: body.children()[1 - s].clone(),
                gives: body.children()[s].clone(),
                names: names_of(&says),
            };
            if says.label() == Some("wi") {
                asking.push(rule);
            } else {
                plain.push(rule);
            }
        }
        [plain, asking]
    }

    /// ( where -> cur <-> nxt ), or `=`, for one rewrite at the head.
    pub fn standard_proof(
        &mut self,
        cur: &Term,
        how: &How,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let (a, b) = (self.rpn(cur), self.rpn(nxt));
        match how {
            How::Defined => Ok(match self.held(held, &t!(a, b, "wceq"), where_)? {
                Some(p) => Built(p),
                None => Route::no("the equation a define holds is not in hand"),
            }),
            How::Applied if cur.label() == Some("co") => {
                self.applied_proof_of_two(cur, nxt, where_, held)
            }
            How::Applied => self.applied_proof(cur, nxt, where_, held),
            How::Eqcom => {
                let (left, right) =
                    (self.rpn(&cur.children()[0]), self.rpn(&cur.children()[1]));
                let law =
                    self.b
                        .ap("eqcom", &binds! {"A" => &left, "B" => &right}, &[]);
                Ok(Built(pf!(self.b; t!(a, b, "wb"), where_, law, "a1i")))
            }
            How::Commuted => {
                let goal = self.to_term(&t!(a, b, "wceq"));
                self.settle(&goal, where_, held, 3, None, None)
            }
            How::Listed(label) => {
                let goal = self.to_term(&t!(a, b, "wceq"));
                self.apply_lemma(label, &goal, where_, held, None, false, None)
            }
            How::Exchanged(label) => {
                // A formula's two orders say the same, ↔; a term's two are
                // one value, =.
                let join = if self.is_wff(cur) { "wb" } else { "wceq" };
                let goal = self.to_term(&t!(a, b, join));
                self.apply_lemma(label, &goal, where_, held, None, false, None)
            }
            How::Rule(label) => {
                let wff = self.is_wff(cur);
                let join = if wff { "wb" } else { "wceq" };
                if lookup(rules::STANDARD, label) == Some(Side::Right) {
                    let goal = self.to_term(&t!(a, b, join));
                    return self
                        .apply_lemma(label, &goal, where_, held, None, false, None);
                }
                let goal = self.to_term(&t!(b, a, join));
                let made =
                    take!(self
                        .apply_lemma(label, &goal, where_, held, None, false, None)?);
                Ok(Built(if wff {
                    self.b.ap(
                        "bicomd",
                        &binds! {"ph" => where_, "ps" => &b, "ch" => &a},
                        &[&made],
                    )
                } else {
                    self.b.ap(
                        "eqcomd",
                        &binds! {"ph" => where_, "A" => &b, "B" => &a},
                        &[&made],
                    )
                }))
            }
        }
    }

    /// The map a function application applies, written as a map or as the
    /// name a define gave it; else None.
    pub(crate) fn applied_map(&self, term: &Term) -> Option<Term> {
        if term.variable().is_some()
            || term.label() != Some("cfv")
            || term.children().len() != 2
        {
            return None;
        }
        let mut f = term.children()[1].clone();
        if let Some(named) = self.named_body(&f, &self.binding) {
            f = named;
        }
        if f.variable().is_some()
            || f.label() != Some("cmpt")
            || f.children().len() != 3
        {
            return None;
        }
        Some(f)
    }

    /// ( where -> ( F ` A ) = C ), C the rule of F's map at A; a decline
    /// where A is not shown to be in the map's domain.
    pub(crate) fn applied_proof(
        &mut self,
        cur: &Term,
        nxt: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Route<Proof>> {
        let (at, written) = (cur.children()[0].clone(), cur.children()[1].clone());
        let own = self.applied_map(cur).expect("an applied map");
        let mut f = own.clone();
        let (bound, over, mut rule) = (
            own.children()[0].clone(),
            own.children()[1].clone(),
            own.children()[2].clone(),
        );
        let c = self.rpn(nxt);
        // Where the rule was read in its other spelling, the map is first
        // shown to be the same map over that spelling, closed, and the value
        // is taken there.
        let apart = self.rules_read.get(&self.rpn(&own)).cloned();
        let mut renamed = None;
        if let Some(apart) = apart {
            let was = t!(self.rpn(&bound), "cv");
            if self.rpn(&self.restated(&rule, &was, &self.rpn(&at))) != c {
                f = own.with_children(vec![bound.clone(), over.clone(), apart.clone()]);
                rule = apart;
                renamed = self.class_alpha(&own, &f)?;
                if renamed.is_none() {
                    return Ok(Route::no("the rule is not renamed apart"));
                }
            }
        }
        let x = self.rpn(&bound);
        let a = self.rpn(&at);
        let b = self.rpn(&rule);
        let d = self.rpn(&over);
        let written_f = self.rpn(&written);
        let tie = self.to_term(&t!(t!(x, "cv", a, "wceq"), t!(b, c, "wceq"), "wi"));
        let instance =
            take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
        let member = take!(self.domain_membership(&a, &d, where_, held)?);
        let a_set = take!(self.settle(
            &self.to_term(&t!(c, "cvv", "wcel")),
            where_,
            held,
            3,
            None,
            None
        )?);
        let mapped = self.rpn(&f);
        let direct = self.b.ap(
            "fvmptd3",
            &binds! {"ph" => where_, "x" => &x, "A" => &a, "B" => &b, "C" => &c, "D" => &d, "F" => &mapped, "V" => "cvv"},
            &[&pf!(self.b; mapped, "eqid"), &instance, &member, &a_set],
        );
        if written_f == mapped {
            return Ok(Built(direct));
        }
        // A defined name is carried to its map first.
        let spelt = self.rpn(&own);
        let mut named = None;
        if written_f != spelt {
            named = self.held(held, &t!(written_f, spelt, "wceq"), where_)?;
            if named.is_none() {
                return Ok(Route::no("the equation a define holds is not in hand"));
            }
        }
        if let Some(renamed) = renamed {
            let same_map =
                pf!(self.b; t!(spelt, mapped, "wceq"), where_, renamed, "a1i");
            named = Some(match named {
                None => same_map,
                Some(n) => self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => where_, "A" => &written_f, "B" => &spelt, "C" => &mapped},
                    &[&n, &same_map],
                ),
            });
        }
        let named = named.expect("a proof the name is its map");
        let via = self.b.ap(
            "fveq1d",
            &binds! {"ph" => where_, "A" => &a, "F" => &written_f, "G" => &mapped},
            &[&named],
        );
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => where_, "A" => t!(a, written_f, "cfv"), "B" => t!(a, mapped, "cfv"), "C" => &c},
            &[&via, &direct],
        )))
    }

    /// Whether a term is a statement rather than a class.
    pub fn is_wff(&self, term: &Term) -> bool {
        let label = match (term.variable(), term.label()) {
            (Some(v), _) => self.float_of(v),
            (None, Some(label)) => label.to_string(),
            (None, None) => return false,
        };
        self.typecode(&label) == "wff"
    }

    /// One proof of the first term against the last, from links each proving
    /// one against the next, joined by `bitrd` or `eqtrd`.
    pub fn chained(&self, where_: &Rpn, links: &[ChainLink]) -> Proof {
        let (first, mut last, mut proof) = (
            links[0].from.clone(),
            links[0].to.clone(),
            links[0].proof.clone(),
        );
        let wff = self.is_wff(&first);
        let start = self.rpn(&first);
        for ChainLink {
            to: now,
            proof: more,
            ..
        } in &links[1..]
        {
            let (mid, end) = (self.rpn(&last), self.rpn(now));
            proof = if wff {
                self.b.ap(
                    "bitrd",
                    &binds! {"ph" => where_, "ps" => &start, "ch" => &mid, "th" => &end},
                    &[&proof, more],
                )
            } else {
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => where_, "A" => &start, "B" => &mid, "C" => &end},
                    &[&proof, more],
                )
            };
            last = now.clone();
        }
        proof
    }

    /// Whether the walk can go a level in from these two: the same
    /// constructor, and a lemma in `rules::CONGRUENCE` for the places that
    /// differ; under an existential only its body may.
    pub(super) fn lifts(&self, one: &Term, other: &Term) -> bool {
        if one.variable().is_some()
            || other.variable().is_some()
            || one.label() != other.label()
            || one.children().len() != other.children().len()
        {
            return false;
        }
        let spelt: Vec<Rpn> = one.children().iter().map(|c| self.rpn(c)).collect();
        let theirs: Vec<Rpn> = other.children().iter().map(|c| self.rpn(c)).collect();
        let Some(label) = one.label() else {
            return false;
        };
        if label == "wrex" && spelt[1] != theirs[1] {
            return false;
        }
        // A sum's term, or a product's factor, is carried under its index
        // as `congruence` carries it.
        if (label == "csu" || label == "cprod") && spelt[1] != theirs[1] {
            return spelt[0] == theirs[0] && spelt[2] == theirs[2];
        }
        // An integral's integrand, under its letter between the ends.
        if label == "cdit" && spelt[3] != theirs[3] {
            return spelt[..3] == theirs[..3];
        }
        // A map's rule, under its letter over the domain.
        if label == "cmpt" && spelt[2] != theirs[2] {
            return spelt[..2] == theirs[..2];
        }
        let mut places = spelt.len();
        if rules::WRAPS.contains(&label) && spelt[places - 1] == theirs[places - 1] {
            places -= 1;
        }
        let slots: Vec<usize> =
            (0..places).filter(|&i| spelt[i] != theirs[i]).collect();
        slots.is_empty()
            || rules::congruence(label, &slots).is_some()
            || rules::function_law(label, &slots).is_some()
    }

    /// `one` carried to `other`, its standard form: where only the parts
    /// rewrite, the walk goes a level in; otherwise the parts are put in
    /// standard form first, the head is rewritten once, and what that gives
    /// is carried on the same way.
    pub(super) fn closed_toward(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        if self.rpn(one) == self.rpn(other) {
            return Ok(None);
        }
        if let Some((how, turned)) = self.pair_first(one) {
            let Built(made) = self.standard_proof(one, &how, &turned, where_, held)?
            else {
                return Ok(Some(Route::no("the pair cannot be turned")));
            };
            let mut links = vec![ChainLink {
                from: one.clone(),
                to: turned.clone(),
                proof: made,
            }];
            if self.rpn(&turned) != self.rpn(other) {
                let rest = self.congruence(
                    &turned,
                    other,
                    where_,
                    held,
                    None,
                    &Leaf::Rows(vec![Row::Toward]),
                )?;
                let Built(rest) = rest else {
                    return Ok(Some(rest));
                };
                links.push(ChainLink {
                    from: turned,
                    to: other.clone(),
                    proof: rest,
                });
            }
            return Ok(Some(Built(self.chained(where_, &links))));
        }
        // A function applied keeps its function.
        let wrapped = one.label().is_some_and(|l| rules::WRAPS.contains(&l));
        let n = one.children().len();
        let kids: Vec<Term> = one
            .children()
            .iter()
            .enumerate()
            .map(|(i, c)| {
                if wrapped && i == n - 1 {
                    c.clone()
                } else {
                    self.standard(c)
                }
            })
            .collect();
        let parts = one.with_children(kids);
        if self.rpn(&parts) == self.rpn(other) && self.lifts(one, &parts) {
            return Ok(None);
        }
        let mut links: Vec<ChainLink> = Vec::new();
        let mut cur = one.clone();
        if self.rpn(&parts) != self.rpn(one) {
            if !self.lifts(one, &parts) {
                return Ok(Some(Route::no("the parts cannot be rewritten in place")));
            }
            let made = self.congruence(
                one,
                &parts,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: one.clone(),
                to: parts.clone(),
                proof: made,
            });
            cur = parts;
        }
        let Some((how, nxt)) = self.standard_step(&cur) else {
            return Ok(Some(Route::no("no rule rewrites the head")));
        };
        let made = self.standard_proof(&cur, &how, &nxt, where_, held)?;
        let Built(made) = made else {
            return Ok(Some(made));
        };
        links.push(ChainLink {
            from: cur,
            to: nxt.clone(),
            proof: made,
        });
        if self.rpn(&nxt) != self.rpn(other) {
            let made = self.congruence(
                &nxt,
                other,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: nxt,
                to: other.clone(),
                proof: made,
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// Two terms with one standard form, at the smallest place they differ:
    /// each carried to its standard form, and the two forms joined by a
    /// renaming where they differ only in the letters they bind.
    pub(super) fn closed_standard(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b {
            return Ok(None);
        }
        // Two that differ only in the letters they bind are one claim by a
        // renaming, which is closed and asks nothing of the scope.
        if self.rebound(&a, &b) {
            let wff = self.is_wff(one);
            let renamed = if wff {
                self.renamed_apart(one, other)?
            } else {
                self.class_renamed(one, other)?
            };
            if let Some(renamed) = renamed {
                let join = if wff { "wb" } else { "wceq" };
                return Ok(Some(Built(
                    pf!(self.b; t!(a, b, join), where_, renamed, "a1i"),
                )));
            }
        }
        let (ours, theirs) = (self.standard(one), self.standard(other));
        let (said, want) = (self.rpn(&ours), self.rpn(&theirs));
        // Letters bound at two depths are paired at each by `class_alpha`
        // and not by `rebound`, which pairs them once for the whole term.
        if said != want && !self.rebound(&said, &want) {
            let unpaired =
                self.is_wff(&ours) || self.class_alpha(&ours, &theirs)?.is_none();
            if unpaired {
                return Ok(self.conditioned(one, other, where_, held)?.map(Built));
            }
        }
        // A formula's pair in no order, crossed between the two sides, is
        // exchanged at the head before the walk goes in: P and A on one side
        // of a line differ from A and P inside a product the pair spreads
        // across, Im(…P…)·Im(…A…), whose factors are exchanged only where
        // each is known to be a number.
        let crossed = self.pair_crossed(one, other);
        if crossed.is_none() && self.lifts(one, other) {
            let mut all = true;
            for (x, y) in one.children().iter().zip(other.children()) {
                if !self.alike_in_place(x, y) {
                    all = false;
                    break;
                }
            }
            if all {
                return Ok(None); // the walk goes a level in
            }
        }
        // One rewrite at the head of either side, and the walk again from
        // there, touches only what differs.
        for (x, y, forward) in [(one, other, true), (other, one, false)] {
            let turned = match &crossed {
                Some(c) if forward => Some(c.clone()),
                _ => None,
            };
            let Some((how, nxt)) = turned.or_else(|| self.standard_step(x)) else {
                continue;
            };
            let Built(made) = self.standard_proof(x, &how, &nxt, where_, held)? else {
                continue;
            };
            let mut links = vec![ChainLink {
                from: x.clone(),
                to: nxt.clone(),
                proof: made,
            }];
            if self.rpn(&nxt) != self.rpn(y) {
                let Built(rest) = self.congruence(
                    &nxt,
                    y,
                    where_,
                    held,
                    None,
                    &Leaf::Rows(vec![Row::Standard]),
                )?
                else {
                    continue;
                };
                links.push(ChainLink {
                    from: nxt,
                    to: y.clone(),
                    proof: rest,
                });
            }
            let proof = self.chained(where_, &links);
            return Ok(Some(Built(if forward {
                proof
            } else {
                self.flipped(where_, x, y, &proof)
            })));
        }
        let mut links: Vec<ChainLink> = Vec::new();
        if self.rpn(&ours) != a {
            let made = self.congruence(
                one,
                &ours,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            links.push(ChainLink {
                from: one.clone(),
                to: ours.clone(),
                proof: made,
            });
        }
        if said != want {
            let wff = self.is_wff(&ours);
            let renamed = if wff {
                self.renamed_apart(&ours, &theirs)?
            } else {
                self.class_alpha(&ours, &theirs)?
            };
            let Some(renamed) = renamed else {
                return Ok(Some(Route::no("no renaming says the two are one")));
            };
            let join = if wff { "wb" } else { "wceq" };
            links.push(ChainLink {
                from: ours.clone(),
                to: theirs.clone(),
                proof: pf!(self.b; t!(said, want, join), where_, renamed, "a1i"),
            });
        }
        if self.rpn(&theirs) != b {
            let made = self.congruence(
                other,
                &theirs,
                where_,
                held,
                None,
                &Leaf::Rows(vec![Row::Toward]),
            )?;
            let Built(made) = made else {
                return Ok(Some(made));
            };
            let flipped = self.flipped(where_, other, &theirs, &made);
            links.push(ChainLink {
                from: theirs.clone(),
                to: other.clone(),
                proof: flipped,
            });
        }
        Ok(Some(Built(self.chained(where_, &links))))
    }

    /// A closed proof that two statements differing in their bound letters
    /// are one, by way of letters neither holds; else None.
    pub fn renamed_apart(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        self.renaming_apart(&a, &b)
    }

    /// Whether two parts come to one standard form, where the walk can close
    /// them one by one below. Either may also differ in the letters it binds:
    /// a class is closed at the class itself, by `class_renamed`, and a
    /// statement is walked into, down to the classes and statements that
    /// bind the letters, each closed there. A statement whose letters a
    /// class inside it binds otherwise, `|G(m, n)|·(m + n) = …` beside the
    /// same with G's set written out, is carried in place so: carried to its
    /// standard form instead, it would be put in the order the bound letters
    /// read as blanks give, which may need a product turned round, and that
    /// asks of a size what nothing says, that it is a number.
    pub(super) fn alike_in_place(&mut self, one: &Term, other: &Term) -> bool {
        let said = self.standard(one);
        let said = self.rpn(&said);
        let want = self.standard(other);
        let want = self.rpn(&want);
        said == want || self.rebound(&said, &want)
    }

    /// Two maps differing in their letter, over a domain that binds one of
    /// the two letters itself: `cbvmptv` holds both apart from the domain,
    /// so the domain's own letter is moved to one neither map holds first
    /// (`mpteq1i`), the maps' letter renamed over the domain so spelt, and
    /// the other map carried back. g(x) = √x over D = {x ∈ ℝ : x > 0} is
    /// such a map. A set-builder is renamed the same way (`cbvrabv`,
    /// `rabeqi`): {c ∈ G(m, n) : …} read with G's rule, which binds c too.
    /// None where the domain binds neither letter.
    pub(super) fn renamed_over_a_domain_apart(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        // A map holds its letter first and its domain after it, and a
        // set-builder its condition, its letter and then its domain.
        let Some(label) = one.label().map(str::to_string) else {
            return Ok(None);
        };
        let (letter_at, domain_at) = if label == "crab" { (1, 2) } else { (0, 1) };
        let Some(lemma) = lookup(rules::DOMAIN, &label) else {
            return Ok(None);
        };
        let letters: Vars = [&one.children()[letter_at], &other.children()[letter_at]]
            .iter()
            .filter_map(|v| v.variable_symbol())
            .collect();
        let (domain, there) =
            (&one.children()[domain_at], &other.children()[domain_at]);
        let clashing: Vec<Symbol> = self
            .letters_bound(domain)
            .union(&self.letters_bound(there))
            .filter(|v| letters.contains(*v))
            .copied()
            .collect();
        if clashing.is_empty() {
            return Ok(None);
        }
        let Some(moved) = self.unheld_for(clashing, &[one, other]) else {
            return Ok(None);
        };
        let apart = domain.substitute(&moved);
        let to_apart = |me: &mut Self, d: &Term| -> Checked<Option<Proof>> {
            if me.rpn(d) == me.rpn(&apart) {
                let d = me.rpn(d);
                return Ok(Some(me.b.ap("eqid", &binds! {"A" => &d}, &[])));
            }
            me.class_alpha(d, &apart)
        };
        let (Some(from_one), Some(from_other)) =
            (to_apart(self, domain)?, to_apart(self, there)?)
        else {
            return Ok(None);
        };
        let over = |map: &Term| {
            let mut kids = map.children().to_vec();
            kids[domain_at] = apart.clone();
            Term::apply(&label, kids)
        };
        let (one_there, other_there) = (over(one), over(other));
        let (Some(first), Some(last)) = (
            self.by_lemma(lemma, one, &one_there, &[&from_one]),
            self.by_lemma(lemma, other, &other_there, &[&from_other]),
        ) else {
            return Ok(None);
        };
        let Some(middle) = self.class_renamed(&one_there, &other_there)? else {
            return Ok(None);
        };
        let (a, b, c, d) = (
            self.rpn(one),
            self.rpn(&one_there),
            self.rpn(&other_there),
            self.rpn(other),
        );
        let to_there = self.b.ap(
            "eqtri",
            &binds! {"A" => &a, "B" => &b, "C" => &c},
            &[&first, &middle],
        );
        Ok(Some(self.b.ap(
            "eqtr4i",
            &binds! {"A" => &a, "B" => &c, "C" => &d},
            &[&to_there, &last],
        )))
    }

    /// A closed proof that two classes differing in the letter they bind are
    /// one (`one = other`), by the lemma `rules::CLASS_BOUND` names for the
    /// binder; else None.
    pub(super) fn class_renamed(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let lemma = if one.variable().is_none() && other.label() == one.label() {
            one.label().and_then(|l| lookup(rules::CLASS_BOUND, l))
        } else {
            None
        };
        let Some(lemma) = lemma else {
            return Ok(None);
        };
        let says = self.statement(lemma);
        let variables = names_of(&says);
        let Some(binding) = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], other, &b, &variables))
        else {
            return Ok(None);
        };
        let sig = self.sig(lemma).clone();
        // The lemma keeps pairs of its variables apart, and a class binding
        // the new letter inside, a map given for F that binds n while n is
        // the letter renamed to, would break that: renamed inside first.
        let apart = sig.disjoint.iter().all(|(a, b)| {
            let (Some(x), Some(y)) = (binding.get(a), binding.get(b)) else {
                return true;
            };
            let theirs = y.names();
            x.names().iter().all(|n| !theirs.contains(n))
        });
        if !apart {
            if let Some(made) = self.renamed_past_inner(one, other)? {
                return Ok(Some(made));
            }
            return self.class_renamed_within(one, other);
        }
        let asked = self.essential(&sig.essentials[0]).substitute(&binding);
        let said = self.prove_essential(&asked, &Rpn::default(), &Facts::new())?;
        let Built(said) = said else {
            return self.class_renamed_within(one, other);
        };
        Ok(Some(self.b.ap(lemma, &self.spelt(&binding), &[&said])))
    }

    /// `class_renamed` where a class inside either binds the letter the
    /// renaming goes to: `( i e. NN |-> ( ( n e. NN |-> B ) ` i ) )` to `( n
    /// e. NN |-> ( ( n e. NN |-> B ) ` n ) )`. The inner classes are moved
    /// to a letter nothing holds, on both sides, the outer letter renamed
    /// between them, and the three joined; None where a step does not go.
    pub(super) fn renamed_past_inner(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let Some(to) = other.children()[0].variable().map(str::to_string) else {
            return Ok(None);
        };
        let Some(spare) = self.unheld(&[one, other]) else {
            return Ok(None);
        };
        let one_moved = inner_moved(one, &to, &spare);
        let other_moved = inner_moved(other, &to, &spare);
        if self.rpn(&one_moved) == self.rpn(one)
            && self.rpn(&other_moved) == self.rpn(other)
        {
            return Ok(None);
        }
        let first = if self.rpn(&one_moved) == self.rpn(one) {
            None
        } else {
            let Some(p) = self.class_alpha(one, &one_moved)? else {
                return Ok(None);
            };
            Some(p)
        };
        let Some(middle) = self.class_renamed(&one_moved, &other_moved)? else {
            return Ok(None);
        };
        let last = if self.rpn(&other_moved) == self.rpn(other) {
            None
        } else {
            let Some(p) = self.class_alpha(&other_moved, other)? else {
                return Ok(None);
            };
            Some(p)
        };
        let (a, b, c, d) = (
            self.rpn(one),
            self.rpn(&one_moved),
            self.rpn(&other_moved),
            self.rpn(other),
        );
        let mut made = middle;
        if let Some(first) = first {
            made = self.b.ap(
                "eqtri",
                &binds! {"A" => &a, "B" => &b, "C" => &c},
                &[&first, &made],
            );
        }
        if let Some(last) = last {
            made = self.b.ap(
                "eqtri",
                &binds! {"A" => &a, "B" => &c, "C" => &d},
                &[&made, &last],
            );
        }
        Ok(Some(made))
    }
}
