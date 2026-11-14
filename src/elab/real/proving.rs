//! Real arithmetic, facts and what is within bounds.

use super::*;

impl<'a> Elaborator<'a> {
    /// A step citing `real arithmetic`.
    pub fn real_arithmetic(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what = format!("step {} claims {}", step.number, step.claim.text());
        self.real_fact(term, scope, facts, &what).map(Built)
    }

    /// A closed fact about square roots of rationals, worked out and then
    /// proved; `what` says where it was asked, as the page writes it.
    pub fn real_fact(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
    ) -> Checked<Proof> {
        let goal = self.to_term(term);
        // A claim of several sentences, `cos(π/2) = 0. sin(π/2) = 1.`, is
        // each of them worked out, as the checker decides each.
        let parts = self.conjoined(&goal, scope, &mut |me, one| {
            let one = me.rpn(one);
            me.real_fact(&one, scope, facts, what).map(Built)
        })?;
        if let Some(Built(p)) = parts {
            return Ok(p);
        }
        if let Some(pairs) = pairs::relation(&goal) {
            return self.real_pairs(&pairs, &goal, scope, facts, what);
        }
        match reals::decide_closed(&goal) {
            Built(Verdict::Holds(true)) => {}
            other => return Err(self.real_unshown(other, what)),
        }
        let proved = match self.roots_known(&goal, scope, facts)? {
            Built(known) => self.real_proved(&goal, scope, &known)?,
            Declined(d) => Declined(d),
        };
        match proved {
            Built(p) => Ok(p),
            Declined(d) => Err(self.defect(
                self.at,
                format!(
                    "{what}, which is true, and real arithmetic cannot show it yet: {}; cite a theorem that states it",
                    d.reason()
                ),
            )),
        }
    }

    /// Two pairs of closed real terms, compared coordinate by coordinate
    /// (`METHODS.md`, Pairs): both coordinates' equations, or the
    /// difference at the first coordinate whose equation is false.
    pub(super) fn real_pairs(
        &mut self,
        pairs: &PairRelation,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
    ) -> Checked<Proof> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let equation = self.rpn(&pairs.equation(at));
                proved.push(self.real_fact(&equation, scope, facts, what)?);
            }
            return Ok(self.pairs_equal(pairs, scope, &proved[0], &proved[1]));
        }
        let Some(at) = pairs.apart_at(&mut real_equal) else {
            return Err(self.real_unshown(reals::decide_closed(goal), what));
        };
        let denial = self.rpn(&pairs.denial(at));
        let apart = self.real_fact(&denial, scope, facts, what)?;
        let members = self.number_members(pairs, scope, facts)?;
        Ok(self.pairs_apart(pairs, scope, at, &apart, &members))
    }

    /// The defect for a claim real arithmetic did not find true.
    pub(super) fn real_unshown(&self, verdict: Route<Verdict>, what: &str) -> Problem {
        let message = match verdict {
            Declined(_) => format!("{what}, which {}", reals::UNREAD),
            Built(Verdict::Holds(false)) => format!("{what}, which is false"),
            Built(Verdict::Unworked(why)) => format!("{what}, which {why}"),
            Built(Verdict::Undecided(why)) => {
                format!("{what}, which {why}{}", reals::NOT_DECIDED_HERE)
            }
            Built(Verdict::Holds(true)) => unreachable!("a true claim is proved"),
        };
        self.defect(self.at, message)
    }

    /// The facts, with √p ∈ ℂ and √p ∈ ℝ for each prime p under a root of
    /// the claim, and the same of π, e and each ln p its values hold: what
    /// the normaliser and a membership ask of each atom.
    pub(super) fn roots_known(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Facts>> {
        let known = facts.copy();
        let atoms = atoms_under(goal).into_iter().map(spelt_atom);
        let roots = primes_under(goal).into_iter().map(root_of_prime);
        for said in atoms.chain(roots).collect::<Vec<Rpn>>() {
            let term = self.to_term(&said);
            for system in ["cr", "cc"] {
                let within =
                    take!(self.real_within(&term, &t!(system), scope, facts)?);
                self.know(&known, t!(&said, system, "wcel"), within);
            }
        }
        Ok(Built(known))
    }

    /// ( scope -> t e. system ) for a square root, π, e or a logarithm that
    /// `real arithmetic` takes, in ℝ or ℂ: its membership said once
    /// (`READERS.md`). π is real (`pire`) and complex (`picn`), e real
    /// (`ere`), and the logarithm of a positive rational real (`relogcld`);
    /// a real one is complex (`recnd`).
    pub(in crate::elab) fn real_within(
        &mut self,
        t: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if surds::is_root(t) {
            return self.root_within(t, system, scope, facts);
        }
        let said = self.rpn(t);
        // A sine or cosine of a real angle is real.
        let trig = reals::Trig::of(t).map(|f| match f {
            reals::Trig::Sine => "resincld",
            reals::Trig::Cosine => "recoscld",
        });
        let real = match t.label() {
            _ if trig.is_some() => {
                let x = self.rpn(&t.children()[0]);
                let angle = self.membership(&x, "cr", scope, facts)?;
                self.b.ap(
                    trig.expect("a sine or cosine"),
                    &binds! {"ph" => scope, "A" => &x},
                    &[&angle],
                )
            }
            Some("cpi") => self.closed_law(&t!("cpi", "cr", "wcel"), "pire", scope),
            Some("ceu") => self.closed_law(&t!("ceu", "cr", "wcel"), "ere", scope),
            _ => {
                let x = self.rpn(&t.children()[0]);
                let positive = self.positive(&x, scope, facts)?;
                self.b
                    .ap("relogcld", &binds! {"ph" => scope, "A" => &x}, &[&positive])
            }
        };
        match system.alone() {
            Some("cr") => Ok(Built(real)),
            Some("cc") => Ok(Built(self.b.ap(
                "recnd",
                &binds! {"ph" => scope, "A" => &said},
                &[&real],
            ))),
            _ => Ok(Route::no("said once only in ℝ and ℂ")),
        }
    }

    /// ( scope -> |PQ| e. system ) for the distance between two points, in
    /// ℝ or ℂ: its membership said once (`READERS.md`). Each point is in ℂ
    /// by its sort, their difference too (`subcld`), and its absolute value
    /// is real (`abscld`); a real one is complex (`recnd`).
    pub(in crate::elab) fn distance_within(
        &mut self,
        t: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let said = self.rpn(t);
        let difference = &t.children()[0];
        let [p, q, _] = difference.children() else {
            return Ok(Route::no("not the absolute value of a difference"));
        };
        let (p, q) = (self.rpn(p), self.rpn(q));
        let first = self.point_membership(&p, scope, facts)?;
        let second = self.point_membership(&q, scope, facts)?;
        let apart = self.b.ap(
            "subcld",
            &binds! {"ph" => scope, "A" => &p, "B" => &q},
            &[&first, &second],
        );
        let real = self.b.ap(
            "abscld",
            &binds! {"ph" => scope, "A" => self.rpn(difference)},
            &[&apart],
        );
        match system.alone() {
            Some("cr") => Ok(Built(real)),
            Some("cc") => Ok(Built(self.b.ap(
                "recnd",
                &binds! {"ph" => scope, "A" => &said},
                &[&real],
            ))),
            _ => Ok(Route::no("said once only in ℝ and ℂ")),
        }
    }

    /// ( scope -> ∠PQR e. system ) for an angle at three points, in ℝ or ℂ:
    /// its membership said once (`READERS.md`). An angle is written only
    /// where its points are said to differ (`SYNTAX.md`, Formulas), so
    /// P ≠ Q and R ≠ Q are lines in scope or follow from one
    /// (`points_apart`), and `gangbnd3` puts the angle in ℝ; a real one is
    /// complex. The proof rests on those lines unnamed, as one resting on a
    /// letter's introduction does, and is sealed as a membership said once.
    pub(in crate::elab) fn angle_within(
        &mut self,
        t: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let said = self.rpn(t);
        let [from, to, _] = t.children()[0].children() else {
            return Ok(Route::no("not an angle"));
        };
        let (p, q, r) = (
            self.rpn(&from.children()[0]),
            self.rpn(&from.children()[1]),
            self.rpn(&to.children()[0]),
        );
        let Some(first) = self.points_apart(&p, &q, scope, facts)? else {
            return Ok(Route::no(
                "no line in scope says the angle's first point is not its vertex",
            ));
        };
        let Some(last) = self.points_apart(&r, &q, scope, facts)? else {
            return Ok(Route::no(
                "no line in scope says the angle's last point is not its vertex",
            ));
        };
        let in_plane = |x: &Rpn| t!(x, "cc", "wcel");
        let (pp, pq, pr) = (
            self.point_membership(&p, scope, facts)?,
            self.point_membership(&q, scope, facts)?,
            self.point_membership(&r, scope, facts)?,
        );
        let members = t!(in_plane(&p), in_plane(&q), in_plane(&r), "w3a");
        let points = self.b.ap(
            "3jca",
            &binds! {"ph" => scope, "ps" => in_plane(&p), "ch" => in_plane(&q), "th" => in_plane(&r)},
            &[&pp, &pq, &pr],
        );
        let differ = t!(t!(&p, &q, "wceq", "wn"), t!(&r, &q, "wceq", "wn"), "wa");
        let apart = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => t!(&p, &q, "wceq", "wn"), "ch" => t!(&r, &q, "wceq", "wn")},
            &[&first, &last],
        );
        let is_real = t!(&said, "cr", "wcel");
        let at_least_0 = t!("cc0", &said, "cle", "wbr");
        let law = self
            .b
            .ap("gangbnd3", &binds! {"A" => &p, "B" => &q, "C" => &r}, &[]);
        let bounds = self.b.ap(
            "sylc",
            &binds! {"ph" => scope, "ps" => &members, "ch" => &differ, "th" => t!(&is_real, &at_least_0, "wa")},
            &[&points, &apart, &law],
        );
        let real = self.b.ap(
            "simpld",
            &binds! {"ph" => scope, "ps" => &is_real, "ch" => &at_least_0},
            &[&bounds],
        );
        let proof = match system.alone() {
            Some("cr") => real,
            Some("cc") => {
                self.b
                    .ap("recnd", &binds! {"ph" => scope, "A" => &said}, &[&real])
            }
            _ => return Ok(Route::no("said once only in ℝ and ℂ")),
        };
        Ok(Built(self.seal(proof, &format!("{MEMBERSHIP}{said:?}"))))
    }

    /// ( scope -> f(x) e. system ) for the sine, cosine or exponential of
    /// x, from `real`, ( scope -> x e. RR ): in ℝ, and so in ℂ.
    pub(in crate::elab) fn applied_within(
        &mut self,
        t: &Term,
        real: &Proof,
        system: &Rpn,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        let said = self.rpn(t);
        let x = self.rpn(&t.children()[0]);
        let lemma = match reals::Trig::of(t) {
            Some(reals::Trig::Sine) => "resincld",
            Some(reals::Trig::Cosine) => "recoscld",
            None => "reefcld",
        };
        let value = self
            .b
            .ap(lemma, &binds! {"ph" => scope, "A" => &x}, &[real]);
        match system.alone() {
            Some("cr") => Ok(Built(value)),
            Some("cc") => Ok(Built(self.b.ap(
                "recnd",
                &binds! {"ph" => scope, "A" => &said},
                &[&value],
            ))),
            _ => Ok(Route::no("said once only in ℝ and ℂ")),
        }
    }

    /// ( scope -> -. a = b ) from what `facts` says: a line saying a ≠ b
    /// either way round, a part of a line that is a conjunction, as a
    /// triangle's three differences are, or what a betweenness or a side of
    /// a line says through the lemma that reads it (`APART_LEMMAS`), a point
    /// off a line once more. None where nothing says it. The angle route
    /// asks it of the whole scope (`points_apart`).
    pub(in crate::elab) fn apart_held(
        &mut self,
        a: &Rpn,
        b: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (x, y) in [(a, b), (b, a)] {
            if let Some(p) = self.held(facts, &t!(x, y, "wceq", "wn"), scope)? {
                return Ok(Some(self.denial_as(p, x, y, a, b, scope)));
            }
            if let Some(p) = self.held(facts, &t!(x, y, "wne"), scope)? {
                let denied = self.b.ap(
                    "neneqd",
                    &binds! {"ph" => scope, "A" => x, "B" => y},
                    &[&p],
                );
                return Ok(Some(self.denial_as(denied, x, y, a, b, scope)));
            }
        }
        let mentions = |claim: &Rpn, x: &Rpn| {
            claim.tokens().windows(x.len()).any(|w| w == x.tokens())
        };
        let mut todo: Vec<(Rpn, Proof, usize)> = facts
            .entries()
            .into_iter()
            .filter(|(claim, _)| mentions(claim, a) && mentions(claim, b))
            .map(|(claim, proof)| (claim, proof, 0))
            .collect();
        while let Some((claim, proof, depth)) = todo.pop() {
            let node = self.to_term(&claim);
            let parts: Vec<Rpn> = node.children().iter().map(|c| self.rpn(c)).collect();
            match (node.label(), parts.as_slice()) {
                (Some("wn"), [_]) if node.children()[0].label() == Some("wceq") => {
                    let eq = &node.children()[0];
                    let (x, y) =
                        (self.rpn(&eq.children()[0]), self.rpn(&eq.children()[1]));
                    if (&x, &y) == (a, b) || (&x, &y) == (b, a) {
                        return Ok(Some(self.denial_as(proof, &x, &y, a, b, scope)));
                    }
                }
                (Some("wne"), [x, y]) if (x, y) == (a, b) || (x, y) == (b, a) => {
                    let denied = self.b.ap(
                        "neneqd",
                        &binds! {"ph" => scope, "A" => x, "B" => y},
                        &[&proof],
                    );
                    return Ok(Some(self.denial_as(denied, x, y, a, b, scope)));
                }
                (Some("wa"), [l, r]) => {
                    for (part, lemma) in [(l, "simpld"), (r, "simprd")] {
                        let taken = self.b.ap(
                            lemma,
                            &binds! {"ph" => scope, "ps" => l, "ch" => r},
                            &[&proof],
                        );
                        todo.push((part.clone(), taken, depth));
                    }
                }
                (Some("w3a"), [l, m, r]) => {
                    for (part, lemma) in [(l, "simp1d"), (m, "simp2d"), (r, "simp3d")] {
                        let taken = self.b.ap(
                            lemma,
                            &binds! {"ph" => scope, "ps" => l, "ch" => m, "th" => r},
                            &[&proof],
                        );
                        todo.push((part.clone(), taken, depth));
                    }
                }
                _ => {}
            }
            if depth < 2 {
                for lemma in APART_LEMMAS {
                    if let Some((reached, by)) =
                        self.through(lemma, &claim, &proof, scope, facts)?
                    {
                        todo.push((reached, by, depth + 1));
                    }
                }
            }
        }
        Ok(None)
    }

    /// `proof` of ( scope -> -. x = y ) as one of ( scope -> -. a = b ),
    /// where x, y is a, b or b, a.
    pub(super) fn denial_as(
        &mut self,
        proof: Proof,
        x: &Rpn,
        y: &Rpn,
        a: &Rpn,
        b: &Rpn,
        scope: &Rpn,
    ) -> Proof {
        if x == a && y == b {
            return proof;
        }
        let apart = self.b.ap(
            "neqned",
            &binds! {"ph" => scope, "A" => x, "B" => y},
            &[&proof],
        );
        let turned = self.b.ap(
            "necomd",
            &binds! {"ph" => scope, "A" => x, "B" => y},
            &[&apart],
        );
        self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => a, "B" => b},
            &[&turned],
        )
    }

    /// What the closed `lemma` reaches from `claim`, held by `proof`, the
    /// one antecedent of it that is no membership in ℂ: each of its points
    /// is in the plane by its sort. A lemma `( members -> ( claim -> Z ) )`
    /// or `( ( members /\ claim ) -> Z )`; None where `claim` does not fit
    /// it or leaves a letter of it open.
    pub(super) fn through(
        &mut self,
        lemma: &str,
        claim: &Rpn,
        proof: &Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<(Rpn, Proof)>> {
        let says = self.statement(lemma);
        let [members, rest] = says.children() else {
            return Ok(None);
        };
        if says.label() != Some("wi") {
            return Ok(None);
        }
        let (slot, reached, curried) = if rest.label() == Some("wi") {
            (rest.children()[0].clone(), rest.children()[1].clone(), true)
        } else if members.label() == Some("wa") {
            (members.children()[1].clone(), rest.clone(), false)
        } else {
            return Ok(None);
        };
        let variables = names_of(&says);
        let ground = self.to_term(claim);
        let Some(binding) = fit(&slot, &ground, &Binding::new(), &variables) else {
            return Ok(None);
        };
        if variables.iter().any(|v| !binding.contains_key(v)) {
            return Ok(None);
        }
        let law = self.b.ap(lemma, &self.spelt(&binding), &[]);
        let reached = self.rpn(&reached.substitute(&binding));
        let asked = if curried {
            members.substitute(&binding)
        } else {
            members.children()[0].substitute(&binding)
        };
        let Some(points) = self.points_in_plane(&asked, scope, facts)? else {
            return Ok(None);
        };
        let asked = self.rpn(&asked);
        let proved = if curried {
            self.b.ap(
                "sylc",
                &binds! {"ph" => scope, "ps" => &asked, "ch" => claim, "th" => &reached},
                &[&points, proof, &law],
            )
        } else {
            let both = t!(&asked, claim, "wa");
            let joined = self.b.ap(
                "jca",
                &binds! {"ph" => scope, "ps" => &asked, "ch" => claim},
                &[&points, proof],
            );
            self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &both, "ch" => &reached},
                &[&joined, &law],
            )
        };
        Ok(Some((reached, proved)))
    }

    /// ( scope -> members ) for a conjunction of memberships in ℂ, each of
    /// a point; None where a part is anything else.
    pub(super) fn points_in_plane(
        &mut self,
        members: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let parts: Vec<Rpn> = members.children().iter().map(|c| self.rpn(c)).collect();
        match (members.label(), members.children()) {
            (Some("wcel"), [x, set]) if self.rpn(set).alone() == Some("cc") => {
                let x = self.rpn(x);
                Ok(Some(self.point_membership(&x, scope, facts)?))
            }
            (Some("wa"), [l, r]) => {
                let (Some(lp), Some(rp)) = (
                    self.points_in_plane(l, scope, facts)?,
                    self.points_in_plane(r, scope, facts)?,
                ) else {
                    return Ok(None);
                };
                Ok(Some(self.b.ap(
                    "jca",
                    &binds! {"ph" => scope, "ps" => &parts[0], "ch" => &parts[1]},
                    &[&lp, &rp],
                )))
            }
            (Some("w3a"), [l, m, r]) => {
                let (Some(lp), Some(mp), Some(rp)) = (
                    self.points_in_plane(l, scope, facts)?,
                    self.points_in_plane(m, scope, facts)?,
                    self.points_in_plane(r, scope, facts)?,
                ) else {
                    return Ok(None);
                };
                Ok(Some(self.b.ap(
                    "3jca",
                    &binds! {"ph" => scope, "ps" => &parts[0], "ch" => &parts[1], "th" => &parts[2]},
                    &[&lp, &mp, &rp],
                )))
            }
            _ => Ok(None),
        }
    }

    /// ( scope -> P e. CC ) for an end of a distance: as the facts hold it,
    /// or, for a point a `let` line introduced, as its line said it, carried
    /// to `scope` and sealed as a membership said once, which a step rests on
    /// without naming its line; a proof of a standard form, which has no
    /// facts, reaches it only this way.
    pub(super) fn point_membership(
        &mut self,
        p: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let claim = t!(p, "cc", "wcel");
        if let Some(held) = self.held(facts, &claim, scope)? {
            return Ok(held);
        }
        let letter = self
            .names
            .iter()
            .find(|(name, kernel)| {
                *kernel == p && self.sorts_now.get(*name).is_some_and(|s| s.is("point"))
            })
            .map(|(name, _)| name.clone());
        if let Some(letter) = letter {
            let kept = self.introduced.get(&letter).cloned().unwrap_or_default();
            let lifted = kept
                .iter()
                .rev()
                .filter(|(said, _, _)| *said == claim)
                .find_map(|(_, proof, at)| self.lifted_to(&claim, proof, at, scope));
            if let Some(lifted) = lifted {
                return Ok(self.seal(lifted, &format!("{MEMBERSHIP}{letter}")));
            }
        }
        self.membership(p, "cc", scope, facts)
    }

    /// ( scope -> √x e. system ) for a root `real arithmetic` takes, in ℝ
    /// or ℂ: its membership said once (`READERS.md`). x is a rational of at
    /// least 0, which `arithmetic` says, and its root is real (`resqrtcld`),
    /// or complex (`sqrtcld`).
    pub(super) fn root_within(
        &mut self,
        root: &Term,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let x = self.rpn(&root.children()[0]);
        match system.alone() {
            Some("cr") => {
                let real = self.numeral_fact(&t!(&x, "cr", "wcel"), scope, facts)?;
                let above =
                    self.numeral_fact(&t!("cc0", &x, "cle", "wbr"), scope, facts)?;
                Ok(Built(self.b.ap(
                    "resqrtcld",
                    &binds! {"ph" => scope, "A" => &x},
                    &[&real, &above],
                )))
            }
            Some("cc") => {
                let complex = self.numeral_fact(&t!(&x, "cc", "wcel"), scope, facts)?;
                Ok(Built(self.b.ap(
                    "sqrtcld",
                    &binds! {"ph" => scope, "A" => &x},
                    &[&complex],
                )))
            }
            _ => Ok(Route::no("a root is said once only in ℝ and ℂ")),
        }
    }

    /// ( scope -> claim ) for a theorem of set.mm stating `claim` with no
    /// hypothesis, as `pire` states π ∈ ℝ.
    pub(in crate::elab) fn closed_law(
        &self,
        claim: &Rpn,
        label: &str,
        scope: &Rpn,
    ) -> Proof {
        self.b.ap(
            "a1i",
            &binds! {"ph" => claim, "ps" => scope},
            &[&self.step(label)],
        )
    }

    /// ( scope -> x e. RR+ ) for a closed x of numerals with a positive
    /// value: x ∈ ℝ and 0 < x by arithmetic (`elrpd`).
    pub(super) fn positive(
        &mut self,
        x: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let real = self.numeral_fact(&t!(x, "cr", "wcel"), scope, facts)?;
        let above = self.numeral_fact(&t!("cc0", x, "clt", "wbr"), scope, facts)?;
        Ok(self
            .b
            .ap("elrpd", &binds! {"ph" => scope, "A" => x}, &[&real, &above]))
    }

    /// A fact about numerals alone, which arithmetic proves.
    pub(super) fn numeral_fact(
        &mut self,
        claim: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let what = format!("real arithmetic asks {}", self.render(claim));
        self.closed_fact(claim, scope, facts, &what, None)
    }

    /// ( scope -> goal ) for a closed claim real arithmetic found true.
    pub(super) fn real_proved(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        let inner = if negated { &goal.children()[0] } else { goal };
        let kids = inner.children().to_vec();
        match (negated, inner.label(), kids.as_slice()) {
            (false, Some("wceq"), [a, b]) => {
                let left = take!(self.valued(a, scope, facts)?);
                let right = take!(self.valued(b, scope, facts)?);
                Ok(Built(self.b.ap(
                    "eqtr4d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &left.canon, "C" => self.rpn(b)},
                    &[&left.proof, &right.proof],
                )))
            }
            (false, Some("wne"), [a, b]) => self.real_apart(a, b, scope, facts),
            (true, Some("wceq"), [a, b]) => {
                let apart = take!(self.real_apart(a, b, scope, facts)?);
                Ok(Built(self.b.ap(
                    "neneqd",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => self.rpn(b)},
                    &[&apart],
                )))
            }
            (_, Some("wbr"), [a, b, relation])
                if matches!(relation.label(), Some("clt" | "cle")) =>
            {
                let strict = relation.label() == Some("clt");
                self.real_ordered(negated, a, b, strict, scope, facts)
            }
            _ => self.by_surd_values(goal, scope, facts),
        }
    }

    /// ( scope -> a =/= b ) for closed a and b of different values: a − b
    /// is the canon of the difference, which is not zero (`surd_apart`), and
    /// `subne0ad` turns that round.
    pub(super) fn real_apart(
        &mut self,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Difference { left, right, gap } =
            take!(self.difference(a, b, scope, facts)?);
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        let difference = t!(&sa, &sb, "cmin", "co");
        // The decider found the difference a surd or logarithms of primes.
        let canon_apart = match gap.value.as_surd() {
            Some(s) => take!(self.surd_apart(&gap.canon, &s, scope, facts)?),
            None => take!(self.ln_apart(&gap.canon, &gap.value, scope, facts)?),
        };
        let differs = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &difference, "B" => &gap.canon, "C" => "cc0"},
            &[&gap.proof, &canon_apart],
        );
        let a_cc = take!(self.valued_within(&sa, &left, "cc", scope, facts)?);
        let b_cc = take!(self.valued_within(&sb, &right, "cc", scope, facts)?);
        Ok(Built(self.b.ap(
            "subne0ad",
            &binds! {"ph" => scope, "A" => &sa, "B" => &sb},
            &[&a_cc, &b_cc, &differs],
        )))
    }

    /// a − b proved equal to the canon of its value: each side to its own
    /// canon, carried through the difference (`oveq12d`), and the
    /// difference of the canons to the canon of the difference.
    pub(super) fn difference(
        &mut self,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Difference>> {
        let left = take!(self.valued(a, scope, facts)?);
        let right = take!(self.valued(b, scope, facts)?);
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        let moved = self.b.ap(
            "oveq12d",
            &binds! {"ph" => scope, "A" => &sa, "B" => &left.canon, "C" => &sb, "D" => &right.canon, "F" => "cmin"},
            &[&left.proof, &right.proof],
        );
        let between = t!(&left.canon, &right.canon, "cmin", "co");
        let value = left.value.minus(&right.value);
        let worked = take!(self.made_canon(&between, &value, scope, facts)?);
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => t!(&sa, &sb, "cmin", "co"), "B" => &between, "C" => &worked.canon},
            &[&moved, &worked.proof],
        );
        Ok(Built(Difference {
            left,
            right,
            gap: Valued {
                value,
                canon: worked.canon,
                proof,
            },
        }))
    }

    /// ( scope -> said e. system ) for a term proved equal to its canon,
    /// which is in ℂ, or real, by the roots and atoms it is built from.
    pub(super) fn valued_within(
        &mut self,
        said: &Rpn,
        valued: &Valued,
        system: &str,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let canon_in = match system {
            "cc" => take!(self.in_cc(&valued.canon, scope, facts)?),
            _ => self.membership(&valued.canon, system, scope, facts)?,
        };
        Ok(Built(self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => said, "B" => &valued.canon, "C" => system},
            &[&valued.proof, &canon_in],
        )))
    }

    /// ( scope -> goal ) for an order a < b or a ≤ b found true, or the
    /// denial of one: the denial of a < b is b ≤ a (`lenltd`), and of a ≤ b
    /// is b < a (`ltnled`).
    pub(super) fn real_ordered(
        &mut self,
        negated: bool,
        a: &Term,
        b: &Term,
        strict: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if !negated {
            let held = match strict {
                true => take!(self.real_below(a, b, scope, facts)?),
                false => take!(self.real_at_most(a, b, scope, facts)?),
            };
            return Ok(Built(held.proof));
        }
        // not a < b is b ≤ a, and not a ≤ b is b < a.
        let held = match strict {
            true => take!(self.real_at_most(b, a, scope, facts)?),
            false => take!(self.real_below(b, a, scope, facts)?),
        };
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        Ok(Built(self.denied(scope, &sb, &sa, &held, !strict)))
    }

    /// ( scope -> a <_ b ): a = b where the values are equal (`eqled`), and
    /// a < b weakened otherwise (`ltled`).
    pub(super) fn real_at_most(
        &mut self,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Ordered>> {
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        let equal = matches!(
            (reals::closed_value(a), reals::closed_value(b)),
            (Built(reals::Value::Exact(x)), Built(reals::Value::Exact(y))) if x == y
        );
        if !equal {
            let below = take!(self.real_below(a, b, scope, facts)?);
            let proof = self.b.ap(
                "ltled",
                &binds! {"ph" => scope, "A" => &sa, "B" => &sb},
                &[&below.left_real, &below.right_real, &below.proof],
            );
            return Ok(Built(Ordered { proof, ..below }));
        }
        let left = take!(self.valued(a, scope, facts)?);
        let right = take!(self.valued(b, scope, facts)?);
        let left_real = take!(self.valued_within(&sa, &left, "cr", scope, facts)?);
        let right_real = take!(self.valued_within(&sb, &right, "cr", scope, facts)?);
        let same = self.b.ap(
            "eqtr4d",
            &binds! {"ph" => scope, "A" => &sa, "B" => &left.canon, "C" => &sb},
            &[&left.proof, &right.proof],
        );
        let proof = self.b.ap(
            "eqled",
            &binds! {"ph" => scope, "A" => &sa, "B" => &sb},
            &[&left_real, &same],
        );
        Ok(Built(Ordered {
            proof,
            left_real,
            right_real,
        }))
    }

    /// ( scope -> a < b ) for a below b: b − a is proved equal to the canon
    /// of its value, which is above 0 (`canon_positive`), and `posdifd`
    /// turns that round.
    pub(super) fn real_below(
        &mut self,
        a: &Term,
        b: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Ordered>> {
        let Difference { left, right, gap } =
            take!(self.difference(b, a, scope, facts)?);
        let above = take!(self.canon_positive(&gap.canon, &gap.value, scope, facts)?);
        let (sa, sb) = (self.rpn(a), self.rpn(b));
        let between = t!(&sb, &sa, "cmin", "co");
        let carried = self.b.ap(
            "breqtrrd",
            &binds! {"ph" => scope, "A" => "cc0", "B" => &gap.canon, "C" => &between, "R" => "clt"},
            &[&above, &gap.proof],
        );
        // The difference was taken as b − a, so its left side is b.
        let a_real = take!(self.valued_within(&sa, &right, "cr", scope, facts)?);
        let b_real = take!(self.valued_within(&sb, &left, "cr", scope, facts)?);
        let iff = self.b.ap(
            "posdifd",
            &binds! {"ph" => scope, "A" => &sa, "B" => &sb},
            &[&a_real, &b_real],
        );
        let proof = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(&sa, &sb, "clt", "wbr"), "ch" => t!("cc0", &between, "clt", "wbr")},
            &[&carried, &iff],
        );
        Ok(Built(Ordered {
            proof,
            left_real: a_real,
            right_real: b_real,
        }))
    }
}
