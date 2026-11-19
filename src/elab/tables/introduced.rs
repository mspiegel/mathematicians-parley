//! Introduced memberships, intervals and function values.

use super::*;
use crate::citing;

impl<'a> Elaborator<'a> {
    /// `said ∈ system` as the page says it once (`READERS.md`, membership said
    /// once), or a decline. Whether and why is `citing::reason`'s, the rule
    /// the checker reads too: a line the step names stating it; a numeral; a
    /// letter in the number system its introducing line names, carried up
    /// `WITHIN`; a sum said once; a distance between two points, in ℝ or ℂ;
    /// an angle at three points, in ℝ or ℂ, from the lines in scope saying
    /// they differ (`angle_within`); a sine, cosine or exponential of a real
    /// argument, in ℝ or ℂ; or a term built from those by +, −, ·,
    /// negation, a power to a numeral or to a letter in ℕ or ℕ₀, and a
    /// quotient whose divisor's `≠ 0` the step writes. What is built here is
    /// the proof of the reason it gives. A letter's membership is sealed as
    /// `membership@<letter>`, which a step rests on without naming it, as it
    /// does a sort; nothing but a membership in a number system is ever proved
    /// from it, since only this route reads it.
    pub fn introduced_membership(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Some(within) = system.alone().and_then(System::of_label) else {
            return Ok(Route::no("not a number system"));
        };
        if self.beyond_once > 0 {
            return Ok(Route::no("a part of a fact the page writes"));
        }
        // Whether and why is the rule both tools read (`citing::reason`);
        // what is built here is the proof of the reason it gives.
        let term = self.to_term(said);
        let mut ask = BuildOnce {
            me: self,
            scope,
            facts,
            problem: None,
        };
        let reason = citing::reason(&mut ask, &term, within);
        if let Some(problem) = ask.problem {
            return Err(problem);
        }
        let Some(reason) = reason else {
            return Ok(Route::no(
                "not a numeral, an introduced letter, or built from them",
            ));
        };
        match reason {
            OnceReason::Numeral => {
                let goal = self.to_term(&t!(said, system, "wcel"));
                self.numeral_within(&goal, scope, facts)
            }
            OnceReason::Letter => {
                let (letter, set) = self
                    .introduced_in(said)
                    .expect("a letter the walk found introduced");
                self.letter_within(said, &letter, &set, system, scope, facts)
            }
            OnceReason::Real => self.real_within(&term, system, scope, facts),
            OnceReason::Distance => self.distance_within(&term, system, scope, facts),
            OnceReason::Angle => self.angle_within(&term, system, scope, facts),
            // The argument is real by the reason given, and the sine, cosine
            // or exponential of a real number is real.
            OnceReason::Applied(_) => {
                let argument = self.rpn(&term.children()[0]);
                let real = take!(self.introduced_membership(
                    &argument,
                    &t!("cr"),
                    scope,
                    facts
                )?);
                self.applied_within(&term, &real, system, scope)
            }
            // n! of an n in ℕ₀ is in ℕ (`faccld`), carried to `system`.
            OnceReason::Factorial(_) => {
                let n = self.rpn(&term.children()[0]);
                let whole =
                    take!(self.introduced_membership(&n, &t!("cn0"), scope, facts)?);
                let made =
                    self.b
                        .ap("faccld", &binds! {"ph" => scope, "N" => &n}, &[&whole]);
                self.carried_within(said, "cn", system, made, scope)
            }
            // |x| of an integer is in ℕ₀ (`nn0abscl`), and of a complex
            // number in ℝ (`abscld`), carried to `system`.
            OnceReason::Absolute { within, .. } => {
                let x = self.rpn(&term.children()[0]);
                if within == System::Z {
                    let integer = take!(self.introduced_membership(
                        &x,
                        &t!("cz"),
                        scope,
                        facts
                    )?);
                    let law = self.b.ap("nn0abscl", &binds! {"A" => &x}, &[]);
                    let made = self.b.ap(
                        "syl",
                        &binds! {"ph" => scope, "ps" => t!(&x, "cz", "wcel"),
                        "ch" => t!(said, "cn0", "wcel")},
                        &[&integer, &law],
                    );
                    self.carried_within(said, "cn0", system, made, scope)
                } else {
                    let complex = take!(self.introduced_membership(
                        &x,
                        &t!("cc"),
                        scope,
                        facts
                    )?);
                    let made = self.b.ap(
                        "abscld",
                        &binds! {"ph" => scope, "A" => &x},
                        &[&complex],
                    );
                    self.carried_within(said, "cr", system, made, scope)
                }
            }
            // A part that a line the step names puts in a number system is
            // a number there, carried up to `system`: N(n) + 1 ∈ ℝ where a
            // line says N(n) ∈ ℝ.
            OnceReason::Stated => {
                match self.stated_within(said, system, scope, facts)? {
                    Some(found) => Ok(Built(found)),
                    None => Ok(Route::no("no line the step names states it")),
                }
            }
            // A sum said once by its terms is in ℝ or ℂ by the sum's lemma,
            // its terms read from the scope at each index.
            OnceReason::Sum => self.summed(&term, system, scope, facts, None),
            // A divisor's `≠ 0` is the page's, from what the step names.
            OnceReason::Built(_) => {
                let named = facts.clone();
                self.built(
                    said,
                    system,
                    scope,
                    &mut |me, part, into| {
                        me.introduced_membership(part, into, scope, facts)
                    },
                    Some(&mut |me, divisor| me.divisor_written(divisor, scope, &named)),
                )
            }
        }
    }

    /// Keep, for each letter let into a number system and not yet kept, its
    /// membership as `facts` hold it under `scope`, the scope its line opens:
    /// what `introduced_membership` carries to any scope inside it.
    pub fn note_introduced(&mut self, scope: &Rpn, facts: &Facts) -> Checked<()> {
        // A point is a complex number in set.mm, which its `let` line says;
        // a distance between two points is real by that (`distance_within`).
        let points = self
            .sorts_now
            .iter()
            .filter(|(_, sort)| sort.is("point"))
            .map(|(letter, _)| (letter.clone(), t!("cc")));
        let letters: Vec<(String, Rpn)> =
            self.sets.clone().into_iter().chain(points).collect();
        for (letter, set) in letters {
            if self.introduced_system(&set).is_none() {
                continue;
            }
            let Some(kernel) = self.names.get(&letter).cloned() else {
                continue;
            };
            let claim = t!(kernel, set, "wcel");
            let kept = self.introduced.get(&letter).is_some_and(|all| {
                all.iter().any(|(c, _, at)| *c == claim && at == scope)
            });
            if kept {
                continue;
            }
            if let Some(proof) = self.held(facts, &claim, scope)? {
                self.introduced.entry(letter).or_default().push((
                    claim,
                    proof,
                    scope.clone(),
                ));
            }
        }
        Ok(())
    }

    /// `wanted` where it is a membership the page says once, or several
    /// joined by "and", as a lemma may ask its side conditions together; a
    /// decline for anything else.
    pub fn said_once_proof(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if wanted.label() == Some("wcel") && wanted.children().len() == 2 {
            let (said, system) = (
                self.rpn(&wanted.children()[0]),
                self.rpn(&wanted.children()[1]),
            );
            return self.introduced_membership(&said, &system, scope, facts);
        }
        if wanted.label() == Some("wf") && wanted.children().len() == 3 {
            return self.declared_type(wanted, scope, facts);
        }
        let joined = self.conjoined(wanted, scope, &mut |me, one| {
            me.said_once_proof(one, scope, facts)
        })?;
        Ok(joined.unwrap_or_else(|| Route::no("not a membership")))
    }

    /// `F : A --> C` for a function a `let` declares F : A --> B, by the
    /// reason `citing::codomain_reason` gives the checker too: B is C, a
    /// number system inside C (`rules::INSIDE`), or a set a `let` puts
    /// inside C, the type widened by `fssd`. The declaration says the type
    /// once, so the step need not name its line.
    pub(super) fn declared_type(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let [domain, codomain, f] = wanted.children() else {
            return Ok(Route::no("not a function's type"));
        };
        let (domain, codomain, f) = (self.rpn(domain), self.rpn(codomain), self.rpn(f));
        let Some(letter) = self
            .names
            .iter()
            .find(|(_, kernel)| **kernel == f)
            .map(|(name, _)| name.clone())
        else {
            return Ok(Route::no("not a declared function"));
        };
        // The type and the parts are what `let` lines say, and nothing else
        // in scope (`said_by_lets`), as the checker reads them.
        let facts = &self.said_by_lets(facts);
        let mut declared: Vec<Rpn> = Vec::new();
        let mut parts: Vec<(Rpn, Rpn)> = Vec::new();
        for (claim, _) in facts.entries() {
            let said = self.to_term(&claim);
            match (said.label(), said.children()) {
                (Some("wf"), [a, b, g])
                    if self.rpn(a) == domain && self.rpn(g) == f =>
                {
                    declared.push(self.rpn(b));
                }
                (Some("wss"), [small, big]) => {
                    parts.push((self.rpn(small), self.rpn(big)))
                }
                (Some("wcel"), [small, power]) if power.label() == Some("cpw") => {
                    if let [big] = power.children() {
                        parts.push((self.rpn(small), self.rpn(big)));
                    }
                }
                _ => {}
            }
        }
        for given in declared {
            let ask = KernelCodomains { parts: &parts };
            let Some(reason) = citing::codomain_reason(&ask, &given, &codomain) else {
                continue;
            };
            let Some(typed) =
                self.held(facts, &t!(&domain, &given, &f, "wf"), scope)?
            else {
                continue;
            };
            let within = match reason {
                CodomainReason::Same => {
                    return Ok(Built(
                        self.seal(typed, &format!("{MEMBERSHIP}{letter}")),
                    ));
                }
                CodomainReason::Systems { small, big } => {
                    let Some(inside) = rules::INSIDE
                        .iter()
                        .find(|i| i.small == small.label() && i.big == big.label())
                    else {
                        continue;
                    };
                    let closed = self.b.ap(inside.lemma, &binds! {}, &[]);
                    pf!(self.b; t!(&given, &codomain, "wss"), scope, closed, "a1i")
                }
                CodomainReason::Part => {
                    let subset = t!(&given, &codomain, "wss");
                    match self.held(facts, &subset, scope)? {
                        Some(p) => p,
                        None => {
                            let member = t!(&given, t!(&codomain, "cpw"), "wcel");
                            let Some(p) = self.held(facts, &member, scope)? else {
                                continue;
                            };
                            self.b.ap(
                                "elpwid",
                                &binds! {"ph" => scope, "A" => &given, "B" => &codomain},
                                &[&p],
                            )
                        }
                    }
                }
            };
            let wider = self.b.ap(
                rules::WIDER_TYPE,
                &binds! {"ph" => scope, "A" => &domain, "B" => &given, "C" => &codomain, "F" => &f},
                &[&typed, &within],
            );
            return Ok(Built(self.seal(wider, &format!("{MEMBERSHIP}{letter}"))));
        }
        Ok(Route::no("no declared type whose codomain lies inside"))
    }

    /// `said ∈ system` from a line the step names saying `said` is in a
    /// number system inside `system`, carried up `WITHIN`; None where no
    /// such line says it.
    pub(super) fn stated_within(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (_, set) in rules::SYSTEM_OF {
            let Some(held) = self.held(facts, &t!(said, set, "wcel"), scope)? else {
                continue;
            };
            if let Built(proof) = self.carried_within(said, set, system, held, scope)? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// Keep the sums the step now being elaborated writes that the page
    /// says are numbers once (`CheckedTheorem::said_sums`), as kernel terms.
    pub fn note_said_sums(&mut self) -> Checked<()> {
        let nodes = self
            .step_now
            .and_then(|i| self.checked.said_sums.get(i))
            .cloned()
            .unwrap_or_default();
        let mut sums = BTreeSet::new();
        for node in &nodes {
            sums.insert(self.term(node)?);
        }
        self.said_sums = sums;
        Ok(())
    }

    /// The letter whose kernel term is `said`, and the number system the
    /// line introducing it put it in; None for anything else. A point is a
    /// complex number in set.mm, which its `let` line says (`note_introduced`
    /// keeps it so), as a lemma's side condition asks of a distance's ends.
    pub(super) fn introduced_in(&self, said: &Rpn) -> Option<(String, Rpn)> {
        let point = self.names.iter().find(|(name, kernel)| {
            *kernel == said && self.sorts_now.get(*name).is_some_and(|s| s.is("point"))
        });
        if let Some((letter, _)) = point {
            return Some((letter.clone(), t!("cc")));
        }
        self.sets.iter().find_map(|(letter, set)| {
            let ours = self.names.get(letter).is_some_and(|k| k == said);
            let counted = self.introduced_system(set).is_some();
            (ours && counted).then(|| (letter.clone(), set.clone()))
        })
    }

    /// The number system a letter introduced in `set` is in first: the
    /// system itself, the one a range lies in (`range_system`), or the one
    /// an interval lies in (`interval_within`), each with points taken out
    /// too, as the checker reads it (`citing::once::set_system`): a member
    /// of ℝ ∖ {2} is in ℝ. None for any other set.
    pub(super) fn introduced_system(&self, set: &Rpn) -> Option<&'static str> {
        if let Some(from) = self.taken_from(set) {
            return self.introduced_system(&from);
        }
        if let Some((label, _)) = set
            .alone()
            .and_then(|s| rules::SYSTEMS.iter().find(|(label, _)| *label == s))
        {
            return Some(label);
        }
        if let Some((system, _)) = self.range_system(set) {
            return Some(system);
        }
        self.interval_within(set).map(|i| i.system)
    }

    /// The row of `rules::INTERVAL_WITHIN` for an interval (a, b) or
    /// [a, b], or one with points taken out, (a, b) ∖ {c}, which the
    /// checker reads as well; None for a set that is no interval.
    pub(super) fn interval_within(
        &self,
        set: &Rpn,
    ) -> Option<&'static rules::IntervalWithin> {
        if let Some(from) = self.taken_from(set) {
            return self.interval_within(&from);
        }
        let interval = self.to_term(set);
        if interval.variable().is_some()
            || interval.label() != Some("co")
            || interval.children().len() != 3
        {
            return None;
        }
        let operation = self.rpn(&interval.children()[2]);
        rules::INTERVAL_WITHIN
            .iter()
            .find(|i| operation.alone() == Some(i.operation))
    }

    /// The set a difference A ∖ B takes from, A; None for a set that is no
    /// difference.
    pub(super) fn taken_from(&self, set: &Rpn) -> Option<Rpn> {
        let difference = self.to_term(set);
        if difference.variable().is_some()
            || difference.label() != Some("cdif")
            || difference.children().len() != 2
        {
            return None;
        }
        Some(self.rpn(&difference.children()[0]))
    }

    /// The number system a range {a, …, b} puts its members in, and the
    /// lemma saying so (`rules::RANGE_WITHIN`, which the checker reads as
    /// well): ℕ from 1, ℕ₀ from 0, ℤ from anywhere. None for a set that is
    /// no range.
    pub(crate) fn range_system(
        &self,
        set: &Rpn,
    ) -> Option<(&'static str, &'static str)> {
        let range = self.to_term(set);
        if range.variable().is_some()
            || range.label() != Some("co")
            || range.children().len() != 3
            || self.rpn(&range.children()[2]).alone() != Some("cfz")
        {
            return None;
        }
        let start = self.rpn(&range.children()[0]);
        rules::RANGE_WITHIN
            .iter()
            .find(|row| row.first.is_none() || row.first == start.alone())
            .map(|row| (row.system, row.lemma))
    }

    /// `said ∈ system` for a letter introduced in `set`, from the scope's
    /// copy of its introducing line, sealed as `membership@<letter>` and
    /// carried up `WITHIN` one lemma at a time.
    pub(super) fn letter_within(
        &mut self,
        said: &Rpn,
        letter: &str,
        set: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let base = self.introduced_system(set).unwrap_or_default();
        if rules::within_path(Some(base), system.alone()).is_none() {
            return Ok(Route::no(format!("{set} is not inside {system}")));
        }
        let claim = t!(said, set, "wcel");
        let mut held = self.held(facts, &claim, scope)?;
        if held.is_none() {
            let all = self.introduced.get(letter).cloned().unwrap_or_default();
            held = all
                .iter()
                .rev()
                .filter(|(kept, _, _)| *kept == claim)
                .find_map(|(_, proof, at)| self.lifted_to(&claim, proof, at, scope));
        }
        let Some(held) = held else {
            return Ok(Route::no("the introducing line is not in scope"));
        };
        let mut proof = self.seal(held, &format!("{MEMBERSHIP}{letter}"));
        // A member of S ∖ {c} is a member of S first, where S is a number
        // system or a range; an interval's points taken out are the
        // interval's own (`out_of_interval`).
        let mut set = set.clone();
        while let Some(from) = self.taken_from(&set) {
            if self.interval_within(&from).is_some() {
                break;
            }
            let removed = self.rpn(&self.to_term(&set).children()[1]);
            let law = self.b.ap(
                "eldifi",
                &binds! {"A" => said, "B" => &from, "C" => &removed},
                &[],
            );
            proof = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(said, &set, "wcel"), "ch" => t!(said, &from, "wcel")},
                &[&proof, &law],
            );
            set = from;
        }
        let set = &set;
        let claim = t!(said, set, "wcel");
        // A range's or an interval's member is in the system the set lies
        // in first; any other set a letter is let into is a number system's
        // label.
        let range = self.range_system(set);
        let interval = self.interval_within(set);
        if let Some((inside, lemma)) = range {
            let says = self.statement(lemma);
            let Some(binding) = fit(
                &says.children()[0],
                &self.to_term(&claim),
                &Binding::new(),
                &names_of(&says),
            ) else {
                return Ok(Route::no(format!("{lemma} does not take {claim}")));
            };
            let law = self.b.ap(lemma, &self.spelt(&binding), &[]);
            proof = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, inside, "wcel")},
                &[&proof, &law],
            );
        }
        if let Some(interval) = interval {
            proof =
                take!(self.out_of_interval(said, set, interval, proof, scope, facts)?);
        }
        self.carried_within(said, base, system, proof, scope)
    }

    /// ( scope -> said e. system ) from `held`, ( scope -> said e. set ),
    /// where `set` is an interval and `system` the one `interval` puts it
    /// in. The lemma takes the membership alone, or the interval's two ends
    /// in the system it asks and then the membership; each end is a
    /// membership said once, as a lemma's side condition is
    /// (`introduced_membership`), and a decline where one is not.
    pub(super) fn out_of_interval(
        &mut self,
        said: &Rpn,
        set: &Rpn,
        interval: &rules::IntervalWithin,
        held: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let claim = t!(said, set, "wcel");
        // A member of (a, b) ∖ {c} is a member of (a, b) first.
        if let Some(from) = self.taken_from(set) {
            let removed = self.rpn(&self.to_term(set).children()[1]);
            let law = self.b.ap(
                "eldifi",
                &binds! {"A" => said, "B" => &from, "C" => &removed},
                &[],
            );
            let held = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, &from, "wcel")},
                &[&held, &law],
            );
            return self.out_of_interval(said, &from, interval, held, scope, facts);
        }
        let gives = t!(said, interval.system, "wcel");
        let says = self.statement(interval.lemma);
        let Some(ends) = interval.ends else {
            let Some(binding) = fit(
                &says.children()[0],
                &self.to_term(&claim),
                &Binding::new(),
                &names_of(&says),
            ) else {
                return Ok(Route::no(format!(
                    "{} does not take {claim}",
                    interval.lemma
                )));
            };
            let law = self.b.ap(interval.lemma, &self.spelt(&binding), &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => &gives},
                &[&held, &law],
            )));
        };
        // ( ( a e. ends /\ b e. ends /\ said e. set ) -> said e. system ),
        // its antecedent a three-way conjunction, the membership last.
        let given = &says.children()[0];
        let Some(binding) = given.children().get(2).and_then(|member| {
            fit(
                member,
                &self.to_term(&claim),
                &Binding::new(),
                &names_of(&says),
            )
        }) else {
            return Ok(Route::no(format!(
                "{} does not take {claim}",
                interval.lemma
            )));
        };
        let bounds = self.to_term(set);
        let [low, high, _] = bounds.children() else {
            return Ok(Route::no(format!("{set} has no two ends")));
        };
        let (low, high) = (self.rpn(low), self.rpn(high));
        let ends_in = t!(ends);
        let low_in = take!(self.introduced_membership(&low, &ends_in, scope, facts)?);
        let high_in = take!(self.introduced_membership(&high, &ends_in, scope, facts)?);
        let law = self.b.ap(interval.lemma, &self.spelt(&binding), &[]);
        Ok(Built(self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(low, ends, "wcel"),
            "ch" => t!(high, ends, "wcel"), "th" => &claim, "ta" => &gives},
            &[&low_in, &high_in, &held, &law],
        )))
    }

    /// ( scope -> said e. system ) from ( scope -> said e. set ), along the
    /// sets `rules::WITHIN` says lie one inside the next, a lemma for each.
    pub(crate) fn carried_within(
        &mut self,
        said: &Rpn,
        set: &str,
        system: &Rpn,
        mut proof: Proof,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        // `WITHIN` is keyed by a number system's label; a class of more than
        // one token is none of them.
        let target = system.alone().unwrap_or_default();
        let mut at: &str = set;
        while at != target {
            let row = lookup(rules::WITHIN, at).unwrap_or(&[]);
            let next = row
                .iter()
                .find(|(to, _)| *to == target)
                .or_else(|| {
                    row.iter().find(|(to, _)| {
                        rules::within_path(Some(to), Some(target)).is_some()
                    })
                })
                .copied();
            let Some((to, lemma)) = next else {
                return Ok(Route::no(format!("{at} is not inside {system}")));
            };
            let push = self.sig(lemma).push()[0].to_string();
            let law = self.b.ap(lemma, &binds! {push => said}, &[]);
            proof = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(said, at, "wcel"),
                "ch" => t!(said, to, "wcel")},
                &[&proof, &law],
            );
            at = to;
        }
        Ok(Built(proof))
    }

    /// One part of a compound, in a number system, or a decline.
    ///
    /// The step's own line first, then that line carried by one lemma, then
    /// the part built in turn if it is a compound. A numeral is the
    /// library's. What the scope holds is last, and only exactly: it is a
    /// line the page wrote, and a step using it without naming it is what
    /// provenance is there to see.
    pub fn part(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let want = t!(said, system, "wcel");
        let found = self.held(facts, &want, scope)?;
        if let Some(f) = &found {
            if from_requires(f) {
                return Ok(Built(f.clone()));
            }
        }
        if let Some(w) = self.written_held(&want)? {
            if let Some(lifted) = self.lifted_to(&want, &w.proof, &w.at, scope) {
                return Ok(Built(lifted));
            }
        }
        // What the page says once, where the letters are introduced, before
        // a cited line: a line cited only for it is cited for nothing.
        if let Built(said_once) =
            self.introduced_membership(said, system, scope, facts)?
        {
            return Ok(Built(said_once));
        }
        if let Some(carried) = self.bridged(said, system, scope, facts)? {
            return Ok(Built(carried));
        }
        let term = self.to_term(said);
        if linear::numeral(&term, self.flabel()).is_some() {
            return self.settle(&self.to_term(&want), scope, facts, 3, None, None);
        }
        let made = self.built(
            said,
            system,
            scope,
            &mut |me, term, into| me.part(term, into, scope, facts),
            Some(&mut |me, divisor| me.divisor_written(divisor, scope, facts)),
        )?;
        if !made.is_declined() {
            return Ok(made);
        }
        if let Some(f) = found {
            return Ok(Built(f));
        }
        // A closed term `arithmetic` works out and the walk does not take
        // apart, (1 + 1)!, is in a system where its value is.
        let labels = self.b.flabel.clone();
        if let Some((value, equal)) =
            super::super::numerals::worked(&self.b, &term, &labels)
        {
            let spelt = super::super::numerals::spell(value);
            if spelt != *said {
                if let Built(inside) = self.part(&spelt, system, scope, facts)? {
                    return Ok(Built(self.b.ap(
                        "eqeltrid",
                        &binds! {"ph" => scope, "A" => said, "B" => &spelt, "C" => system},
                        &[&equal, &inside],
                    )));
                }
            }
        }
        if let Some(valued) = self.function_value(said, system, scope, facts)? {
            return Ok(Built(valued));
        }
        // A finite sum is a number because its terms are (`summed`).
        if term.variable().is_none() && term.label() == Some("csu") {
            if let Built(p) = self.summed(&term, system, scope, facts, None)? {
                return Ok(Built(p));
            }
        }
        if let Some(p) = self.equated_part(said, system, scope, facts)? {
            return Ok(Built(p));
        }
        // A term the walk took apart names the part nothing says, as the
        // checker names the first part not said; an atom names itself.
        if matches!(&made, Declined(d) if d.reason() != NOT_BUILT) {
            return Ok(made);
        }
        Ok(self.no("nothing written says {}", &[&want]))
    }

    /// `said ∈ system` from an equation in hand with `said` on one side: the
    /// term is in what the other side is in (`eqeltrd`), as a reader takes
    /// a(0) = 0 to say a(0) ∈ ℝ, whatever method the step names
    /// (`METHODS.md`). The other side may not hold `said`, and a term
    /// already being read this way is not read again, so that two equations
    /// cannot send it round.
    pub(super) fn equated_part(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if self.equating.contains(said) {
            return Ok(None);
        }
        // An equation the step may rest on (`in_hand`): a line it cites or
        // one of its own requires lines.
        for (fact, proof) in facts.entries() {
            let node = self.to_term(&fact);
            if node.variable().is_some()
                || node.label() != Some("wceq")
                || node.children().len() != 2
            {
                continue;
            }
            let (left, right) =
                (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            // The other side may hold the term itself, x = (√x)², and is a
            // number by its own parts; `equating` keeps the search from
            // coming back to the term through it.
            let (other, equal) = if left == *said {
                (right, proof)
            } else if right == *said {
                let turned = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => &left, "B" => &right},
                    &[&proof],
                );
                (left, turned)
            } else {
                continue;
            };
            self.equating.insert(said.clone());
            let made = self.part(&other, system, scope, facts);
            self.equating.shift_remove(said);
            if let Built(inner) = made? {
                return Ok(Some(
                    pf!(self.b; scope, said, other, system, equal, inner, "eqeltrd"),
                ));
            }
        }
        Ok(None)
    }

    /// `( F ` x ) ∈ system` where a fact in hand gives F's type, F : A → B,
    /// and x is in A: a function's value at a point of its domain is in its
    /// codomain (`ffvelcdm`), carried to the system wanted by one of the
    /// lemmas `bridged` carries by.
    ///
    /// A function's type is a `let` line, a sort, and is cited for its values
    /// (`READERS.md`): a step or requires line that needs a(k) ∈ ℝ names the
    /// type. A family's values are the exception, a sum's terms or what an
    /// item asks of every member, where a(k) for a : {1, …, n} → ℝ is a
    /// number wherever k is in the range, as the summand's atoms are.
    pub(crate) fn function_value(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        self.function_value_from(said, system, scope, facts, false)
    }

    /// `function_value` into a set that is no number system, by a define's
    /// map only: f(x) ∈ U from g : L → U, g the map x ∈ L ↦ f(x), where no
    /// line says f(x) ∈ U itself. A value of a function typed into the set
    /// is the lemma search's to find, as it always was.
    pub(crate) fn function_value_by_map(
        &mut self,
        said: &Rpn,
        set: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        self.function_value_from(said, set, scope, facts, true)
    }

    /// `function_value`, by a define's map only where `maps_only`.
    pub(super) fn function_value_from(
        &mut self,
        said: &Rpn,
        system: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        maps_only: bool,
    ) -> Checked<Option<Proof>> {
        let term = self.to_term(said);
        if term.variable().is_some() || term.label() != Some("cfv") {
            return Ok(None);
        }
        let (point, function) =
            (self.rpn(&term.children()[0]), self.rpn(&term.children()[1]));
        for (typed, held) in facts.entries() {
            let t = self.to_term(&typed);
            if t.variable().is_some() || t.label() != Some("wf") {
                continue;
            }
            let (domain, codomain, typed_function) = (
                self.rpn(&t.children()[0]),
                self.rpn(&t.children()[1]),
                self.rpn(&t.children()[2]),
            );
            // A define's map whose rule at the point is the value: g, f on
            // L, typed g : L → U, puts f(x) in U at x ∈ L, since g(x) is
            // f(x) there (`applied_proof`).
            let through = match typed_function == function {
                true if maps_only => continue,
                true => None,
                false => match self.map_read_as(&point, &typed_function, said) {
                    Some(at) => Some(at),
                    None => continue,
                },
            };
            let inside = t!(&point, &domain, "wcel");
            let Built(at) =
                self.settle(&self.to_term(&inside), scope, facts, 2, None, None)?
            else {
                continue;
            };
            let value = t!(said, &codomain, "wcel");
            let shown = through.clone().unwrap_or_else(|| said.clone());
            let law = self.b.ap(
                "ffvelcdm",
                &binds! {"F" => &typed_function, "A" => &domain, "B" => &codomain, "C" => &point},
                &[],
            );
            let mut made = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => &typed, "ch" => &inside, "th" => t!(&shown, &codomain, "wcel")},
                &[&held, &at, &law],
            );
            if let Some(at_map) = &through {
                let Built(equal) =
                    self.applied_proof(&self.to_term(at_map), &term, scope, facts)?
                else {
                    continue;
                };
                made = self.b.ap(
                    "eqeltrrd",
                    &binds! {"ph" => scope, "A" => at_map, "B" => said, "C" => &codomain},
                    &[&equal, &made],
                );
            }
            if codomain == *system {
                return Ok(Some(made));
            }
            // A codomain that is a range puts the value in the system the
            // range lies in, as a letter let into the range is (`SYNTAX.md`,
            // a function's type and a point of its domain).
            if let Some((inside, lemma)) = self.range_system(&codomain) {
                match self
                    .out_of_range(said, &codomain, inside, lemma, made, system, scope)?
                {
                    Built(carried) => return Ok(Some(carried)),
                    Declined(_) => continue,
                }
            }
            let (Some(from), Some(to)) = (codomain.alone(), system.alone()) else {
                continue;
            };
            let Some(label) = self
                .bridge_labels()
                .get(&(from.to_string(), to.to_string()))
                .cloned()
            else {
                continue;
            };
            let push = self.sig(&label).push()[0].to_string();
            let law = self.b.ap(&label, &binds! {push => said}, &[]);
            return Ok(Some(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &value, "ch" => t!(said, system, "wcel")},
                &[&made, &law],
            )));
        }
        Ok(None)
    }

    /// The map `named` applied at `point`, where `named` is a define's map
    /// and its rule there is `said`: g(x) for f(x), g the map x ∈ L ↦ f(x).
    /// None where `named` is no map or its rule at the point is something
    /// else.
    pub(super) fn map_read_as(
        &mut self,
        point: &Rpn,
        named: &Rpn,
        said: &Rpn,
    ) -> Option<Rpn> {
        let at = t!(point, named, "cfv");
        let at_term = self.to_term(&at);
        self.applied_map(&at_term)?;
        let body = self.applied_body(&at_term)?;
        (self.rpn(&body) == *said).then_some(at)
    }

    /// ( scope -> said e. system ) from `held`, ( scope -> said e. range ):
    /// the range's lemma (`rules::RANGE_WITHIN`) puts its member in the
    /// system the range lies in, `inside`, and `carried_within` takes it on.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn out_of_range(
        &mut self,
        said: &Rpn,
        range: &Rpn,
        inside: &str,
        lemma: &str,
        held: Proof,
        system: &Rpn,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        let claim = t!(said, range, "wcel");
        let says = self.statement(lemma);
        let Some(binding) = fit(
            &says.children()[0],
            &self.to_term(&claim),
            &Binding::new(),
            &names_of(&says),
        ) else {
            return Ok(Route::no(format!("{lemma} does not take {claim}")));
        };
        let law = self.b.ap(lemma, &self.spelt(&binding), &[]);
        let proof = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, inside, "wcel")},
            &[&held, &law],
        );
        self.carried_within(said, inside, system, proof, scope)
    }

    /// The lemmas `rules::MEMBERSHIP` declares that take a thing in one
    /// number system to another, by the two systems.
    pub(super) fn bridge_labels(&mut self) -> IndexMap<(String, String), String> {
        if self.bridges.is_none() {
            let mut bridges = IndexMap::new();
            for label in self.declared_as(super::super::state::Role::Carrier) {
                let whole = self.statement(&label);
                let (given, gives) = (&whole.children()[0], &whole.children()[1]);
                // Keyed by the two systems' labels: a carrier takes a thing in
                // one number system, a constant, to another.
                let (Some(from), Some(to)) = (
                    self.rpn(&given.children()[1]).alone(),
                    self.rpn(&gives.children()[1]).alone(),
                ) else {
                    continue;
                };
                bridges
                    .entry((from.to_string(), to.to_string()))
                    .or_insert(label);
            }
            self.bridges = Some(bridges);
        }
        self.bridges.clone().unwrap_or_default()
    }

    /// What a line states, sentence by sentence: its own sentences, and
    /// where it obtained names, their memberships, which the scope holds
    /// with the line as their origin.
    pub fn stated_claims(&self, r: &str, facts: &Facts, lines: &Lines) -> Vec<Rpn> {
        let mut out = self.line_writes(r, lines);
        for (said, proof) in facts.entries() {
            if rests_on_only(&proof, r) && !out.contains(&said) {
                out.push(said);
            }
        }
        out
    }

    /// What a line states (`stated_claims`), with each proof under `scope`
    /// where `facts` holds one.
    pub fn stated_by(
        &mut self,
        r: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<IndexMap<Rpn, Option<Proof>>> {
        let mut out: IndexMap<Rpn, Option<Proof>> = IndexMap::new();
        for said in self.stated_claims(r, facts, lines) {
            let held = self.held(facts, &said, scope)?;
            out.insert(said, held);
        }
        Ok(out)
    }
}
