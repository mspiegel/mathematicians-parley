//! Universals, instances and rewriting by facts.

use std::iter;

use super::*;
use crate::elab;

impl<'a> Elaborator<'a> {
    /// ( scope -> F : A ⟶ C ), F the map ( x ∈ A ↦ B ) or the name a define
    /// gives it, where B is in C at every point of A (`fmpt`, `feq1d`): a
    /// defined function's type, which the page says once where its rule is
    /// a number there by what it says once (`SYNTAX.md`, "A define with a
    /// parameter also states what its function is on").
    ///
    /// The define's line is read behind what the step may rest on
    /// (`define_equation`), since a step rests on it without naming it.
    pub(in crate::elab) fn map_into(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let [domain, codomain, named] = wanted.children() else {
            return Ok(None);
        };
        // A map written as a map, as a rule a citation gives a function
        // letter is read (`rule_as_map`), is typed by its rule alone.
        if named.label() == Some("cmpt") {
            return self.map_type(named, domain, codomain, scope, facts, depth);
        }
        // A define's name is equal to its map by the define's own line,
        // which every step may rest on.
        let var = match (named.label(), named.children()) {
            (Some("cv"), [v]) => self.rpn(v).alone().unwrap_or_default(),
            _ => return Ok(None),
        };
        let (Some(body), Some(label)) = (
            self.definitions.get(var).cloned(),
            self.defined_by.get(var).cloned(),
        ) else {
            return Ok(None);
        };
        let map = self.to_term(&body);
        if map.variable().is_some() || map.label() != Some("cmpt") {
            return Ok(None);
        }
        let Some(typed) = self.map_type(&map, domain, codomain, scope, facts, depth)?
        else {
            return Ok(None);
        };
        let (a, c, name) = (self.rpn(domain), self.rpn(codomain), self.rpn(named));
        let Some(equal) = self.define_equation(&name, &body, &label, scope, facts)?
        else {
            return Ok(None);
        };
        let turned = self.b.ap(
            "feq1d",
            &binds! {"ph" => scope, "A" => &a, "B" => &c, "F" => &name, "G" => &body},
            &[&equal],
        );
        let want = self.rpn(wanted);
        let theirs = t!(a, c, body, "wf");
        let made = pf!(self.b; scope, want, theirs, typed, turned, "mpbird");
        // The page says the type once, on the define's line, and a step
        // rests on it without naming that line, as on a letter's membership.
        Ok(Some(Proof {
            items: made.items,
            origin: iter::once(format!("{MEMBERSHIP}{label}")).collect(),
        }))
    }

    /// ( scope -> ( x ∈ A ↦ B ) : A ⟶ C ) where B is in C at every point of
    /// A (`fmpt`); None where the map is over another set, or the rule is
    /// not settled there.
    pub(super) fn map_type(
        &mut self,
        map: &Term,
        domain: &Term,
        codomain: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let [x, over, rule] = map.children() else {
            return Ok(None);
        };
        if self.rpn(over) != self.rpn(domain) {
            return Ok(None);
        }
        let (x, over, rule, codomain, map) = (
            self.rpn(x),
            self.rpn(over),
            self.rpn(rule),
            self.rpn(codomain),
            self.rpn(map),
        );
        let every = t!(t!(rule, codomain, "wcel"), x, over, "wral");
        let Built(each) =
            self.settle(&self.to_term(&every), scope, facts, depth - 1)?
        else {
            return Ok(None);
        };
        let iff = self.b.ap(
            "fmpt",
            &binds! {"x" => &x, "A" => &over, "B" => &codomain, "C" => &rule, "F" => &map},
            &[&pf!(self.b; map, "eqid")],
        );
        let want = t!(over, codomain, map, "wf");
        Ok(Some(pf!(self.b; scope, every, want, each, iff, "sylib")))
    }

    /// ( scope -> wanted ) where a fact says it of every member of a set and
    /// another puts a term in that set whose instance it is (`rspcv`), as
    /// `instantiate` reads a line at a name the step gives. A sum lemma
    /// moved to a letter the scope does not hold asks its terms at that
    /// letter, and the line the step cites says them of every index. The
    /// instance may spell a letter it binds otherwise than the wanted, as an
    /// integral inside it over t where the lemma's is over k, and is carried
    /// across that renaming as any fact is (`held_rebound`).
    pub(crate) fn instance_of_universal(
        &mut self,
        wanted: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (said, held) in facts.entries() {
            let whole = self.to_term(&said);
            if whole.variable().is_some() || whole.label() != Some("wral") {
                continue;
            }
            let (body, letter, domain) = (
                whole.children()[0].clone(),
                self.rpn(&whole.children()[1]),
                self.rpn(&whole.children()[2]),
            );
            let mark = t!(letter, "cv");
            for (member, inside) in facts.entries() {
                let m = self.to_term(&member);
                if m.variable().is_some()
                    || m.label() != Some("wcel")
                    || self.rpn(&m.children()[1]) != domain
                {
                    continue;
                }
                let at = self.rpn(&m.children()[0]);
                let instance = self.rpn(&self.restated(&body, &mark, &at));
                let across = if instance == *wanted {
                    None
                } else if self.rebound(&instance, wanted) {
                    let Some(across) = self.renaming_apart(&instance, wanted)? else {
                        continue;
                    };
                    Some(across)
                } else {
                    continue;
                };
                let ph = self.rpn(&body);
                // At the letter it binds the instance is the body itself, and
                // `rsp` takes it: `rspcv` keeps its term apart from the letter.
                let applied = if at == mark {
                    // `rsp` takes the "for all" first and the membership
                    // second, the other way round from `rspcv`.
                    let taken = self.b.ap(
                        "rsp",
                        &binds! {"ph" => &ph, "x" => &letter, "A" => &domain},
                        &[],
                    );
                    self.b.ap(
                        "com12",
                        &binds! {"ph" => &said, "ps" => &member, "ch" => &ph},
                        &[&taken],
                    )
                } else {
                    let tie = self.to_term(&t!(
                        t!(mark, at, "wceq"),
                        t!(ph, instance, "wb"),
                        "wi"
                    ));
                    let Built(asked) = self.prove_essential(&tie, scope, facts)? else {
                        continue;
                    };
                    self.b.ap(
                        "rspcv",
                        &binds! {"ph" => &ph, "ps" => &instance, "x" => &letter, "A" => &at, "B" => &domain},
                        &[&asked],
                    )
                };
                let carried = pf!(self.b; scope, member, t!(said, instance, "wi"), inside, applied, "syl");
                let proof = pf!(self.b; scope, said, instance, held, carried, "mpd");
                let Some(across) = across else {
                    return Ok(Some(proof));
                };
                let turned =
                    pf!(self.b; t!(instance, wanted, "wb"), scope, across, "a1i");
                return Ok(Some(
                    pf!(self.b; scope, instance, wanted, proof, turned, "mpbid"),
                ));
            }
        }
        Ok(None)
    }

    /// `instance_of_universal` at a term no fact puts in the set: the wanted
    /// is read as the "for all"'s body at some term, the term shown a member
    /// of the set by the search, and the line taken there. A requires line
    /// "for all i ∈ {1, …, 1}, i/(i + 1)! ∈ ℝ" is read at the numeral 1,
    /// which no line puts in {1, …, 1}. A membership asked in a wider number
    /// system than the body says is the body's carried there (`bridged`).
    pub(crate) fn instance_at_a_term(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        for (said, _) in facts.entries() {
            let whole = self.to_term(&said);
            if whole.variable().is_some() || whole.label() != Some("wral") {
                continue;
            }
            let (body, letter, domain) = (
                whole.children()[0].clone(),
                self.rpn(&whole.children()[1]),
                self.rpn(&whole.children()[2]),
            );
            // The body with its letter a pattern variable no part of it names.
            let text = self.rpn(&body);
            let Some(hole) = ["A", "B", "C", "D", "E", "F"]
                .into_iter()
                .find(|v| !text.has(v))
            else {
                continue;
            };
            fn holed(t: &Term, letter: &str, hole: &Term) -> Term {
                if t.label() == Some("cv") && t.children()[0].variable() == Some(letter)
                {
                    return hole.clone();
                }
                if t.variable().is_some() {
                    return t.clone();
                }
                let kids = t
                    .children()
                    .iter()
                    .map(|c| holed(c, letter, hole))
                    .collect();
                t.with_children(kids)
            }
            let Some(name) = whole.children()[1].variable().map(str::to_string) else {
                continue;
            };
            let pattern = holed(&body, &name, &Term::var(hole));
            let vars: Vars = [Symbol::of(hole)].into_iter().collect();
            let membership = |t: &Term| {
                t.label() == Some("wcel")
                    && t.children().len() == 2
                    && t.children()[1]
                        .label()
                        .is_some_and(|l| lookup(rules::SYSTEMS, l).is_some())
            };
            let binding = fit(&pattern, wanted, &Binding::new(), &vars).or_else(|| {
                (membership(&pattern) && membership(wanted))
                    .then(|| {
                        fit(
                            &pattern.children()[0],
                            &wanted.children()[0],
                            &Binding::new(),
                            &vars,
                        )
                    })
                    .flatten()
            });
            let Some(at) = binding.and_then(|b| b.get(hole).cloned()) else {
                continue;
            };
            let at = self.rpn(&at);
            if letter.alone().is_some_and(|l| at.has(l)) {
                continue;
            }
            let member = self.to_term(&t!(at, domain, "wcel"));
            let Built(inside) = self.settle(&member, scope, facts, depth - 1)? else {
                continue;
            };
            let there = facts.copy();
            self.know(&there, self.rpn(&member), inside);
            let instance = self.rpn(&self.restated(&body, &t!(letter, "cv"), &at));
            let Some(p) = self.instance_of_universal(&instance, scope, &there)? else {
                continue;
            };
            let rpn = self.rpn(wanted);
            if instance == rpn {
                return Ok(Some(p));
            }
            self.know(&there, instance.clone(), p);
            if let Some(found) = self.held(&there, &rpn, scope)? {
                return Ok(Some(found));
            }
            if membership(wanted) {
                let (s, sys) = (
                    self.rpn(&wanted.children()[0]),
                    self.rpn(&wanted.children()[1]),
                );
                if let Some(found) = self.bridged(&s, &sys, scope, &there)? {
                    return Ok(Some(found));
                }
            }
        }
        Ok(None)
    }

    /// The declared lemmas that could conclude what is wanted, in order,
    /// through an index built from each lemma's own statement.
    pub(super) fn declared(&mut self, wanted: &Term, backwards: bool) -> Vec<String> {
        let keys = self.head_keys(wanted);
        let index = self.lemma_index();
        index
            .iter()
            .filter(|(_, (heads, _))| {
                heads[backwards as usize].iter().any(|k| keys.contains(k))
            })
            .map(|(label, _)| label.clone())
            .collect()
    }

    /// The declared lemmas of one role, in the order they are declared.
    pub fn declared_as(&mut self, role: Role) -> Vec<String> {
        self.lemma_index()
            .iter()
            .filter(|(_, (_, said))| *said == role)
            .map(|(label, _)| label.clone())
            .collect()
    }

    /// Every declared lemma set.mm has, with its readings and its role.
    pub(super) fn lemma_index(
        &mut self,
    ) -> &IndexMap<String, ([IndexSet<HeadKey>; 2], Role)> {
        if self.lemma_heads.is_none() {
            let mut index = IndexMap::new();
            for label in rules::MEMBERSHIP {
                if let Some(sig) = self.b.sigs.get(label) {
                    let sig = sig.clone();
                    index
                        .insert(label.to_string(), (self.heads(&sig), self.role(&sig)));
                }
            }
            self.lemma_heads = Some(index);
        }
        self.lemma_heads.as_ref().unwrap()
    }

    /// What a declared lemma is for, read off what it states.
    pub(super) fn role(&self, sig: &Signature) -> Role {
        let whole = self.statement(&sig.label);
        if !sig.essentials.is_empty() {
            return Role::Side;
        }
        if sig.floats.len() == 1 && whole.label() == Some("wi") {
            let (given, gives) = (&whole.children()[0], &whole.children()[1]);
            if given.label() == Some("wcel")
                && gives.label() == Some("wcel")
                && given.children()[0].variable().is_some()
                && self.rpn(&given.children()[0]) == self.rpn(&gives.children()[0])
            {
                return Role::Carrier;
            }
        }
        Role::Side
    }

    /// What each reading of a lemma can end on, forwards and backwards.
    pub(super) fn heads(&self, sig: &Signature) -> [IndexSet<HeadKey>; 2] {
        let whole = self.statement(&sig.label);
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            reads = reads.children()[1].clone();
        }
        let said = if whole.label() == Some("wb") {
            whole.clone()
        } else {
            reads
        };
        let mut forward = vec![whole.clone()];
        let mut backward = Vec::new();
        if said.label() == Some("wb") {
            forward.push(said.children()[1].clone());
            backward.push(said.children()[0].clone());
        }
        let ends = |starts: Vec<Term>| {
            let mut out = IndexSet::new();
            for start in starts {
                let mut node = start;
                out.insert(self.head_key(&node));
                while node.label() == Some("wi") && node.variable().is_none() {
                    node = node.children()[1].clone();
                    out.insert(self.head_key(&node));
                }
            }
            out
        };
        [ends(forward), ends(backward)]
    }

    /// How a lemma's conclusion constrains what it can match.
    pub(super) fn head_key(&self, node: &Term) -> HeadKey {
        if node.variable().is_some() {
            return HeadKey::Any;
        }
        if node.label() == Some("wcel")
            && node.children().len() == 2
            && node.children()[1].names().is_empty()
        {
            return HeadKey::Member(self.rpn(&node.children()[1]));
        }
        match node.label() {
            Some(label) => HeadKey::Head(label.to_string()),
            None => HeadKey::Any,
        }
    }

    /// The keys a lemma's conclusion may carry and still match `wanted`.
    pub(super) fn head_keys(&self, wanted: &Term) -> IndexSet<HeadKey> {
        let mut keys = IndexSet::new();
        keys.insert(HeadKey::Any);
        let Some(label) = wanted.label() else {
            return keys;
        };
        keys.insert(HeadKey::Head(label.to_string()));
        if wanted.label() == Some("wcel") && wanted.children().len() == 2 {
            keys.insert(HeadKey::Member(self.rpn(&wanted.children()[1])));
        }
        keys
    }

    /// What is wanted, with a term in it put as an equation in hand says.
    ///
    /// The equations are the ones in `facts`, which during a step is what the
    /// step names, so this rewrites only by a line the step cites. Only a
    /// term built from others is replaced, never a name or a constant. Each
    /// rewrite spends a level, and a term already being rewritten is not
    /// rewritten again, so the rewrites stop.
    pub(super) fn rewritten(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let want = self.rpn(wanted);
        if self.rewriting.contains(&want) {
            return Ok(self.no("{} is already being rewritten", &[&want]));
        }
        self.rewriting.insert(want.clone());
        let out = self.rewrite_by_facts(wanted, &want, scope, facts, depth);
        self.rewriting.shift_remove(&want);
        out
    }

    /// One pass over the equations in hand, for `rewritten`.
    pub(super) fn rewrite_by_facts(
        &mut self,
        wanted: &Term,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        for said in facts.keys() {
            let equation = self.to_term(&said);
            if equation.label() != Some("wceq") || equation.children().len() != 2 {
                continue;
            }
            let (left, right) = (
                equation.children()[0].clone(),
                equation.children()[1].clone(),
            );
            for (old, new, flip) in [(&left, &right, true), (&right, &left, false)] {
                if old.variable().is_some()
                    || old.children().is_empty()
                    || old.label() == Some("cv")
                {
                    continue;
                }
                let (was, now) = (self.rpn(old), self.rpn(new));
                // A numeral is a constant however set.mm spells it, and so is
                // a sum of them.
                if was.tokens().iter().all(|t| rules::numeric(t.as_str())) {
                    continue;
                }
                let put = self.replaced(wanted, &was, new);
                if self.rpn(&put) == *want {
                    continue;
                }
                let Built(under) = self.settle(&put, scope, facts, depth - 1)? else {
                    continue;
                };
                let leaf = Leaf::Rows(vec![Row::Cited {
                    was: was.clone(),
                    now: now.clone(),
                    said: said.clone(),
                    flip,
                }]);
                let Built(alike) =
                    self.congruence(&put, wanted, scope, facts, None, &leaf)?
                else {
                    continue;
                };
                return Ok(Built(
                    pf!(self.b; scope, self.rpn(&put), want, under, alike, "mpbid"),
                ));
            }
        }
        Ok(self.no("no equation in hand rewrites {}", &[want]))
    }

    /// `term` with every occurrence of the term spelt `was` put as `new`.
    pub(crate) fn replaced(&self, term: &Term, was: &Rpn, new: &Term) -> Term {
        if self.rpn(term) == *was {
            return new.clone();
        }
        if term.variable().is_some() || term.children().is_empty() {
            return term.clone();
        }
        term.with_children(
            term.children()
                .iter()
                .map(|c| self.replaced(c, was, new))
                .collect(),
        )
    }

    /// What is wanted, held by the scope under another name for a term: a
    /// declared equation is asked whether the fact in hand is the fact wanted
    /// said differently, and the congruence carries it across.
    ///
    /// A fact is read in other words only where no other is being read so:
    /// what this reaches through asks `settle` afresh, which starts its depth
    /// over, and each fact it asks may be a larger term than the last
    /// (|⌊A⌋| ∈ ℕ₀, then ||⌊A⌋|| ∈ ℕ₀), so a reading inside a reading has
    /// nothing that must decrease and need not end. No proof of the corpus
    /// reads a fact in other words inside such a reading.
    pub(super) fn said_otherwise(
        &mut self,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Option<Proof>> {
        let _ = depth;
        let want = self.rpn(wanted);
        if !self.saying.is_empty() {
            return Ok(None);
        }
        self.saying.insert(want.clone());
        let out = self.otherwise(wanted, &want, scope, facts);
        self.saying.shift_remove(&want);
        out
    }

    /// One pass over the facts in hand, for `said_otherwise`: the first
    /// whose standard form is what is wanted's.
    pub(super) fn otherwise(
        &mut self,
        wanted: &Term,
        want: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        for (said, proof) in facts.entries() {
            if said == *want {
                continue;
            }
            let alike = self.same(&self.to_term(&said), wanted, scope, facts, None)?;
            if let Built(alike) = alike {
                return Ok(Some(pf!(self.b; scope, said, want, proof, alike, "mpbid")));
            }
        }
        Ok(None)
    }

    /// Whether one lemma settles what is wanted, and how.
    ///
    /// A biconditional says two things, so it can be read either way, and a
    /// lemma may ask something and only then say its two things: the asking
    /// is peeled off first and what is left is read the same way a bare
    /// biconditional is.
    pub(super) fn fits(
        &mut self,
        label: &str,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
    ) -> Checked<Option<Proof>> {
        let whole = self.statement(label);
        let mut asks = Vec::new();
        let mut joins = Vec::new();
        let mut reads = whole.clone();
        while reads.label() == Some("wi") {
            asks.push(reads.children()[0].clone());
            joins.push(Join::Implies);
            reads = reads.children()[1].clone();
        }
        let side = if backwards { 0 } else { 1 };
        let mut readings: Vec<(Vec<Term>, Vec<Join>, Term)> = Vec::new();
        if whole.label() == Some("wb") {
            readings.push((
                vec![whole.children()[1 - side].clone()],
                vec![Join::Iff],
                whole.children()[side].clone(),
            ));
            // and the biconditional itself, which a side condition may ask
            // for as it stands
            if !backwards {
                readings.push((Vec::new(), Vec::new(), whole.clone()));
            }
        } else if reads.label() == Some("wb") {
            let mut a = asks.clone();
            a.push(reads.children()[1 - side].clone());
            let mut j = joins.clone();
            j.push(Join::Iff);
            readings.push((a, j, reads.children()[side].clone()));
            if !backwards {
                readings.push((Vec::new(), Vec::new(), whole.clone()));
            }
        } else if !backwards {
            // Nothing was said two ways, so the statement is read as it
            // stands and `fitting` peels it.
            readings.push((Vec::new(), Vec::new(), whole.clone()));
        }
        for (antecedents, held, side) in readings {
            let found = self.fitting(
                label,
                &whole,
                antecedents,
                held,
                side,
                wanted,
                scope,
                facts,
                depth,
                backwards,
            )?;
            if found.is_some() {
                return Ok(found);
            }
        }
        Ok(None)
    }

    /// One reading of a lemma, applied to what is wanted: its antecedents
    /// are peeled until what is left is what is wanted.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn fitting(
        &mut self,
        label: &str,
        whole: &Term,
        mut antecedents: Vec<Term>,
        mut joins: Vec<Join>,
        reads: Term,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
    ) -> Checked<Option<Proof>> {
        let variables = names_of(whole);
        let mut reads = reads;
        let binding = loop {
            if let Some(b) = fit(&reads, wanted, &Binding::new(), &variables) {
                break b;
            }
            if reads.label() != Some("wi") {
                return Ok(None);
            }
            antecedents.push(reads.children()[0].clone());
            joins.push(Join::Implies);
            reads = reads.children()[1].clone();
        };
        // What the lemma concludes need not fix everything it asks, so an
        // antecedent still open is matched against something already known,
        // whole, and failing that a conjunct at a time.
        let sig = self.sig(label).clone();
        let read = self.read_off(&sig, binding, &variables);
        let binding = self.opened(&antecedents, read, facts, &variables);
        self.fitted(
            label,
            &sig,
            &antecedents,
            &joins,
            wanted,
            scope,
            facts,
            depth,
            backwards,
            binding,
        )
    }

    /// The binding with what the antecedents leave open filled in.
    ///
    /// A conjunct asking where to look for something rather than anything of
    /// it is left to `sethood`, which reads it so, and is not matched. Every
    /// antecedent is matched whole before any is taken apart. Both are read
    /// through the standard form's one-way rules first, so that a fact
    /// answers a slot however either is spelt: `X ∈ 𝒫A` in hand fills the
    /// A of a slot asking `X ⊆ A`.
    pub(super) fn opened(
        &mut self,
        antecedents: &[Term],
        binding: Binding,
        facts: &Facts,
        variables: &Vars,
    ) -> Binding {
        let mut binding = binding;
        let mut whole = Vec::new();
        let keys: Vec<Term> = facts
            .keys()
            .iter()
            .map(|held| {
                let held = self.to_term(held);
                self.read_through(&held, false, None)
            })
            .collect();
        for slot in antecedents {
            if slot.names().iter().all(|n| binding.contains_key(&**n)) {
                continue;
            }
            let slot = self.read_through(slot, false, None);
            let mut filled_any = false;
            for held in &keys {
                if let Some(filled) = fit(&slot, held, &binding, variables) {
                    binding = filled;
                    filled_any = true;
                    break;
                }
            }
            if !filled_any {
                whole.push(slot);
            }
        }
        for slot in &whole {
            for piece in conjuncts_of(slot) {
                if piece.names().iter().all(|n| binding.contains_key(&**n)) {
                    continue;
                }
                // A fixed function's type is what a line says of it, not a
                // place to look.
                if !sethood(&piece, &binding).is_empty()
                    && !function_fixed(&piece, &binding)
                {
                    continue;
                }
                for held in &keys {
                    if let Some(filled) = fit(&piece, held, &binding, variables) {
                        binding = filled;
                        break;
                    }
                }
            }
            // A class neither the claim nor a fact fixes is set.mm asking
            // where to look for the thing rather than asking anything of it,
            // and _V holds every set.
            for open in sethood(slot, &binding) {
                binding.insert(open, Term::apply("cvv", Vec::new()));
            }
        }
        binding
    }

    /// The lemma proved under one binding, or None where it is not.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn fitted(
        &mut self,
        label: &str,
        sig: &Signature,
        antecedents: &[Term],
        joins: &[Join],
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        depth: i32,
        backwards: bool,
        binding: Binding,
    ) -> Checked<Option<Proof>> {
        let variables = names_of(&self.statement(label));
        // A declared lemma may state a hypothesis in full rather than ask for
        // it, which is a spelling and not a difference in what it leans on.
        let read = self.read_off(sig, binding, &variables);
        let binding = self.instanced(sig, read);
        let mut essentials = Vec::new();
        for e in &sig.essentials {
            let asked = self.essential(e).substitute(&binding);
            essentials.push(self.prove_essential(&asked, scope, facts)?);
        }
        let mut proofs = Vec::new();
        for one in essentials {
            match one {
                Built(p) => proofs.push(p),
                Declined(_) => return Ok(None),
            }
        }
        let mut proof = self.b.ap(
            label,
            &self.spelt(&binding),
            &proofs.iter().collect::<Vec<_>>(),
        );
        if antecedents.is_empty() {
            return Ok(Some(pf!(self.b; self.rpn(wanted), scope, proof, "a1i")));
        }
        for (i, slot) in antecedents.iter().enumerate() {
            let asks = slot.substitute(&binding);
            let mut rest = self.rpn(wanted);
            for (later, join) in antecedents[i + 1..].iter().zip(&joins[i + 1..]).rev()
            {
                let said = self.rpn(&later.substitute(&binding));
                // A biconditional read backwards states its sides the other
                // way round from the order they are taken in.
                rest = if *join == Join::Iff && backwards {
                    t!(rest, said, "wb")
                } else {
                    t!(said, rest, join_token(*join))
                };
            }
            let Built(under) = self.settle(&asks, scope, facts, depth - 1)? else {
                return Ok(None);
            };
            let first = proof.last() == label;
            let asked = self.rpn(&asks);
            proof = match (joins[i] == Join::Iff && backwards, first) {
                // `sylibr` takes what is asked before what is concluded, as
                // the forward discharges do.
                (true, true) => pf!(self.b; scope, asked, rest, under, proof, "sylibr"),
                // `mpbird` concludes its first letter from its second.
                (true, false) => {
                    pf!(self.b; scope, rest, asked, under, proof, "mpbird")
                }
                (false, _) => {
                    let fold = discharge(joins[i], first);
                    pf!(self.b; scope, asked, rest, under, proof, fold)
                }
            };
        }
        Ok(Some(proof))
    }

    // --- congruence -----------------------------------------------------

    /// A target read as a tree, so a rewrite can walk down it: a target need
    /// not be one constructor, and each level wants its own congruence
    /// lemma.
    pub fn shape(&mut self, pattern: &str) -> Shape {
        if let Some(found) = self.shapes.get(pattern) {
            return found.clone();
        }
        let mut stack: Vec<Shape> = Vec::new();
        for token in pattern.split_whitespace() {
            if let Some(n) = token.strip_prefix('_') {
                stack.push(Shape::Hole(n.parse::<usize>().unwrap() - 1));
                continue;
            }
            let count = self.sig(token).floats.len();
            if count == 0 {
                stack.push(Shape::Const(token.to_string()));
                continue;
            }
            let args = stack.split_off(stack.len() - count);
            // The operation is an operand of the lemma that rewrites under it
            // where it is a constant, as `cabs` is in |x|. Where it is a hole
            // it is an argument like any other.
            match (rules::WRAPS.contains(&token), args.last()) {
                (true, Some(Shape::Const(op))) => {
                    let op = op.clone();
                    let kids = args[..args.len() - 1].to_vec();
                    stack.push(Shape::App(op, Some(token.to_string()), kids));
                }
                _ => stack.push(Shape::App(token.to_string(), None, args)),
            }
        }
        let found = stack.swap_remove(0);
        self.shapes.insert(pattern.to_string(), found.clone());
        found
    }

    /// A proof that `node` equals `node` with `old` replaced by `new`.
    ///
    /// The path from the root of the claim to the occurrence decides the
    /// lemmas, one per step along it, and which hole the occurrence sits in
    /// decides which lemma. Nothing is searched for.
    pub fn rewrite(
        &mut self,
        node: &Node,
        old: &Rpn,
        new: &Rpn,
        scope: &Rpn,
        eqproof: &Proof,
    ) -> Checked<Route<(Rpn, Proof)>> {
        if self.term(node)? == *old {
            return Ok(Built((new.clone(), eqproof.clone())));
        }
        // A phrase is its meaning in set.mm, so it is rewritten there.
        if let Some(meaning) = self.phrase_written_out(node) {
            return self.rewrite(&meaning, old, new, scope, eqproof);
        }
        // A library function's application fills what its definition builds
        // with its arguments; its name fills no slot.
        let library = self.library_application(node);
        let children: &[Node] = match &library {
            Some((_, arguments)) => arguments,
            None => &node.children,
        };
        // A binder's variable fills its slot as itself, and nothing rewrites
        // it; the body speaks of what the binder introduces. A hole that
        // holds its variable already is that variable (`Elaborator::term`).
        let bound = self
            .binders
            .get(&node.notation())
            .cloned()
            .unwrap_or_default();
        let walked = self.names_kept(|me| -> Checked<Route<Walked>> {
            for &i in &bound {
                let c = &node.children[i];
                if c.rpn.is_none() {
                    let var = me.binder_var(&c.text)?;
                    me.names.insert(c.text.to_string(), t!(var, "cv"));
                }
            }
            let mut holes = Vec::new();
            for (i, c) in children.iter().enumerate() {
                holes.push(if bound.contains(&i) && c.rpn.is_none() {
                    t!(me.binder_var(&c.text)?)
                } else {
                    me.term(c)?
                });
            }
            let mut after = holes.clone();
            let mut proofs = IndexMap::new();
            for (i, child) in children.iter().enumerate() {
                if bound.contains(&i) || !holds_run(&me.term(child)?, old) {
                    continue;
                }
                let (built, proof) =
                    take!(me.rewrite(child, old, new, scope, eqproof)?);
                after[i] = built;
                proofs.insert(i, proof);
            }
            Ok(Built(Walked {
                holes,
                after,
                proofs,
            }))
        })?;
        let Walked {
            holes,
            after,
            proofs,
        } = take!(walked);
        if proofs.is_empty() {
            let said = self.term(node)?;
            return Ok(Route::no(format!("nothing to rewrite in {said}")));
        }
        let pattern = match library {
            Some((builds, _)) => builds,
            None => self.pattern(node)?,
        };
        let tree = self.shape(&pattern);
        Ok(self.descend(&tree, &holes, &after, &proofs, scope))
    }

    /// Walk a target down to the holes that changed, a lemma a level.
    pub(super) fn descend(
        &mut self,
        tree: &Shape,
        before: &[Rpn],
        after: &[Rpn],
        proofs: &IndexMap<usize, Proof>,
        scope: &Rpn,
    ) -> Route<(Rpn, Proof)> {
        let (label, wrap, kids) = match tree {
            Shape::Hole(i) => return Built((after[*i].clone(), proofs[i].clone())),
            Shape::Const(_) => return Route::no("no hole changed under this target"),
            Shape::App(label, wrap, kids) => (label, wrap, kids),
        };
        let was: Vec<Rpn> = kids.iter().map(|k| spell(k, before)).collect();
        let mut now = was.clone();
        let mut deeper = Vec::new();
        let mut slots = Vec::new();
        for (slot, kid) in kids.iter().enumerate() {
            if !proofs.keys().any(|h| holds(kid, *h)) {
                continue;
            }
            match self.descend(kid, before, after, proofs, scope) {
                Built((built, under)) => {
                    now[slot] = built;
                    deeper.push(under);
                    slots.push(slot);
                }
                Declined(d) => return Declined(d),
            }
        }
        if slots.is_empty() {
            return Route::no("no hole changed under this target");
        }
        // An operation or a relation is itself an operand of the lemma that
        // rewrites under it; a constructor that takes its arguments directly
        // is not. What changed comes first, old beside new, then the rest.
        let head = wrap.clone().unwrap_or_else(|| label.clone());
        let spelt_now = applied(&now, label, wrap.as_deref());
        if (head == "csu" || head == "cprod") && slots.contains(&1) {
            let by_slot: IndexMap<usize, Proof> =
                slots.iter().copied().zip(deeper.iter().cloned()).collect();
            return self
                .summand_changed(&head, scope, &was, &now, &by_slot)
                .map(|p| (spelt_now, p));
        }
        // A map or an indexed union over another domain: `mpteq1d` and
        // `iuneq1d` take the letter before the domains, so their parts are
        // given by name.
        if (head == "cmpt" || head == "ciun") && slots == [1] {
            let old_map = self.to_term(&t!(was[0], was[1], was[2], label));
            let new_map = self.to_term(&t!(now[0], now[1], now[2], label));
            if let Some(wider) =
                self.domain_holding(&old_map, &new_map, scope, &deeper[0])
            {
                return Built((spelt_now, wider));
            }
            let lemma =
                rules::congruence(&head, &[1]).expect("a congruence for a domain");
            return Built((
                spelt_now,
                self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "x" => &was[0], "A" => &was[1], "B" => &now[1], "C" => &was[2]},
                    &deeper.iter().collect::<Vec<_>>(),
                ),
            ));
        }
        // A "for all", a "there is" or a set-builder over another domain, its
        // body maybe changing too: the lemmas take the body and the letter
        // before the domains, so their parts are given by name, as
        // `congruence` gives them.
        if matches!(head.as_str(), "wral" | "wrex" | "crab") && slots == [2] {
            let lemma =
                rules::congruence(&head, &[2]).expect("a congruence for a domain");
            return Built((
                spelt_now,
                self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "ps" => &was[0], "x" => &was[1], "A" => &was[2], "B" => &now[2]},
                    &[&deeper[0]],
                ),
            ));
        }
        if matches!(head.as_str(), "wral" | "wrex") && slots == [0, 2] {
            let lemma = rules::congruence(&head, &[0, 2])
                .expect("a congruence for a domain and a body");
            return Built((
                spelt_now,
                self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "ps" => &was[0], "ch" => &now[0], "x" => &was[1], "A" => &was[2], "B" => &now[2]},
                    &[&deeper[1], &deeper[0]],
                ),
            ));
        }
        // A value whose function changes: `fveq1d` takes the argument before
        // the two functions, so its parts are given by name.
        if head == "cfv" && slots == [1] {
            return Built((
                spelt_now,
                self.b.ap(
                    "fveq1d",
                    &binds! {"ph" => scope, "A" => &was[0], "F" => &was[1], "G" => &now[1]},
                    &deeper.iter().collect::<Vec<_>>(),
                ),
            ));
        }
        // A function changing in a statement that it is one-to-one, or onto:
        // the closed law after the equation by `syl`.
        if let Some(law) = rules::function_law(&head, &slots) {
            let parts =
                binds! {"A" => &was[0], "B" => &was[1], "F" => &was[2], "G" => &now[2]};
            let old = t!(was[0], was[1], was[2], head);
            let carried = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(was[2], now[2], "wceq"),
                "ch" => t!(old, spelt_now, "wb")},
                &[&deeper[0], &self.b.ap(law, &parts, &[])],
            );
            return Built((spelt_now, carried));
        }
        let lemma = rules::congruence(&head, &slots)
            .unwrap_or_else(|| panic!("no congruence for {head} at {slots:?}"));
        // A function changing in its type, `feq1d` and `f1oeq1d`: their
        // letters are bound by name, since set.mm declares the domain and
        // codomain before the function, which the order below would not.
        if matches!(head.as_str(), "wf" | "wf1o") && slots == [2] {
            let carried = self.b.ap(
                lemma,
                &binds! {"ph" => scope, "A" => &was[0], "B" => &was[1],
                "F" => &was[2], "G" => &now[2]},
                &[&deeper[0]],
            );
            return Built((spelt_now, carried));
        }
        let mut all: Vec<crate::mm::spell::Part> = vec![elab::part(scope)];
        for &slot in &slots {
            all.push(elab::part(&was[slot]));
            all.push(elab::part(&now[slot]));
        }
        for (j, o) in was.iter().enumerate() {
            if !slots.contains(&j) {
                all.push(elab::part(o));
            }
        }
        if wrap.is_some() {
            all.push(elab::part(label));
        }
        all.extend(deeper.iter().map(|p| elab::part(p)));
        all.push(elab::part(lemma));
        Built((spelt_now, self.b.proof(&all)))
    }

    /// A sum or a product rewritten where its term changes, and its range
    /// maybe; `head` is `csu` or `cprod`.
    ///
    /// `sumeq2sdv` rewrites the summand from an equation with no index in
    /// it, which set.mm lets it do only where the scope does not mention the
    /// index. The range, where it changes too, is rewritten first by
    /// `sumeq1d`, and `eqtrd` joins the two. A product is rewritten the same
    /// way by `prodeq2sdv` and `prodeq1d`.
    pub(super) fn summand_changed(
        &self,
        head: &str,
        scope: &Rpn,
        was: &[Rpn],
        now: &[Rpn],
        proofs: &IndexMap<usize, Proof>,
    ) -> Route<Proof> {
        let (term_law, range_law) = match head {
            "cprod" => ("prodeq2sdv", "prodeq1d"),
            _ => ("sumeq2sdv", "sumeq1d"),
        };
        let (limits, summand, index) = (&was[0], &was[1], &was[2]);
        if index.alone().is_some_and(|i| scope.has(i)) {
            return Route::no("the scope mentions the index the sum binds");
        }
        let rewritten = self.b.ap(
            term_law,
            &binds! {"ph" => scope, "A" => &now[0], "B" => summand, "C" => &now[1], "k" => index},
            &[&proofs[&1]],
        );
        let Some(first) = proofs.get(&0) else {
            return Built(rewritten);
        };
        let moved = self.b.ap(
            range_law,
            &binds! {"ph" => scope, "A" => limits, "B" => &now[0], "C" => summand, "k" => index},
            &[first],
        );
        Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => t!(limits, summand, index, head),
            "B" => t!(now[0], summand, index, head), "C" => t!(now[0], now[1], index, head)},
            &[&moved, &rewritten],
        ))
    }

    // --- closing a difference -------------------------------------------

    /// What a leaf of the walk says where two terms differ: a proof, a
    /// decline, or None where the walk goes a level in.
    pub fn leaf(
        &mut self,
        leaf: &Leaf,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Route<Proof>>> {
        match leaf {
            Leaf::Rows(rows) => {
                for row in rows {
                    let found = match row {
                        Row::Held => self.closed_held(one, other, where_, held)?,
                        Row::Cited {
                            was,
                            now,
                            said,
                            flip,
                        } => self.closed_cited(
                            one, other, where_, held, was, now, said, *flip,
                        )?,
                        Row::Assumed { was, now, under } => self.closed_assumed(
                            one, other, where_, held, was, now, under,
                        )?,
                        Row::Standard => {
                            self.closed_standard(one, other, where_, held)?
                        }
                        Row::Toward => self.closed_toward(one, other, where_, held)?,
                        Row::Identity => {
                            self.closed_identity(one, other, where_, held)?
                        }
                        Row::Bare => self.closed_bare(one, other, where_, held)?,
                        Row::InNoOrder => {
                            self.closed_in_no_order(one, other, where_, held)?
                        }
                    };
                    if found.is_some() {
                        return Ok(found);
                    }
                }
                Ok(None)
            }
            Leaf::Arithmetic { what, step } => {
                if !one.names().is_empty() || !other.names().is_empty() {
                    return Ok(None);
                }
                // A pair arithmetic does not work out whole, 2! and (1 + 1)!,
                // is carried a level in, where the pieces that change are.
                let claim = t!(self.rpn(one), self.rpn(other), "wceq");
                if super::super::field::decide_closed(&self.to_term(&claim))
                    .is_declined()
                {
                    return Ok(None);
                }
                self.closed_fact(&claim, where_, held, what, Some(step))
                    .map(|p| Some(Built(p)))
            }
            Leaf::RealArithmetic { what } => {
                if !one.names().is_empty() || !other.names().is_empty() {
                    return Ok(None);
                }
                let claim = t!(self.rpn(one), self.rpn(other), "wceq");
                self.real_fact(&claim, where_, held, what)
                    .map(|p| Some(Built(p)))
            }
        }
    }
}
