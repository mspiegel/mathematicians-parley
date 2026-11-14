//! Citing a theorem the corpus proves.

use super::*;

impl<'a> Elaborator<'a> {
    /// Apply a theorem this corpus proves, as this elaborator states it: its
    /// hypotheses became the antecedent of one implication, so citing it is
    /// conjoining the facts the step supplies and applying one label.
    pub(super) fn cite_corpus(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        other: &'a Theorem,
    ) -> Checked<Proof> {
        let full = other.qualified();
        if !self.cited.contains(&full) {
            self.cited.push(full.clone());
        }
        // A sequence the cited statement defines by recursion is read as
        // this proof's sequence of that name (`in_its_names`), and the step
        // reads that define without citing it, as the statement speaks of
        // the sequence by name.
        for (_, r) in other.stated_recursions() {
            if let Some(name) =
                r.names.iter().find(|n| self.recursion_named(n).is_none())
            {
                return Err(self.defect(
                    step.line,
                    format!(
                        "{full} is stated over {name}, which its define gives by recursion, and nothing here defines {name} by recursion"
                    ),
                ));
            }
        }
        let recursive = self.recursions_read(other);
        let claimed = step.claim.sentences().len();
        // The theorem read under what the citation gives its letters. A
        // letter named in `apart` is read as a class of its own, and what it
        // stands for is given back beside the reading, to be put in once the
        // theorem's bound letters are moved off its letters.
        let read = |me: &mut Self, apart: &BTreeSet<String>| -> Checked<Reading> {
            let mut spare: std::collections::VecDeque<&str> =
                CLASS_NAMES.iter().copied().collect();
            let mut given: Vec<Given> = Vec::new();
            {
                let saved = me.names.clone();
                // Every value is read in the step's own names before any
                // letter of the theorem is given one: `a := b/k, b := a/k`
                // swaps the two, and reading the second after the first is
                // given would read a/k as (b/k)/k.
                let values: IndexMap<String, Rpn> =
                    me.instantiated(&step.just)?.into_iter().collect();
                // What the citation does not write is found by matching the
                // theorem against what the step claims and cites, as the
                // checker finds it (`citing::taken`, SYNTAX.md "No pair says
                // what goes without saying"): `A ⊆ B ∪ A` cited for
                // `B ⊆ A ∪ B` puts B for A and A for B.
                let matched = me.corpus_matched(step, other)?;
                // A letter read apart stands for a class no value and no name
                // of the step writes, since the value is put back in for that
                // class over the whole reading: the citing proof's own first
                // `let` is cA, as the theorem's is.
                let held: BTreeSet<&str> = saved
                    .values()
                    .chain(values.values())
                    .chain(matched.values())
                    .flat_map(|t| t.tokens().iter().map(|s| s.as_str()))
                    .collect();
                let mut unheld = CLASS_NAMES
                    .iter()
                    .rev()
                    .copied()
                    .filter(|c| !held.contains(c))
                    .collect::<Vec<_>>()
                    .into_iter();
                for h in &other.hypotheses {
                    // A graph's line introduces one class, the graph, whose
                    // parts its vertices, edges and the notations' `@ends`
                    // and `@deg` are; it asserts no formula to read.
                    let introduced = (h.kind == Intro::Let)
                        .then(|| Introduction::read(h.body(&other.path)));
                    match introduced.map(|i| i.form) {
                        Some(Form::Graph(graph)) | Some(Form::GraphListed(graph)) => {
                            let name = graph.graph.clone();
                            let theirs = spare
                                .pop_front()
                                .expect("a class for each let")
                                .to_string();
                            if let Some(term) = values.get(&name) {
                                me.names.insert(name.clone(), term.clone());
                            } else if !saved.contains_key(&name) {
                                me.names.insert(name.clone(), t!(theirs));
                            }
                            // A graph given in full names its vertices and
                            // edges too, each what the citing proof calls by
                            // the same name.
                            for listed in graph
                                .listed
                                .iter()
                                .flat_map(|l| l.vertices.iter().chain(&l.edges))
                            {
                                if !saved.contains_key(listed) {
                                    let theirs = spare
                                        .pop_front()
                                        .expect("a class for each thing listed");
                                    me.names.insert(listed.clone(), t!(theirs));
                                }
                            }
                            continue;
                        }
                        // A group's line names the group's set and its
                        // identity, which are the citing proof's group's
                        // where it lets one by the same names, and a class
                        // of their own where it does not.
                        Some(Form::Group {
                            group,
                            finite,
                            identity,
                        }) => {
                            let theirs = spare
                                .pop_front()
                                .expect("a class for each let")
                                .to_string();
                            if !saved.contains_key(&group) {
                                me.group(&group, finite, &identity, &theirs);
                            }
                            continue;
                        }
                        _ => {}
                    }
                    // Parsed with the theorem's own sorts, which say what its
                    // letters are; only its shape and name are used here.
                    let said = h.body(&other.path);
                    let node = me.in_its_names(Item::Theorem(other), |me| {
                        me.hypothesis_node(h.kind, &said)
                    })?;
                    // `let X be a set` and `let A be a point` name a class as
                    // surely as `let n ∈ ℕ` does, and the name is in the same
                    // place.
                    if h.kind == Intro::Let
                        && matches!(
                            node.notation(),
                            MEMBERSHIP
                                | EXISTS
                                | IS_A_POINT
                                | CONJUNCTION
                                | FUNCTION_TYPE
                        )
                    {
                        let name = node.leftmost().text.to_string();
                        let theirs = spare
                            .pop_front()
                            .expect("a class for each let")
                            .to_string();
                        // A letter neither the citation nor the match fixes
                        // stands for what the citing proof calls by the same
                        // word, or for a class of its own. Each is given, so
                        // that a letter the theorem binds is moved off what
                        // it stands for (`apart_from_values`): grow-by-one's
                        // v may be a point the citing proof holds as w.
                        if let Some(term) = values
                            .get(&name)
                            .or_else(|| matched.get(&name))
                            .or_else(|| saved.get(&name))
                        {
                            let class = if apart.contains(&name) {
                                let Some(own) = unheld.next() else {
                                    return Err(me.defect(
                                        step.line,
                                        "no class is left to read the cited theorem's letter apart from what the citation gives it",
                                    ));
                                };
                                me.names.insert(name.clone(), t!(own));
                                t!(own)
                            } else {
                                me.names.insert(name.clone(), term.clone());
                                t!(theirs)
                            };
                            given.push(Given {
                                name: name.clone(),
                                class,
                                term: term.clone(),
                            });
                        } else {
                            me.names.insert(name.clone(), t!(theirs));
                        }
                    }
                }
                // Read in its own file's definitions, as its conclusion is below.
                let wanted =
                    me.in_its_names(Item::Theorem(other), |me| -> Checked<Vec<Rpn>> {
                        let mut out = Vec::new();
                        for h in &other.hypotheses {
                            // A graph's line asks that the graph be an
                            // undirected multigraph, as it says in its own
                            // theorem (`Elaborator::graph`).
                            let body = h.body(&other.path);
                            if h.kind == Intro::Let {
                                let introduced = Introduction::read(body.clone());
                                match &introduced.form {
                                    Form::Graph(graph) | Form::GraphListed(graph) => {
                                        let class = me.names[&graph.graph].clone();
                                        out.push(me.graph_said(
                                            graph,
                                            &class,
                                            &introduced,
                                        )?);
                                        continue;
                                    }
                                    // A group's line asks that the structure
                                    // its set is the base of be a group, and
                                    // its set finite where it says so
                                    // (`Elaborator::group`).
                                    Form::Group { group, finite, .. } => {
                                        let base = me.names[group].clone();
                                        let structure = (base.len() > 2
                                            && base.ends_with(&["cbs", "cfv"]))
                                        .then(|| {
                                            Rpn::from(&base.tokens()[..base.len() - 2])
                                        });
                                        let Some(structure) = structure else {
                                            return Err(me.defect(
                                                step.line,
                                                format!(
                                                    "{group} is no group's set here"
                                                ),
                                            ));
                                        };
                                        let mut asked = t!(structure, "cgrp", "wcel");
                                        if *finite {
                                            asked = t!(
                                                asked,
                                                t!(base, "cfn", "wcel"),
                                                "wa"
                                            );
                                        }
                                        out.push(asked);
                                        continue;
                                    }
                                    _ => {}
                                }
                            }
                            let node = me.hypothesis_node(h.kind, &body)?;
                            out.push(me.term(&node)?);
                        }
                        Ok(out)
                    })?;
                // The step may claim one sentence of a conclusion that says
                // several, or the conclusion in other words.
                let stated = me.in_its_names(Item::Theorem(other), |me| {
                    me.claim_of(&other.stated())
                })?;
                // What the cited label proves is its statement over its own
                // letters, which the claim may bind otherwise; the two are
                // joined below, not taken to be one.
                let mut whole = stated.clone();
                if other.stated().sentences().len() > claimed {
                    whole = stated;
                }
                Ok(Reading {
                    wanted,
                    whole,
                    given,
                })
            }
        };
        let first = self.names_and_sets_kept(|me| read(me, &BTreeSet::new()))?;
        let (wanted, whole) = self.apart_from_values(first, |me, apart| {
            me.names_and_sets_kept(|me| read(me, apart))
        })?;
        // A cited theorem asks for what it asks for, and a hypothesis a
        // reader would not think to write as a line is written as a
        // `requires` instead, or settled as a side condition. What the step
        // cites is laid over the scope, as `apply_lemma` lays it: a line and
        // a hypothesis may state one claim, and the step names the line.
        // What a cited line says beyond itself is read as `apply_lemma`
        // reads it: `let j ∈ ℕ` also says j ≥ 1 (`with_implied`).
        let known = self.known_implied(Some(step), scope, facts)?;
        for one in &wanted {
            // A membership the page says once is taken from where it says
            // it, and not from the scope's copy of a line the step does not
            // name.
            if let Built(p) = self.said_once_proof(&self.to_term(one), scope, &known)? {
                self.know(&known, one.clone(), p);
                continue;
            }
            // Held where the step may rest on it, as everything in `known`
            // is (`in_hand`).
            if self.holds(&known, one) {
                continue;
            }
            // A hypothesis that is an identity once its identity elements
            // are dropped, 1 = 0 + 1 at i := 0, needs no line (`SYNTAX.md`).
            match self.settle_or_bare(&self.to_term(one), scope, &known, None, None)? {
                Built(p) => self.know(&known, one.clone(), p),
                Declined(_) => {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "nothing supplies {}, which {} assumes",
                            self.render(one),
                            step.just.head
                        ),
                    ));
                }
            }
        }
        let mut pair = wanted.first().cloned();
        let mut proof = match &pair {
            Some(p) => Some(
                self.held(&known, p, scope)?
                    .expect("a hypothesis just supplied"),
            ),
            None => None,
        };
        for extra in wanted.iter().skip(1) {
            let held = self
                .held(&known, extra, scope)?
                .expect("a hypothesis just supplied");
            let p = pair.clone().unwrap();
            proof = Some(pf!(self.b; scope, p, extra, proof.unwrap(), held, "jca"));
            pair = Some(t!(p, extra, "wa"));
        }
        let mut applied = match &pair {
            Some(pair) => t!(pair, whole, "wi"),
            None => whole.clone(),
        };
        let mut pushed = self.cited_pushes(step, &full, &applied)?;
        // The theorem keeps its bound letters apart, and a class put in it
        // that binds one of them again would hand two of them one letter:
        // its statement is read with its own letters moved off
        // (`unshadowed`), and `concluded` carries that back to the claim.
        let mut whole = whole;
        if pushed.letters_meet() {
            let Some(unshadowed) = self.unshadowed(&self.to_term(&whole)) else {
                return Err(self.defect(
                    step.line,
                    "no letter is left to move the cited theorem's bound letters apart from the classes put in it",
                ));
            };
            whole = self.rpn(&unshadowed);
            applied = match &pair {
                Some(pair) => t!(pair, whole, "wi"),
                None => whole.clone(),
            };
            pushed = self.cited_pushes(step, &full, &applied)?;
        }
        let cited = label_of(
            &full,
            &self.b.sigs,
            self.b.syntax(),
            &self.thm.path,
            self.thm.line,
        )?;
        // The cited theorem is proved in another file, so the library does
        // not hold it; what it takes is what is being pushed, and what it
        // states is its file's statement, which the build's own check of
        // each application reads (`Builder::fault`). Kept apart from the
        // signatures, which `label_of` reads.
        if !self.b.arities.contains_key(&cited) {
            self.b.arities.insert(
                cited.clone(),
                Signature {
                    label: Symbol::of(&cited),
                    kind: Kind::Theorem,
                    statement: pushed.statement.clone(),
                    floats: pushed.floats.clone(),
                    essentials: Vec::new(),
                    disjoint: BTreeSet::new(),
                },
            );
        }
        let pushed = pushed.values;
        // A theorem that assumes nothing states its conclusion outright.
        let mut parts: Vec<crate::mm::spell::Part> = Vec::new();
        let proof = match (&pair, &proof) {
            (Some(pair), Some(given)) => {
                parts.push(super::super::part(scope));
                parts.push(super::super::part(pair));
                parts.push(super::super::part(&whole));
                parts.push(super::super::part(given));
                parts.extend(pushed.iter().map(|p| super::super::part(p)));
                parts.push(super::super::part(&cited));
                parts.push(super::super::part("syl"));
                self.b.proof(&parts)
            }
            _ => {
                parts.push(super::super::part(&whole));
                parts.push(super::super::part(scope));
                parts.extend(pushed.iter().map(|p| super::super::part(p)));
                parts.push(super::super::part(&cited));
                parts.push(super::super::part("a1i"));
                self.b.proof(&parts)
            }
        };
        // A theorem of this file stated over the file's own defines speaks of
        // them by name, as the citing step does, so the step reads them as
        // the statement does without citing them, as the checker reads it.
        let kept = self.resting.clone();
        let over = crate::sorts::stated_over(self.thm, self.scopes, &other.qualified());
        if let Some(allowed) = &mut self.resting {
            allowed.extend(over);
            allowed.extend(recursive);
        }
        // What the step writes and cites is what reading the statement over
        // the step's own terms may ask: e(n) ∈ ℤ, to read s at e(n).
        let read = self.with_cited(Some(step), scope, &known, None)?;
        let offered = self.in_hand(&facts.with(&read));
        let concluded = self.concluded(step, term, &whole, proof, scope, &offered);
        self.resting = kept;
        concluded
    }

    /// The cited theorem's hypotheses and statement with what its letters
    /// stand for put in, where a value holds a letter the theorem binds:
    /// `f := t`, with t held as k, into `for all k ∈ ℕ, f(k) = k + 1` would
    /// read t's k as the theorem's. A theorem is applied at whatever letters
    /// the build gives its bound ones, so the theorem's k is moved to one
    /// nothing holds, and the value put in after: the theorem is read again
    /// with those letters as classes of their own (`again`), and the classes
    /// and letters substituted together. A value that binds the letter
    /// itself, as a map does, is moved apart from the same way. A reading
    /// where no value writes a letter the theorem binds is kept as it is.
    pub(in crate::elab) fn apart_from_values(
        &mut self,
        first: Reading,
        again: impl FnOnce(&mut Self, &BTreeSet<String>) -> Checked<Reading>,
    ) -> Checked<(Vec<Rpn>, Rpn)> {
        let bound_in = |me: &Self, reading: &Reading| -> BTreeSet<String> {
            reading
                .wanted
                .iter()
                .chain(std::iter::once(&reading.whole))
                .flat_map(|t| me.letters_bound(&me.to_term(t)))
                .map(|v| v.to_string())
                .collect()
        };
        // The letters a value writes, free or bound: a map the value binds
        // n in, put where the theorem binds n around it, gives the kernel a
        // renaming onto n of a body that already binds n, which `cbvralvw`
        // and the theorem's own disjointness refuse.
        let spelt_in = |me: &Self, term: &Rpn| -> BTreeSet<String> {
            term.tokens()
                .iter()
                .filter(|t| me.is_setvar(t))
                .filter_map(|t| me.var_of(t).variable().map(String::from))
                .collect()
        };
        let bound = bound_in(self, &first);
        let apart: BTreeSet<String> = first
            .given
            .iter()
            .filter(|g| !spelt_in(self, &g.term).is_disjoint(&bound))
            .map(|g| g.name.clone())
            .collect();
        if apart.is_empty() {
            return Ok((first.wanted, first.whole));
        }
        let second = again(self, &apart)?;
        let held: BTreeSet<String> = second
            .given
            .iter()
            .filter(|g| apart.contains(&g.name))
            .flat_map(|g| spelt_in(self, &g.term))
            .collect();
        let moving: Vec<Symbol> = bound_in(self, &second)
            .intersection(&held)
            .map(|v| Symbol::of(v))
            .collect();
        let terms: Vec<Term> = second
            .wanted
            .iter()
            .chain(std::iter::once(&second.whole))
            .chain(second.given.iter().map(|g| &g.term))
            .map(|t| self.to_term(t))
            .collect();
        let refs: Vec<&Term> = terms.iter().collect();
        let Some(mut binding) = self.unheld_for(moving, &refs) else {
            return Err(self.defect(
                self.at,
                "no letter is left to move the cited theorem's bound letters apart from what the citation gives it",
            ));
        };
        for g in second.given.iter().filter(|g| apart.contains(&g.name)) {
            if let Some(class) = self.to_term(&g.class).variable_symbol() {
                binding.insert(class, self.to_term(&g.term));
            }
        }
        let put = |me: &Self, t: &Rpn| me.rpn(&me.to_term(t).substitute(&binding));
        Ok((
            second.wanted.iter().map(|t| put(self, t)).collect(),
            put(self, &second.whole),
        ))
    }

    /// ( scope -> term ) from the cited theorem's statement `whole`, proved
    /// by `proof`: the statement itself, over other bound letters, or one
    /// sentence of it said in other words.
    pub(super) fn concluded(
        &mut self,
        step: &Step,
        term: &Rpn,
        whole: &Rpn,
        proof: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let whole = whole.clone();
        if *term == whole {
            return Ok(proof);
        }
        // The claim over other bound letters: one claim, renamed closed by
        // way of letters nothing holds (`renaming_apart`).
        if self.rebound(&whole, term) {
            if let Some(across) = self.renaming_apart(&whole, term)? {
                let turned = pf!(self.b; t!(whole, term, "wb"), scope, across, "a1i");
                return Ok(pf!(self.b; scope, whole, term, proof, turned, "mpbid"));
            }
        }
        // The claim over other bound letters and with a defined name where
        // the statement has what it names, as J(n + 1) the statement writes
        // as its integral: renamed onto the claim read through its names,
        // and that read back to the claim as written.
        let claim = self.to_term(term);
        let read = self.read_out(&claim);
        let read_rpn = self.rpn(&read);
        if read_rpn != *term && self.rebound(&whole, &read_rpn) {
            if let Some(across) = self.renaming_apart(&whole, &read_rpn)? {
                if let Built(alike) = self.same(&read, &claim, scope, facts, None)? {
                    let turned =
                        pf!(self.b; t!(whole, read_rpn, "wb"), scope, across, "a1i");
                    let there =
                        pf!(self.b; scope, whole, read_rpn, proof, turned, "mpbid");
                    return Ok(
                        pf!(self.b; scope, read_rpn, term, there, alike, "mpbid"),
                    );
                }
            }
        }
        let taken = Facts::new();
        self.know(&taken, whole.clone(), proof.clone());
        self.unpack_all(&whole, &proof, scope, &taken);
        if let Some(p) = self.held(&taken, term, scope)? {
            return Ok(p);
        }
        for (one, shown) in taken.entries() {
            if let Built(alike) =
                self.same(&self.to_term(&one), &self.to_term(term), scope, facts, None)?
            {
                return Ok(pf!(self.b; scope, one, term, shown, alike, "mpbid"));
            }
        }
        // Or the claim with its identity elements dropped, as the checker
        // compares the two (`SYNTAX.md`, "An identity element goes without
        // saying"): at n := 0 the statement says J(0 + 1), and the step J(1).
        // Where the statement writes a defined name out, the claim is read
        // through its names too.
        for (one, shown) in taken.entries() {
            if let Some(p) = self.tidied(&shown, &one, term, scope, facts)? {
                return Ok(p);
            }
            // The statement's identity elements dropped where it stands,
            // over its own bound letters, then renamed onto the claim read
            // through its names: J(0 + 1) written out binds t, and the
            // claim's J(1) read out binds a letter of its own.
            // Both are compared bare, since dropping may take more from the
            // statement than the claim leaves out: t^(2·(0 + 1)) is t² bare,
            // where the claim read out says i^(2·1).
            let bare = self.rpn(&self.without_identities(&self.to_term(&one)));
            let bare_read = self.rpn(&self.without_identities(&read));
            if bare != one && read_rpn != *term && self.rebound(&bare, &bare_read) {
                if let Some(dropped) = self.tidied(&shown, &one, &bare, scope, facts)? {
                    if let Some(across) = self.renaming_apart(&bare, &bare_read)? {
                        let turned = pf!(self.b; t!(bare, bare_read, "wb"), scope, across, "a1i");
                        let renamed = pf!(self.b; scope, bare, bare_read, dropped, turned, "mpbid");
                        if let Some(there) =
                            self.tidied(&renamed, &bare_read, &read_rpn, scope, facts)?
                        {
                            if let Built(alike) =
                                self.same(&read, &claim, scope, facts, None)?
                            {
                                return Ok(
                                    pf!(self.b; scope, read_rpn, term, there, alike, "mpbid"),
                                );
                            }
                        }
                    }
                }
            }
            if read_rpn != *term {
                if let Some(there) =
                    self.tidied(&shown, &one, &read_rpn, scope, facts)?
                {
                    if let Built(alike) =
                        self.same(&read, &claim, scope, facts, None)?
                    {
                        return Ok(
                            pf!(self.b; scope, read_rpn, term, there, alike, "mpbid"),
                        );
                    }
                }
            }
        }
        // A sentence "A ↔ B" with a line stating A gives B, and B gives A;
        // "if A then B" with A gives B (`SYNTAX.md`, the conventions at
        // every citation).
        for (one, shown) in taken.entries() {
            let node = self.to_term(&one);
            let label = node.label().map(String::from);
            let [a, b] = node.children() else {
                continue;
            };
            let (a, b) = (self.rpn(a), self.rpn(b));
            let ways: Vec<(&Rpn, &Rpn, &str)> = match label.as_deref() {
                Some("wb") => vec![(&a, &b, "mpbid"), (&b, &a, "mpbird")],
                Some("wi") => vec![(&a, &b, "mpd")],
                _ => continue,
            };
            for (given, got, rule) in ways {
                let Some(held) = self.held(facts, given, scope)? else {
                    continue;
                };
                let reached = match rule {
                    "mpbird" => pf!(self.b; scope, got, given, held, shown, "mpbird"),
                    _ => pf!(self.b; scope, given, got, held, shown, rule),
                };
                if got == term {
                    return Ok(reached);
                }
                if let Built(alike) = self.same(
                    &self.to_term(got),
                    &self.to_term(term),
                    scope,
                    facts,
                    None,
                )? {
                    return Ok(pf!(self.b; scope, got, term, reached, alike, "mpbid"));
                }
            }
        }
        Err(self.defect(
            step.line,
            format!(
                "{} does not conclude what step {} claims",
                step.just.head, step.number
            ),
        ))
    }
}
