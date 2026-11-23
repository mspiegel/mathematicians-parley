//! Citing a theorem the corpus proves.

use std::collections::VecDeque;
use std::{iter, slice};

use super::cited_items::ShownPart;
use super::unfolds::{PlacedTrees, RecordedSupply};
use super::*;
use crate::checker::record::{Facing, Supplied, SuppliedBy};
use crate::citing::Way as Read;
use crate::corpus::records::LemmaReading;
use crate::corpus::Hypothesis;
use crate::matching::{Meeting, Tree};
use crate::notations::{EQUALITY, FOR_ALL, THERE_IS, TIMES};
use crate::sorts;

impl<'a> Elaborator<'a> {
    /// ( scope -> one ) for the hypothesis `h` of a cited theorem, read as
    /// this elaborator states it (`hypothesis_node`), from what the checker
    /// recorded as supplying it (`entry`). What only set.mm asks of a `let`
    /// is the elaborator's own (`own_hypothesis`): that a point, a set, an
    /// element, a group or a graph is one, whatever the record names; and
    /// beside what `a ∉ X` and `let f : A → B be one-to-one` say, that a is
    /// a set and f's type, the left of the "and" the reading makes.
    #[allow(clippy::too_many_arguments)]
    fn hypothesis_supplied(
        &mut self,
        step: &Step,
        h: &Hypothesis,
        path: &str,
        entry: Option<&Supplied>,
        values: &NodeBinding,
        one: &Rpn,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Proof> {
        let form =
            (h.kind == Intro::Let).then(|| Introduction::read(h.body(path)).form);
        let kind_only = matches!(
            form,
            Some(
                Form::Point(_)
                    | Form::Set(_)
                    | Form::Element(_)
                    | Form::Group { .. }
                    | Form::Graph(_)
                    | Form::GraphListed(_)
            )
        );
        if kind_only {
            return self.own_hypothesis(step, one, scope, known);
        }
        let Some(entry) = entry else {
            return Err(self.unreached(
                step.line,
                format!(
                    "the checker recorded nothing supplying {}",
                    self.render(one)
                ),
            ));
        };
        let split = matches!(form, Some(Form::NotIn(_) | Form::FunctionBeing { .. }));
        let node = self.to_term(one);
        let (own, recorded) = match (split, node.label(), node.children()) {
            (true, Some("wa"), [left, right]) => {
                (Some(self.rpn(left)), self.rpn(right))
            }
            _ => (None, one.clone()),
        };
        let Some(given) = self.supplied_proof(
            step,
            &entry.by,
            Some(RecordedSupply {
                supplied: entry,
                values,
            }),
            &recorded,
            scope,
            known,
        )?
        else {
            // The checker accepts the step and names what supplies the
            // hypothesis; the build that cannot use it has a gap.
            return Err(self.defect(
                step.line,
                format!(
                    "what the checker recorded as supplying {} does not give it",
                    self.render(&recorded)
                ),
            ));
        };
        let Some(own) = own else {
            return Ok(given);
        };
        let left = self.own_hypothesis(step, &own, scope, known)?;
        Ok(pf!(self.b; scope, own, recorded, left, given, "jca"))
    }

    /// ( scope -> one ) for what only set.mm asks of a cited theorem's
    /// hypothesis, which no page line writes: that a point is a complex
    /// number, a class a set, a structure a group, and a function's type a
    /// line keeps apart from its claim. Said once where the page lets the
    /// letter, held among the step's facts, or built from the term's
    /// structure (`settle_or_bare`).
    fn own_hypothesis(
        &mut self,
        step: &Step,
        one: &Rpn,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Proof> {
        if let Built(p) = self.said_once_proof(&self.to_term(one), scope, known)? {
            return Ok(p);
        }
        if let Some(p) = self.held(known, one, scope)? {
            return Ok(p);
        }
        match self.settle_or_bare(&self.to_term(one), scope, known, None, None)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                step.line,
                format!(
                    "nothing supplies {}, which {} assumes",
                    self.render(one),
                    step.just.head
                ),
            )),
        }
    }

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
            let mut spare: VecDeque<&str> = CLASS_NAMES.iter().copied().collect();
            let mut given: Vec<Given> = Vec::new();
            {
                let saved = me.names.clone();
                // Every value is read in the step's own names before any
                // letter of the theorem is given one: `a := b/k, b := a/k`
                // swaps the two, and reading the second after the first is
                // given would read a/k as (b/k)/k. What the citation does
                // not write is what the checker's match gives it
                // (`citing::taken`, SYNTAX.md "No pair says what goes
                // without saying"): `A ⊆ B ∪ A` cited for `B ⊆ A ∪ B` puts
                // B for A and A for B.
                let values = me.corpus_matched(step, other)?;
                // A letter read apart stands for a class no value and no name
                // of the step writes, since the value is put back in for that
                // class over the whole reading: the citing proof's own first
                // `let` is cA, as the theorem's is.
                let held: BTreeSet<&str> = saved
                    .values()
                    .chain(values.values())
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
                        if let Some(term) =
                            values.get(&name).or_else(|| saved.get(&name))
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
        // Each hypothesis from what the checker recorded as supplying it
        // (`Cited::supplied`, by the hypothesis's place), with what a cited
        // line says beyond itself read as `apply_lemma` reads it: `let j ∈
        // ℕ` also says j ≥ 1 (`with_implied`).
        let known = self.known_implied(Some(step), scope, facts)?;
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let values = cited.binding_with_written();
        for (i, (one, h)) in wanted.iter().zip(&other.hypotheses).enumerate() {
            let entry = cited
                .supplied
                .iter()
                .find(|s| s.at.is_some_and(|a| a.line == i));
            let proof = self.hypothesis_supplied(
                step,
                h,
                &other.path,
                entry,
                &values,
                one,
                scope,
                &known,
            )?;
            self.know(&known, one.clone(), proof);
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
        let over = sorts::stated_over(self.thm, self.scopes, &other.qualified());
        if let Some(allowed) = &mut self.resting {
            allowed.extend(over);
            allowed.extend(recursive);
        }
        // What the step writes and cites is what reading the statement over
        // the step's own terms may ask: e(n) ∈ ℤ, to read s at e(n).
        let read = self.with_cited(Some(step), scope, &known, None)?;
        let offered = self.in_hand(&facts.with(&read));
        let sentences = other.stated().sentences().len();
        let concluded =
            self.concluded(step, term, &whole, sentences, proof, scope, &offered);
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
                .chain(iter::once(&reading.whole))
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
        // Each value read again as a class of its own, and put in for it
        // apart from the theorem's bound letters (`put_apart`).
        let mut values = Binding::new();
        for g in second.given.iter().filter(|g| apart.contains(&g.name)) {
            if let Some(class) = self.to_term(&g.class).variable_symbol() {
                values.insert(class, self.to_term(&g.term));
            }
        }
        let terms: Vec<Term> = second
            .wanted
            .iter()
            .chain(iter::once(&second.whole))
            .map(|t| self.to_term(t))
            .collect();
        let Some(mut put) = self.put_apart(&terms, &values, &BTreeSet::new()) else {
            return Err(self.defect(
                self.at,
                "no letter is left to move the cited theorem's bound letters apart from what the citation gives it",
            ));
        };
        let whole = put.pop().map(|t| self.rpn(&t));
        let wanted = put.iter().map(|t| self.rpn(t)).collect();
        match whole {
            Some(whole) => Ok((wanted, whole)),
            None => Err(self.defect(self.at, "a cited theorem read with no statement")),
        }
    }

    /// ( scope -> term ) from the cited theorem's statement `whole`, of
    /// `sentences` sentences, proved by `proof`, as the checker recorded the
    /// citation reads it (`Cited::concluded`). The claim is taken apart
    /// into its conjuncts, as the checker takes it apart (`conjuncts`), and
    /// each is the sentence the record names, or the part of that sentence,
    /// read the way it names, and carried as the record says the two meet
    /// (`met_as`). An obtain takes its "there is" whole, the sentence the
    /// record names (`Cited::obtained`), over the letters the step obtains.
    #[allow(clippy::too_many_arguments)]
    fn concluded(
        &mut self,
        step: &Step,
        term: &Rpn,
        whole: &Rpn,
        sentences: usize,
        proof: Proof,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        if term == whole {
            return Ok(proof);
        }
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let said = self.sentences_proved(whole, proof, sentences, scope);
        if let Some(k) = cited.obtained {
            let Some((there, shown)) = said.get(k).cloned() else {
                return Err(self.unreached(
                    step.line,
                    "the checker obtains from a sentence the cited theorem does not have",
                ));
            };
            let renamed = Meeting {
                renamed: true,
                ..Meeting::default()
            };
            return match self.met_as(
                &there,
                shown,
                term,
                &renamed,
                Tree::First,
                scope,
                facts,
            )? {
                Some(p) => Ok(p),
                None => Err(self.unreached(
                    step.line,
                    format!(
                        "the sentence the checker obtains from says {}, and the step obtains {}",
                        self.render(&there),
                        self.render(term)
                    ),
                )),
            };
        }
        let mut readings = Vec::new();
        for concluded in &cited.concluded {
            let Some((sentence, shown)) = said.get(concluded.sentence).cloned() else {
                return Err(self.unreached(
                    step.line,
                    "the checker concluded a sentence the cited theorem does not have",
                ));
            };
            readings.push(self.read_way(
                step,
                &sentence,
                shown,
                concluded.way,
                scope,
                facts,
            )?);
        }
        self.claim_from_readings(step, term, &cited, readings, scope, facts)
    }

    /// ( scope -> term ), the claim taken apart as the checker takes it
    /// apart (`claim_parts`), each part from the reading the checker
    /// concluded it from, `readings[k]` for `Cited::concluded[k]`: that
    /// reading, or the part of it the record names (`concluded_part`),
    /// carried as the record says the two meet (`met_as`).
    pub(in crate::elab) fn claim_from_readings(
        &mut self,
        step: &Step,
        term: &Rpn,
        cited: &Cited,
        readings: Vec<(Rpn, Proof)>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        // One conclusion gives the claim whole, however many parts it has:
        // a group concluding one statement letter (`citing::taken`), and a
        // claim proved where the page's sentence is not what is proved, a
        // chain link under a sum or a step at one member.
        let pieces = match cited.concluded.len() {
            1 => vec![term.clone()],
            _ => self.claim_parts(step)?,
        };
        if pieces.len() != cited.concluded.len() || readings.len() != pieces.len() {
            return Err(self.unreached(
                step.line,
                format!(
                    "the claim has {} parts, and the checker concluded {}",
                    pieces.len(),
                    cited.concluded.len()
                ),
            ));
        }
        // What carries a reading to the claim asks as a lemma does, from
        // what the step names: a define read at its arguments asks each is
        // a set.
        let supplied = self.supplied(Some(step), scope, facts)?;
        let held = self.with_cited(Some(step), scope, &supplied, None)?;
        let mut proved = Vec::new();
        for (k, (piece, (read, shown))) in pieces.into_iter().zip(readings).enumerate()
        {
            let (part, shown) = match self.concluded_part(step, cited, k)? {
                None => (read, shown),
                Some(target) => match self.conjunct_proof(&read, shown, &target, scope)
                {
                    Some(at) => at,
                    None => {
                        return Err(self.unreached(
                            step.line,
                            format!(
                                "the checker concluded {} from a part, {}, the reading does not have",
                                self.render(&piece),
                                self.render(&target)
                            ),
                        ));
                    }
                },
            };
            let Some(met) = cited.meetings.get(k).cloned().flatten() else {
                return Err(self.unreached(
                    step.line,
                    "the checker recorded no meeting of the reading with the claim",
                ));
            };
            // Identity elements the record drops, and defines it reads out,
            // are dropped and read out where it places them, in the two
            // trees it met (`Cited::met_trees`), as the item writes its
            // sentence (`carried_at_places`).
            if !met.identities.is_empty() || !met.unfolded.is_empty() {
                let Some(trees) = cited.met_trees.get(k).cloned().flatten() else {
                    return Err(self.unreached(
                        step.line,
                        "the checker recorded no trees for a meeting it placed identities or read-outs in",
                    ));
                };
                let placed = PlacedTrees {
                    said: trees.item,
                    wanted: trees.claim,
                    said_in: Tree::First,
                };
                let Some(proof) = self.carried_at_places(
                    step, &part, shown, &piece, &placed, &met, scope, &held,
                )?
                else {
                    return Err(self.defect(
                        step.line,
                        format!(
                            "{} gives {}, and the checker read it as the claim's {} with identity elements dropped or defines read out",
                            step.just.head,
                            self.render(&part),
                            self.render(&piece)
                        ),
                    ));
                };
                proved.push(ShownPart { want: piece, proof });
                continue;
            }
            // An equation the record says faces the claim's the other way
            // round is turned first, by its own lemma (`Cited::facings`).
            let (part, shown) = match cited.facings.get(k).copied().flatten() {
                Some(Facing::Turned) => {
                    let Some((turned, flip)) = self.turned_claim(&part) else {
                        return Err(self.unreached(
                            step.line,
                            "the checker turned a reading that is no equation",
                        ));
                    };
                    let Sides { left, right } = self.equation_sides(&part);
                    (turned, pf!(self.b; scope, left, right, shown, flip))
                }
                _ => (part, shown),
            };
            match self.met_as(&part, shown, &piece, &met, Tree::First, scope, &held)? {
                Some(proof) => proved.push(ShownPart { want: piece, proof }),
                None => {
                    return Err(self.unreached(
                        step.line,
                        format!(
                            "{} gives {}, and the checker read it as the claim's {}",
                            step.just.head,
                            self.render(&part),
                            self.render(&piece)
                        ),
                    ));
                }
            }
        }
        let mut proved = proved.into_iter().peekable();
        match self.joined_from(&self.to_term(term), &mut proved, scope) {
            Some(p) if proved.peek().is_none() => Ok(p),
            _ => Err(self.unreached(
                step.line,
                format!(
                    "the claim {} is not the parts the checker took it apart into",
                    self.render(term)
                ),
            )),
        }
    }

    /// Each part of the step's claim as the checker takes it apart, sentence
    /// by sentence (`citing::conjuncts`), as a term: "P, Q, R form a
    /// triangle" is one part, though set.mm writes it as an "and". While a
    /// step said of every member is proved at one (`Elaborator::member`),
    /// what is proved is the body of its "for all", and that is taken
    /// apart.
    pub(in crate::elab) fn claim_parts(&mut self, step: &Step) -> Checked<Vec<Rpn>> {
        let library = self.item_library();
        let mut out = Vec::new();
        for sentence in step.claim.sentences() {
            let mut node = self.read(&sentence)?;
            if self.member.is_some() && node.notation() == FOR_ALL {
                if let Some(body) = node.children.last() {
                    node = body.clone();
                }
            }
            for part in citing::conjuncts(&node, &library) {
                out.push(self.term(&part)?);
            }
        }
        Ok(out)
    }

    /// The part of the item's sentence the checker concluded the claim's
    /// part `k` from, as a term at the citation's values
    /// (`Cited::binding_with_written`): the sentence read the recorded way
    /// (`citing::readings`), the part of that reading the record names
    /// (`Concluded::part`), and the part of that a property applied gives,
    /// read as its body (`Cited::within`). None where the record takes the
    /// reading whole.
    fn concluded_part(
        &mut self,
        step: &Step,
        cited: &Cited,
        k: usize,
    ) -> Checked<Option<Rpn>> {
        let Some(concluded) = cited.concluded.get(k) else {
            return Ok(None);
        };
        let within = cited.within.get(k).copied().flatten();
        if concluded.part.is_none() && within.is_none() {
            return Ok(None);
        }
        let library = self.item_library();
        let unread = |me: &Self| {
            me.unreached(
                step.line,
                "the checker concluded a part the item does not have",
            )
        };
        let mut node =
            self.reading_node(step, cited, concluded.sentence, concluded.way)?;
        if let Some(i) = concluded.part {
            let Some(part) = citing::conjuncts(&node, &library).get(i).cloned() else {
                return Err(unread(self));
            };
            node = part;
        }
        let binding: NodeBinding = cited.binding_with_written().into_iter().collect();
        node = filled(&node, &binding, &library.ctx);
        if let Some(w) = within {
            let Some(part) = citing::conjuncts(&node, &library).get(w).cloned() else {
                return Err(unread(self));
            };
            node = part;
        }
        Ok(Some(self.term(&node)?))
    }

    /// Sentence `sentence` of the cited item, counted across its groups,
    /// read `way` (`citing::readings`), in the item's letters.
    fn reading_node(
        &mut self,
        step: &Step,
        cited: &Cited,
        sentence: usize,
        way: Read,
    ) -> Checked<Node> {
        let library = self.item_library();
        let found = library.groups(&cited.item).and_then(|groups| {
            let said = groups.iter().flat_map(|g| g.gives.iter()).nth(sentence)?;
            citing::readings(said, &library)
                .into_iter()
                .find(|r| r.way == way)
                .map(|r| r.claimed)
        });
        found.ok_or_else(|| {
            self.unreached(
                step.line,
                "the checker read a sentence the item does not have",
            )
        })
    }

    /// The reading of the cited item the checker took the claim from, as a
    /// term at the citation's values (`Cited::binding_with_written`): the
    /// sentence of its first conclusion read the recorded way, or the
    /// sentence an obtain obtains from, read forwards; written as `spelt`
    /// says its lemma writes it, in the item's letters before the values
    /// are put in, so a product a value holds is left as it stands.
    pub(in crate::elab) fn concluded_reading(
        &mut self,
        step: &Step,
        cited: &Cited,
        spelt: LemmaReading,
    ) -> Checked<Term> {
        let (sentence, way) = match (cited.concluded.first(), cited.obtained) {
            (Some(c), _) => (c.sentence, c.way),
            (None, Some(k)) => (k, Read::Forward),
            (None, None) => {
                return Err(self.unreached(
                    step.line,
                    "the checker recorded no reading of this citation",
                ))
            }
        };
        self.sentence_read(step, cited, sentence, way, spelt)
    }

    /// Sentence `sentence` of the cited item read `way`, as a term at the
    /// citation's values (`Cited::binding_with_written`), written as
    /// `spelt` says its lemma writes it, in the item's letters before the
    /// values are put in, so a product a value holds is left as it stands.
    pub(in crate::elab) fn sentence_read(
        &mut self,
        step: &Step,
        cited: &Cited,
        sentence: usize,
        way: Read,
        spelt: LemmaReading,
    ) -> Checked<Term> {
        let mut node = self.reading_node(step, cited, sentence, way)?;
        if spelt.turned {
            node = equation_turned(&node);
        }
        if spelt.factors_swapped {
            node = factors_swapped(&node);
        }
        let library = self.item_library();
        let binding: NodeBinding = cited.binding_with_written().into_iter().collect();
        let filled = filled(&node, &binding, &library.ctx);
        self.read_apart(step, &filled)
    }

    /// `filled`, an item's sentence or hypothesis at a citation's values, as
    /// a term. A letter it binds whose variable a name of the proof holds is
    /// read as one nothing holds (`unheld_for`): the item's k is spelt with
    /// the variable the proof's obtained q is, and read so it would capture
    /// q; and a value's own bound letter, the X of ⋃(X ∈ D) X where the
    /// proof names an X, is read apart alike, so that the reading and the
    /// hypotheses carried to the lemma spell one set one way.
    pub(in crate::elab) fn read_apart(
        &mut self,
        step: &Step,
        filled: &Node,
    ) -> Checked<Term> {
        let mut read = self.read_apart_together(step, slice::from_ref(filled))?;
        match read.pop() {
            Some(term) => Ok(term),
            None => Err(self.defect(step.line, "no tree to read the item by")),
        }
    }

    /// `trees` read as terms as `read_apart` reads one, each letter that one
    /// of them binds and a name of the proof holds given one letter nothing
    /// holds, the same in all of them: the two trees a meeting is of spell
    /// a define's bound letter alike once it is read out in each.
    pub(in crate::elab) fn read_apart_together(
        &mut self,
        step: &Step,
        trees: &[Node],
    ) -> Checked<Vec<Term>> {
        let held = self.names_held();
        let mut bound: Vec<Symbol> = Vec::new();
        let mut rest: Vec<Node> = trees.to_vec();
        while let Some(node) = rest.pop() {
            if let Some(at) = self.binders.get(&node.notation()).cloned() {
                for at in at {
                    let letter = &node.children[at];
                    if letter.is_name()
                        && !bound.contains(&letter.text)
                        && held.contains(&self.binder_var(&letter.text)?)
                    {
                        bound.push(letter.text);
                    }
                }
            }
            rest.extend(node.children.iter().cloned());
        }
        let Some(letters) = self.unheld_for(bound, &[]) else {
            return Err(self.defect(step.line, "no letter left to read the item by"));
        };
        let kept = self.bound_as.clone();
        for (name, letter) in &letters {
            self.bound_as
                .insert(name.to_string(), self.rpn(letter).to_string());
        }
        let read: Checked<Vec<Rpn>> = trees.iter().map(|t| self.term(t)).collect();
        self.bound_as = kept;
        Ok(read?.iter().map(|r| self.to_term(r)).collect())
    }

    /// The part of the "and" `whole` that is `target` up to the letters each
    /// binds (`rebound`), with its proof from a proof of `whole`, found from
    /// the outside in: the reading's own bound letters may be spelt apart
    /// from the item's. None where it is no part.
    fn conjunct_proof(
        &mut self,
        whole: &Rpn,
        proof: Proof,
        target: &Rpn,
        scope: &Rpn,
    ) -> Option<(Rpn, Proof)> {
        if whole == target || self.rebound(whole, target) {
            return Some((whole.clone(), proof));
        }
        let node = self.to_term(whole);
        let (Some("wa" | "w3a"), 2 | 3) = (node.label(), node.children().len()) else {
            return None;
        };
        for (kid, kid_proof) in self.conjuncts_once(whole, proof, scope) {
            if let Some(found) = self.conjunct_proof(&kid, kid_proof, target, scope) {
                return Some(found);
            }
        }
        None
    }

    /// The sides of the "and" `term`, one level down, each with its proof
    /// from `proof`.
    fn conjuncts_once(
        &mut self,
        term: &Rpn,
        proof: Proof,
        scope: &Rpn,
    ) -> Vec<(Rpn, Proof)> {
        let node = self.to_term(term);
        let kids: Vec<Rpn> = node.children().iter().map(|c| self.rpn(c)).collect();
        let lemmas: &[&str] = match (node.label(), kids.len()) {
            (Some("wa"), 2) => &["simpld", "simprd"],
            (Some("w3a"), 3) => &["simp1d", "simp2d", "simp3d"],
            _ => return vec![(term.clone(), proof)],
        };
        let mut out = Vec::new();
        for (kid, lemma) in kids.iter().zip(lemmas) {
            let mut all: Vec<crate::mm::spell::Part> = vec![super::super::part(scope)];
            all.extend(kids.iter().map(|k| super::super::part(k)));
            all.push(super::super::part(&proof));
            all.push(super::super::part(*lemma));
            out.push((kid.clone(), self.b.proof(&all)));
        }
        out
    }

    /// Each of the `count` sentences `whole` joins by "and", left to right,
    /// with its proof under `scope` from `proof` of the whole (`claim_of`
    /// joins them so).
    fn sentences_proved(
        &mut self,
        whole: &Rpn,
        proof: Proof,
        count: usize,
        scope: &Rpn,
    ) -> Vec<(Rpn, Proof)> {
        if count <= 1 {
            return vec![(whole.clone(), proof)];
        }
        let node = self.to_term(whole);
        if node.label() != Some("wa") {
            return vec![(whole.clone(), proof)];
        }
        let (rest, last) =
            (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
        let first = pf!(self.b; scope, rest, last, proof.clone(), "simpld");
        let second = pf!(self.b; scope, rest, last, proof, "simprd");
        let mut out = self.sentences_proved(&rest, first, count - 1, scope);
        out.push((last, second));
        out
    }

    /// Each conjunct of `term`, every "and" taken apart left to right
    /// (`conjuncts_of`), with its proof under `scope` from `proof`.
    pub(in crate::elab) fn conjuncts_proved(
        &mut self,
        term: &Rpn,
        proof: Proof,
        scope: &Rpn,
    ) -> Vec<(Rpn, Proof)> {
        let once = self.conjuncts_once(term, proof, scope);
        if let [(one, _)] = once.as_slice() {
            if one == term {
                return once;
            }
        }
        let mut out = Vec::new();
        for (kid, taken) in once {
            out.extend(self.conjuncts_proved(&kid, taken, scope));
        }
        out
    }

    /// A cited sentence read the way the checker recorded (`Way`): as it
    /// stands; "A ↔ B" or "if A then B" with A, giving B; or "A ↔ B" with
    /// B, giving A; the A or B from where the checker recorded it stands
    /// (`Cited::firsts`).
    fn read_way(
        &mut self,
        step: &Step,
        sentence: &Rpn,
        shown: Proof,
        way: Read,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<(Rpn, Proof)> {
        if way == Read::AsWritten {
            return Ok((sentence.clone(), shown));
        }
        let node = self.to_term(sentence);
        let label = node.label().map(String::from);
        let [a, b] = node.children() else {
            return Err(self.unreached(
                step.line,
                "the checker read a sentence through, which is no ↔ or if",
            ));
        };
        let (a, b) = (self.rpn(a), self.rpn(b));
        let (given, got) = match way {
            Read::Backward => (b.clone(), a.clone()),
            _ => (a.clone(), b.clone()),
        };
        // The premise is the fact the checker read the reading from, where
        // it recorded it stands (`Cited::firsts`).
        let firsts: Vec<SuppliedBy> = self
            .citation_read(step)
            .map(|c| c.firsts.iter().flatten().map(|f| f.by.clone()).collect())
            .unwrap_or_default();
        let mut found = None;
        for by in firsts
            .iter()
            .filter(|by| !matches!(by, SuppliedBy::Unstated))
        {
            if let Some(p) =
                self.supplied_proof(step, by, None, &given, scope, facts)?
            {
                found = Some(p);
                break;
            }
        }
        let Some(held) = found else {
            return Err(self.defect(
                step.line,
                format!(
                    "{} gives {} where {} holds, and the line the checker read that from does not give it",
                    step.just.head,
                    self.render(&got),
                    self.render(&given)
                ),
            ));
        };
        let reached = match (label.as_deref(), way) {
            (Some("wb"), Read::Forward) => {
                pf!(self.b; scope, a, b, held, shown, "mpbid")
            }
            (Some("wb"), Read::Backward) => {
                pf!(self.b; scope, a, b, held, shown, "mpbird")
            }
            (Some("wi"), Read::Forward) => pf!(self.b; scope, a, b, held, shown, "mpd"),
            _ => {
                return Err(self.unreached(
                    step.line,
                    "the checker read a sentence through, which is no ↔ or if",
                ));
            }
        };
        Ok((got, reached))
    }
}

/// `node` with the equation under its "there is" turned round, as a lemma
/// may write it (`metamath-reads turned`).
fn equation_turned(node: &Node) -> Node {
    match (node.notation(), node.children.as_slice()) {
        (THERE_IS, [letter, domain, body]) => node.with_children(vec![
            letter.clone(),
            domain.clone(),
            equation_turned(body),
        ]),
        (EQUALITY, [left, right]) => {
            node.with_children(vec![right.clone(), left.clone()])
        }
        _ => node.clone(),
    }
}

/// `node` with the two factors of each product the other way round, as a
/// lemma may write them (`metamath-reads factors swapped`).
fn factors_swapped(node: &Node) -> Node {
    if node.children.is_empty() {
        return node.clone();
    }
    let mut kids: Vec<Node> = node.children.iter().map(factors_swapped).collect();
    if node.spelling() == TIMES && kids.len() == 2 {
        kids.swap(0, 1);
    }
    node.with_children(kids)
}
