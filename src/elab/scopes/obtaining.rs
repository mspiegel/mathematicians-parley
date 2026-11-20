//! Obtaining, defines and the frames' facts.

use std::vec::IntoIter;

use super::*;
use crate::checker::record::{FirstAt, JoinedWhole};
use crate::elab;
use crate::mm::Kind;

impl<'a> Elaborator<'a> {
    /// X, where an induction runs over `over` = 𝒫X, the parts of X; None
    /// for any other set.
    pub(super) fn parts_over(&self, over: &Rpn) -> Option<Rpn> {
        let set = self.to_term(over);
        match (set.label(), set.children()) {
            (Some("cpw"), [whole]) => Some(self.rpn(whole)),
            _ => None,
        }
    }

    /// The functions from X to Y, where `over` is that set (`X ↑m Y` in
    /// set.mm, the codomain first).
    pub(super) fn function_set(&self, over: &Rpn) -> Option<FunctionSet> {
        let set = self.to_term(over);
        let kids = set.children();
        (set.label() == Some("co")
            && kids.len() == 3
            && self.rpn(&kids[2]).alone() == Some("cmap"))
        .then(|| FunctionSet {
            domain: self.rpn(&kids[1]),
            codomain: self.rpn(&kids[0]),
        })
    }

    /// How many "there is" layers open `term`, each over a set.
    pub(super) fn there_is_depth(&self, term: &Rpn) -> usize {
        let mut depth = 0;
        let mut rest = self.to_term(term);
        while rest.label() == Some("wrex") && rest.children().len() == 3 {
            depth += 1;
            rest = rest.children()[0].clone();
        }
        depth
    }

    /// Names introduced from an existence claim, which opens a scope.
    ///
    /// This is the step that changes the shape of every step after it: the
    /// kernel cannot hand a name out of an existential, so everything below
    /// is proved as the body of an implication and the existential is
    /// discharged at the very end.
    /// An obtain's line, its sentences after the memberships, from the body
    /// its "there is" gives (`body`, proved by `proof`), as the checker
    /// paired them (`pairs`, `CheckedTheorem::obtained_parts`): each part of
    /// each sentence carried from the part of the body the checker found it
    /// in (`ObtainedPart::owed_written`), as it stands, with its bound
    /// variable renamed (`renaming`), as `same` takes the one to the other,
    /// or once identity elements are dropped (`reached`); then each sentence
    /// joined from its parts, and the line from its sentences in order.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn obtained_line(
        &mut self,
        step: &Step,
        pairs: &[record::ObtainedPart],
        sentences: &[Node],
        got: usize,
        body: &Rpn,
        proof: &Proof,
        inner: &Rpn,
        lifted: &Facts,
        allowed: &BTreeSet<String>,
    ) -> Checked<(Rpn, Proof)> {
        let unpaired = |me: &Self, what: &str| {
            me.defect(step.line, format!("step {}: {what}", step.number))
        };
        let held = Facts::new();
        self.know(&held, body.clone(), proof.clone());
        self.unpack_all(body, proof, inner, &held);
        let mut line: Option<(Rpn, Proof)> = None;
        for (k, node) in sentences.iter().enumerate().skip(got) {
            let said = self.term(node)?;
            let parts =
                super::super::elaborate::parts_along(node, &self.to_term(&said));
            let mut proofs = Vec::new();
            for (j, part) in parts.iter().enumerate() {
                let Some(pair) = pairs.iter().find(|p| p.sentence == k && p.part == j)
                else {
                    return Err(unpaired(
                        self,
                        "a part the checker paired with nothing",
                    ));
                };
                // A body built as the step's claim states it
                // (`existence_claimed`) gives the part itself.
                let want = self.rpn(part);
                if let Some(itself) = self.held(&held, &want, inner)? {
                    proofs.push(itself);
                    continue;
                }
                // The body's part, found among what the body gives: as the
                // checker read it, over other bound letters (`renaming`), or
                // one claim in set.mm (`same`), as a map applied is its
                // rule at its argument.
                let written = self.term(&pair.owed_written)?;
                let mut source = None;
                for (one, p) in held.entries() {
                    let (one_term, written_term) =
                        (self.to_term(&one), self.to_term(&written));
                    let mut found = one == written
                        || self.renaming(&written_term, &one_term)?.is_some();
                    if !found {
                        let alike = self.resting_on(Some(allowed.clone()), |me| {
                            let offered = me.in_hand(lifted);
                            me.same(
                                &one_term,
                                &written_term,
                                inner,
                                &offered,
                                Some(step),
                            )
                        })?;
                        found = !alike.is_declined();
                    }
                    if found {
                        source = Some((one, p));
                        break;
                    }
                }
                let Some((owed, from)) = source else {
                    return Err(unpaired(
                        self,
                        "a part of the body its proof does not give",
                    ));
                };
                let carried = if owed == want {
                    from
                } else if let Some(same) = self.renaming(&self.to_term(&owed), part)? {
                    self.b.ap(
                        "sylib",
                        &binds! {"ph" => inner, "ps" => &owed, "ch" => &want},
                        &[&from, &same],
                    )
                } else {
                    let (to, owed_term) = (part.clone(), self.to_term(&owed));
                    let alike = self.resting_on(Some(allowed.clone()), |me| {
                        let offered = me.in_hand(lifted);
                        me.same(&owed_term, &to, inner, &offered, Some(step))
                    })?;
                    match alike {
                        Built(alike) => {
                            pf!(self.b; inner, owed, want, from, alike, "mpbid")
                        }
                        Declined(_) => {
                            let reached =
                                self.resting_on(Some(allowed.clone()), |me| {
                                    let offered = me.in_hand(lifted);
                                    me.reached(&from, &owed, &want, inner, &offered)
                                })?;
                            let Some(p) = reached else {
                                return Err(self.defect(
                                    step.line,
                                    format!(
                                        "step {} claims {}, and what it obtains says {}",
                                        step.number,
                                        self.render(&want),
                                        self.render(&owed)
                                    ),
                                ));
                            };
                            p
                        }
                    }
                };
                proofs.push(carried);
            }
            let mut proofs = proofs.into_iter();
            let Some(sentence) =
                self.joined_along(node, &self.to_term(&said), &mut proofs, inner)
            else {
                return Err(unpaired(self, "a sentence its parts do not join to"));
            };
            line = Some(match line {
                None => (said, sentence),
                Some((so_far, p)) => {
                    let both = t!(so_far, said, "wa");
                    let proof = pf!(self.b; inner, so_far, said, p, sentence, "jca");
                    (both, proof)
                }
            });
        }
        line.ok_or_else(|| unpaired(self, "no sentence after its memberships"))
    }

    /// The proof of `term`, the set.mm form of the sentence `node`, from the
    /// proofs of its parts in order (`parts_along`), joined where the
    /// sentence joins them; None where the parts run out, or the sentence
    /// is joined by other than conjunctions of two.
    pub(super) fn joined_along(
        &mut self,
        node: &Node,
        term: &Term,
        proofs: &mut IntoIter<Proof>,
        scope: &Rpn,
    ) -> Option<Proof> {
        let count = super::super::elaborate::parts_along(node, term).len();
        self.joined_tree(term, count, proofs, scope)
    }

    /// `term`, a conjunction of `count` parts, each proved in turn by
    /// `proofs`, joined by `jca` as its conjunctions nest.
    pub(super) fn joined_tree(
        &mut self,
        term: &Term,
        count: usize,
        proofs: &mut IntoIter<Proof>,
        scope: &Rpn,
    ) -> Option<Proof> {
        if count == 1 {
            return proofs.next();
        }
        if term.label() != Some("wa") {
            return None;
        }
        let (l, r) = (term.children()[0].clone(), term.children()[1].clone());
        let left_count = super::super::matcher::conjuncts_of(&l).len().min(count - 1);
        let left = self.joined_tree(&l, left_count, proofs, scope)?;
        let right = self.joined_tree(&r, count - left_count, proofs, scope)?;
        let (lr, rr) = (self.rpn(&l), self.rpn(&r));
        Some(pf!(self.b; scope, lr, rr, left, right, "jca"))
    }

    pub fn obtain(
        &mut self,
        step: &Step,
        number: &str,
        scope: &Rpn,
        whole: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        // The existence is found with what the step may rest on, and what it
        // obtains is added to the whole scope.
        let facts = &self.in_hand(whole);
        let got: Vec<String> = step.just.obtained.clone();
        let named = step.just.obtained_from.clone();
        let cited = match named.as_deref() {
            Some(n) => Some(self.item_cited(n)?),
            None => None,
        };
        let (mut ex, mut p_ex);
        match &named {
            None => {
                // The line already claims the existence, so there is no item
                // to instantiate and nothing of its own to rename.
                let where_ = step.just.refs.first().cloned();
                let held = where_
                    .as_ref()
                    .and_then(|w| self.line_written(w, &self.lines));
                let (Some(where_), Some(held)) = (where_, held) else {
                    return Err(self.unreached(
                        step.line,
                        "an obtain that names neither an item nor a line claiming the existence",
                    ));
                };
                ex = held.claim.clone();
                p_ex = self.carried(&where_, facts, &self.lines.clone());
                // A line says each of its sentences and their parts apart, and
                // a "for all" of it read at a block's letter (`line_says`), so
                // the "there is" is the one of those that binds as many names
                // as the step obtains, as the checker takes it.
                if self.there_is_depth(&ex) < got.len() {
                    let lines = self.lines.clone();
                    let says = self.line_says(&where_, scope, facts, &lines)?;
                    let found = says
                        .entries()
                        .into_iter()
                        .find(|(one, _)| self.there_is_depth(one) >= got.len());
                    if let Some((one, p)) = found {
                        ex = one;
                        p_ex = p;
                    }
                }
                // Eliminating an existential puts the name it binds into the
                // scope, and the lemma that does it forbids that name in what
                // the scope already says. So the claim is respelt first, over
                // names nothing else holds.
                let standing: BTreeSet<String> = scope
                    .tokens()
                    .iter()
                    .filter(|t| {
                        self.b
                            .sigs
                            .get(t.as_str())
                            .is_some_and(|s| s.kind == Kind::Float)
                    })
                    .map(|t| t.as_str().to_string())
                    .collect();
                let binders: Vec<String> = self
                    .bound_in(&self.to_term(&ex))
                    .iter()
                    .map(|v| self.float_of(v))
                    .collect();
                let renames = got
                    .iter()
                    .zip(binders.iter())
                    .any(|(name, letter)| self.bound_as.get(name) != Some(letter));
                if binders.iter().any(|b| standing.contains(b)) || renames {
                    let fresh = self.renamed(&ex, got.len())?;
                    let apart =
                        self.renaming(&self.to_term(&ex), &self.to_term(&fresh))?;
                    let Some(apart) = apart else {
                        return Err(self.defect(
                            step.line,
                            "the existence this obtains from binds a name the scope already holds",
                        ));
                    };
                    let turned = pf!(self.b; t!(ex, fresh, "wb"), scope, apart, "a1i");
                    p_ex = pf!(self.b; scope, ex, fresh, p_ex, turned, "mpbid");
                    ex = fresh;
                }
            }
            Some(_) if cited.is_some_and(|item| item.unfolds()) => {
                // The existence is the one the step's claim states, over
                // names nothing else holds, reached as a step claiming it
                // would reach it.
                let item = cited.expect("the guard found it");
                let claimed = self.existence_claimed(step, &got)?;
                ex = self.renamed(&claimed, got.len())?;
                let lines = self.lines.clone();
                let mut found = self.trying(
                    item,
                    step,
                    super::super::elaborate::Way::Unfolded,
                    &ex,
                    scope,
                    facts,
                    &lines,
                )?;
                // What is obtained may be an equation written the other way
                // round from the one the item gives, `a·x + b·y = d` for
                // `d = a·x + b·y`: reached turned, and carried across.
                if found.is_declined() {
                    if let Some(turned) = self.existence_turned(&ex, got.len()) {
                        if let Built(p) = self.trying(
                            item,
                            step,
                            super::super::elaborate::Way::Unfolded,
                            &turned,
                            scope,
                            facts,
                            &lines,
                        )? {
                            let alike = self.same(
                                &self.to_term(&turned),
                                &self.to_term(&ex),
                                scope,
                                facts,
                                Some(step),
                            )?;
                            if let Built(alike) = alike {
                                found = Built(
                                    pf!(self.b; scope, turned, ex, p, alike, "mpbid"),
                                );
                            }
                        }
                    }
                }
                p_ex = match found {
                    Built(p) => p,
                    Declined(_) => {
                        return Err(self.defect(
                            step.line,
                            format!(
                                "nothing step {number} cites says {}",
                                self.render(&ex)
                            ),
                        ));
                    }
                };
            }
            Some(item_name) => {
                let item = self.item_cited(item_name)?;
                // Read under what the citation gives the item's letters. A
                // letter named in `apart` is read as a class nothing else
                // holds, and its value put in once the item's bound letters
                // are moved off it, as `cite_corpus` reads a theorem
                // (`apart_from_values`).
                let read = |me: &mut Self,
                            apart: &BTreeSet<String>|
                 -> Checked<Reading> {
                    me.names_kept(|me| -> Checked<Reading> {
                    // A record's sentence comes back with each of its letters
                    // already what it stands for (`item_sentence_here`), in
                    // the proof's names. A theorem's is read in its own
                    // letters, which the values name, read in the proof's
                    // names as they stand, before anything is obtained, as
                    // the checker read the citation (`corpus_matched`).
                    let values: Vec<(String, Rpn)> = match item {
                        Item::Theorem(theorem) => {
                            me.corpus_matched(step, theorem)?.into_iter().collect()
                        }
                        Item::Record(_) => Vec::new(),
                    };
                    // A name is a variable of the kernel whatever it is
                    // spelt with, and a spare stands for it as one does for
                    // a binder's name.
                    for name in &got {
                        let var = me.binder_var(name)?;
                        me.names.insert(name.clone(), t!(var, "cv"));
                    }
                    let held: BTreeSet<String> = me
                        .names
                        .values()
                        .chain(values.iter().map(|(_, t)| t))
                        .flat_map(|t| t.tokens().iter().map(|s| s.to_string()))
                        .collect();
                    let mut unheld = CLASS_NAMES
                        .iter()
                        .rev()
                        .filter(|c| !held.contains(**c));
                    // The item's letters are what the citation gives them,
                    // even where an obtained name is spelt as one of them:
                    // `obtain x, n: thm:lowest-terms x := √2` gives the
                    // item's x the value √2, and obtains another x.
                    let mut given: Vec<Given> = Vec::new();
                    for (name, term) in values {
                        let class = if apart.contains(&name) {
                            let Some(own) = unheld.next() else {
                                return Err(me.defect(
                                    step.line,
                                    "no class is left to read the cited theorem's letter apart from what the citation gives it",
                                ));
                            };
                            t!(*own)
                        } else {
                            term.clone()
                        };
                        me.names.insert(name.clone(), class.clone());
                        given.push(Given { name, class, term });
                    }
                    // A library item says its existential in its own names,
                    // and the step's lines say what those stand for. The
                    // sentence is the one the checker obtains from.
                    let cited = me.citation_read(step).cloned().ok_or_else(|| {
                        me.unreached(step.line, "the checker reads no citation here")
                    })?;
                    let said = me.obtained_from(item, &cited, step.line)?;
                    let node = match item {
                        Item::Record(r) => me.item_sentence_here(step, r, &said)?,
                        // Parsed with the theorem's own sorts, which say what
                        // its letters are, and made a term in the step's names.
                        Item::Theorem(_) => {
                            me.in_its_names(item, |me| me.read_one(&said))?
                        }
                    };
                    Ok(Reading {
                        wanted: Vec::new(),
                        whole: me.term(&node)?,
                        given,
                    })
                    })
                };
                let first = read(self, &BTreeSet::new())?;
                let (_, claimed) = self.apart_from_values(first, read)?;
                // An item states its existential in its own names, and a
                // binder takes the variable its name is spelled with, so the
                // one obtained is renamed to a variable nothing else holds.
                // An item saying "A ↔ there is …" gives one where a line the
                // step cites says A, as `mod-remainder` does from a mod m = r.
                let whole = self.to_term(&claimed);
                let sides = (whole.label() == Some("wb"))
                    .then(|| (whole.children()[0].clone(), whole.children()[1].clone()))
                    .filter(|(a, there)| {
                        there.label() == Some("wrex") && a.label() != Some("wrex")
                    });
                if let Some((given, there)) = sides {
                    let given = self.rpn(&given);
                    ex = self.renamed(&self.rpn(&there), got.len())?;
                    let iff = t!(given, ex, "wb");
                    let p_iff = match self.cite_item(step, &iff, scope, facts, item)? {
                        Built(p) => p,
                        Declined(d) => {
                            panic!(
                                "an item cited for an obtain declined: {}",
                                self.say(&d)
                            )
                        }
                    };
                    let supplied = self.supplied(Some(step), scope, facts)?;
                    let known = self.with_cited(Some(step), scope, &supplied, None)?;
                    let p_given = match self.settle(
                        &self.to_term(&given),
                        scope,
                        &known,
                        3,
                        None,
                        None,
                    )? {
                        Built(p) => p,
                        Declined(_) => {
                            return Err(self.defect(
                                step.line,
                                format!(
                                    "step {number} obtains from {}, and nothing it cites says {}",
                                    step.just.head,
                                    self.render(&given)
                                ),
                            ));
                        }
                    };
                    p_ex = pf!(self.b; scope, given, ex, p_given, p_iff, "mpbid");
                } else {
                    ex = self.renamed(&claimed, got.len())?;
                    p_ex = match self.cite_item(step, &ex, scope, facts, item)? {
                        Built(p) => p,
                        Declined(d) => {
                            panic!(
                                "an item cited for an obtain declined: {}",
                                self.say(&d)
                            )
                        }
                    };
                }
            }
        }
        // What the line is obtained from is what it rests on; what it
        // introduces is sealed below with the same name.
        let p_ex = self.check_step(p_ex, step, number, false)?;

        // The existential says which names it introduces and where they run,
        // so the scope is read off it rather than off the text.
        let mut layers: Vec<(String, Rpn)> = Vec::new();
        let mut rest = self.to_term(&ex);
        while layers.len() < got.len() {
            let kids = rest.children().to_vec();
            if rest.label() != Some("wrex") || kids.len() != 3 {
                return Err(self.unreached(
                    step.line,
                    format!(
                        "step {number} obtains {} from {}, which is no \"there is\" of as many",
                        got.join(", "),
                        self.render(&ex)
                    ),
                ));
            }
            layers.push((
                self.float_of(kids[1].variable().unwrap_or_default()),
                self.rpn(&kids[2]),
            ));
            rest = kids[0].clone();
        }
        let body = self.rpn(&rest);
        let memberships: Vec<Rpn> =
            layers.iter().map(|(v, s)| t!(v, "cv", s, "wcel")).collect();
        // The memberships joined from the left, ((x ∈ A ∧ y ∈ B) ∧ z ∈ C),
        // which the discharge takes apart from the right (`discharged`).
        let mut member = memberships[0].clone();
        for one in &memberships[1..] {
            member = t!(member, one, "wa");
        }
        for (name, (variable, over_term)) in got.iter().zip(layers.iter()) {
            self.names.insert(name.clone(), t!(variable, "cv"));
            self.sets.insert(name.clone(), over_term.clone());
        }
        // Read after the obtained names are bound, so a sentence naming one of
        // them is about the variable the existential introduced.
        let sentences = self.said(step)?;
        // The body is taken apart as deep as the sentences the claim wrote
        // for it, as any line saying several things is; the claim's other
        // sentences are the memberships.
        let deep = sentences.len().saturating_sub(got.len() + 1);
        // A point is a point as `let A be a point` says it is: a sort, which
        // a step rests on without citing the line and the checker does not
        // let it cite. So is a function among the functions from X to Y,
        // f : X → Y, as `let f : X → Y` says it: the checker asks a
        // function's type only of one the proof defines. A polynomial is a
        // function too, and "q is a polynomial" a fact, as `let p be a
        // polynomial` asserts one. A number obtained is cited for its
        // membership, as a requires line from the obtain.
        let points = got.iter().zip(layers.iter()).all(|(name, (_, over))| {
            let sort = self.sorts_now.get(name).and_then(|s| s.name());
            sort == Some("point")
                || (sort == Some("function")
                    && over.len() > 2
                    && over.ends_with(&["cmap", "co"]))
        });
        let members = if points {
            let sort = format!("{number}∈");
            self.sorts.insert(sort.clone());
            sort
        } else {
            number.to_string()
        };
        let (outer, held) = self.widen(scope, whole, &member, Some(&members));
        let (inner, lifted) = self.widen_to(&outer, &held, &body, Some(number), deep);
        self.note_introduced(&inner, &lifted)?;
        // A function obtained among the functions from X to Y has the type
        // f : X → Y, as `let f : X → Y` gives it: `elmapi`.
        for (variable, over_term) in &layers {
            let Some(FunctionSet { domain, codomain }) = self.function_set(over_term)
            else {
                continue;
            };
            let named = t!(variable, "cv");
            let member = t!(named, over_term, "wcel");
            let Some(is_member) = self.held(&lifted, &member, &inner)? else {
                continue;
            };
            let typed = t!(domain, codomain, named, "wf");
            let law = self.b.ap(
                "elmapi",
                &binds! {"A" => &named, "B" => &codomain, "C" => &domain},
                &[],
            );
            let made = pf!(self.b; &inner, member, typed, is_member, law, "syl");
            // A sort, as the type a `let` line gives is: a step rests on it
            // without citing the obtain.
            let sort = format!("{number}∈");
            self.sorts.insert(sort.clone());
            let sealed = self.seal(made, &sort);
            self.know(&lifted, typed, sealed);
        }
        // The claim's first sentences are the memberships of the names, each
        // the one the existence lays down by one standard form: `C ⊆ A` is
        // `C ∈ 𝒫A`. A function among the functions from X to Y is said by
        // its type, `f : X → Y`, as above.
        for (sentence, (variable, over)) in sentences.iter().zip(&layers) {
            let said = self.term(sentence)?;
            let named = t!(variable, "cv");
            let member = match self.function_set(over) {
                Some(FunctionSet { domain, codomain }) => {
                    t!(domain, codomain, named, "wf")
                }
                None => t!(named, over, "wcel"),
            };
            if said == member {
                continue;
            }
            // The item binds its own letters inside the set, `⋃(Y ∈ C) Y`,
            // and the page may bind another, `⋃(B ∈ F) B`: the two are one
            // claim (`renaming_apart`), and the line is known as written.
            if let Some(renamed) = self.renaming_apart(&member, &said)? {
                if let Some(held) = self.held(&lifted, &member, &inner)? {
                    let proof = self.b.ap(
                        "sylib",
                        &binds! {"ph" => &inner, "ps" => &member, "ch" => &said},
                        &[&held, &renamed],
                    );
                    self.know(&lifted, said, proof);
                    continue;
                }
            }
            let alike = self.same(
                &self.to_term(&member),
                &self.to_term(&said),
                &inner,
                &lifted,
                Some(step),
            )?;
            if alike.is_declined() {
                return Err(self.defect(
                    step.line,
                    format!(
                        "step {number} claims {}, and what it obtains says {}",
                        self.render(&said),
                        self.render(&member)
                    ),
                ));
            }
        }
        let proof = self
            .held(&lifted, &body, &inner)?
            .expect("the body just laid down");
        // What carrying the body to the line may rest on: what the step
        // names, and the body it obtains, which stands for the step.
        let mut allowed = self.named(step, number, false);
        allowed.insert(number.to_string());
        // The line is what the page writes: built from the body as the
        // checker paired its sentences with the body's parts
        // (`obtained_line`), where it did. An obtain whose "there is" the
        // checker leaves to the build, a part or a function said otherwise,
        // is read here whole. An item states its body in its own bound
        // letters, `for all x ∈ ℂ`, and the page may bind another,
        // `for all n ∈ ℂ`, which a later `instantiate n := …` names; the two
        // are one claim (`renaming`).
        let pairs = self.checked.obtained_parts.get(&step.just.line).cloned();
        let (line_term, line_proof) = match (sentences.get(got.len()..), pairs) {
            (Some([_, ..]), Some(pairs)) => self.obtained_line(
                step,
                &pairs,
                &sentences,
                got.len(),
                &body,
                &proof,
                &inner,
                &lifted,
                &allowed,
            )?,
            (Some([first, rest @ ..]), None) => {
                let mut said = self.term(first)?;
                for s in rest {
                    said = t!(said, self.term(s)?, "wa");
                }
                match self.renaming(&self.to_term(&body), &self.to_term(&said))? {
                    Some(same) => {
                        let proof = self.b.ap(
                            "sylib",
                            &binds! {"ph" => &inner, "ps" => &body, "ch" => &said},
                            &[&proof, &same],
                        );
                        (said, proof)
                    }
                    None if said == body => (body.clone(), proof),
                    // Written another way, `1 < d` for `d > 1`, the claim is
                    // the body by one standard form, or by one once the
                    // identity elements of both are dropped (`reached`);
                    // anything else is a claim the existence does not give.
                    None => {
                        let (from, to) = (self.to_term(&body), self.to_term(&said));
                        let alike = self.resting_on(Some(allowed.clone()), |me| {
                            let offered = me.in_hand(&lifted);
                            me.same(&from, &to, &inner, &offered, Some(step))
                        })?;
                        let proof = match alike {
                            Built(alike) => {
                                pf!(self.b; &inner, body, said, proof, alike, "mpbid")
                            }
                            Declined(_) => {
                                let reached =
                                    self.resting_on(Some(allowed.clone()), |me| {
                                        let offered = me.in_hand(&lifted);
                                        me.reached(
                                            &proof, &body, &said, &inner, &offered,
                                        )
                                    })?;
                                match reached {
                                    Some(p) => p,
                                    None => {
                                        return Err(self.defect(
                                            step.line,
                                            format!(
                                                "step {number} claims {}, and what it obtains says {}",
                                                self.render(&said),
                                                self.render(&body)
                                            ),
                                        ))
                                    }
                                }
                            }
                        };
                        (said, proof)
                    }
                }
            }
            _ => (body.clone(), proof),
        };
        // The line rests on nothing the step does not name but the body it
        // obtains, and stands for the step from here on, as a step's proof
        // does (`check_step`): what carried the body to the claim, an
        // identity element dropped from a number its `let` says, is the
        // obtain's, not a citer's.
        self.rests_on_named(
            &line_proof,
            &allowed,
            step.line,
            &format!("step {number}"),
        )?;
        let line_proof = self.seal(line_proof, number);
        if line_term != body {
            // Known at this scope, so a deeper one carries it as it carries
            // the body.
            self.know(&lifted, line_term.clone(), line_proof.clone());
        }
        self.lines
            .set(number, Line::new(line_term, line_proof, sentences));
        let discharge = if layers.len() == 1 {
            "rexlimdva"
        } else {
            "rexlimdvva"
        };
        let mut pushed: Vec<Rpn> = layers.iter().map(|(v, _)| t!(v)).collect();
        pushed.extend(layers.iter().map(|(_, s)| s.clone()));
        let mut closers = closers;
        closers.push(Closer::Obtain(Rc::new(ObtainCloser {
            line: step.line,
            scope: scope.clone(),
            ex,
            p_ex,
            body,
            outer,
            inner: inner.clone(),
            pushed,
            layers,
            discharge,
        })));
        Ok((inner, lifted, closers))
    }

    /// What a scope's closer makes of a proof and its goal where the scope
    /// ends.
    pub fn close(
        &mut self,
        closer: &Closer,
        proof: Proof,
        goal: &Rpn,
    ) -> Checked<Proof> {
        match closer {
            Closer::Obtain(c) => self.close_obtain(c, proof, goal),
            Closer::Define(c) => {
                // The claim discharged here was read before the define was,
                // so it cannot name the variable; `exlimdv` forbids it.
                if goal.has(&c.var) {
                    return Err(self.unreached(
                        c.line,
                        format!(
                            "what {} names is still named where its scope ends",
                            c.label
                        ),
                    ));
                }
                let inner = pf!(self.b; c.scope, c.said, goal, proof, "ex");
                let dropped =
                    pf!(self.b; c.scope, c.said, goal, c.var, inner, "exlimdv");
                Ok(pf!(self.b; c.scope, c.ex, goal, c.p_ex, dropped, "mpd"))
            }
        }
    }

    pub(super) fn discharged(
        &self,
        c: &ObtainCloser,
        proof: &Proof,
        goal: &Rpn,
    ) -> Proof {
        let inner = pf!(self.b; c.outer, c.body, goal, proof, "ex");
        if c.layers.len() > 2 {
            return self.discharged_each(c, inner, goal);
        }
        let mut all: Vec<crate::mm::spell::Part> =
            vec![elab::part(&c.scope), elab::part(&c.body), elab::part(goal)];
        all.extend(c.pushed.iter().map(|p| elab::part(p)));
        all.push(elab::part(&inner));
        all.push(elab::part(c.discharge));
        let eliminated = self.b.proof(&all);
        pf!(self.b; c.scope, c.ex, goal, c.p_ex, eliminated, "mpd")
    }

    /// Three names or more, which set.mm discharges with no one lemma: the
    /// last name at a time, from ( ( scope ∧ ( M ∧ z ∈ C ) ) → ( body → goal ) ),
    /// regrouped by `anassrs` and discharged by `rexlimdva`, until two are
    /// left for `rexlimdvva`.
    pub(super) fn discharged_each(
        &self,
        c: &ObtainCloser,
        inner: Proof,
        goal: &Rpn,
    ) -> Proof {
        let member = |(v, set): &(String, Rpn)| t!(v, "cv", set, "wcel");
        let joined = |upto: usize| {
            let mut out = member(&c.layers[0]);
            for layer in &c.layers[1..upto] {
                out = t!(out, member(layer), "wa");
            }
            out
        };
        let mut proof = inner;
        let mut body = c.body.clone();
        let mut k = c.layers.len();
        while k > 2 {
            let (var, set) = c.layers[k - 1].clone();
            let before = joined(k - 1);
            let last = member(&c.layers[k - 1]);
            let then = t!(body, goal, "wi");
            let regrouped = self.b.ap(
                "anassrs",
                &binds! {"ph" => &c.scope, "ps" => &before, "ch" => &last, "th" => &then},
                &[&proof],
            );
            let held = t!(c.scope, before, "wa");
            proof = self.b.ap(
                "rexlimdva",
                &binds! {"ph" => &held, "ps" => &body, "ch" => goal, "x" => &var, "A" => &set},
                &[&regrouped],
            );
            body = t!(body, var, set, "wrex");
            k -= 1;
        }
        let ((x, a), (y, b)) = (c.layers[0].clone(), c.layers[1].clone());
        let eliminated = self.b.ap(
            "rexlimdvva",
            &binds! {"ph" => &c.scope, "ps" => &body, "ch" => goal,
            "x" => &x, "A" => &a, "y" => &y, "B" => &b},
            &[&proof],
        );
        pf!(self.b; c.scope, c.ex, goal, c.p_ex, eliminated, "mpd")
    }

    /// The goal may bind the letter an obtained name stands for, and the
    /// discharge keeps the name out of the goal, so the goal is renamed apart
    /// for it and back.
    pub(super) fn close_obtain(
        &mut self,
        c: &ObtainCloser,
        proof: Proof,
        goal: &Rpn,
    ) -> Checked<Proof> {
        let caught: Vec<&String> = c
            .layers
            .iter()
            .map(|(v, _)| v)
            .filter(|v| goal.has(v))
            .collect();
        if caught.is_empty() {
            return Ok(self.discharged(c, &proof, goal));
        }
        let whole = self.to_term(goal);
        let mut moved = Binding::new();
        for v in caught {
            let mut terms: Vec<&Term> = vec![&whole];
            terms.extend(moved.values());
            let Some(letter) = self.unheld(&terms) else {
                return Err(
                    self.defect(c.line, "no letter left to rename the goal apart with")
                );
            };
            let var = self.sig(v).statement[1];
            moved.insert(var, letter);
        }
        let apart = whole.substitute(&moved);
        let Some(back) = self.renaming(&apart, &whole)? else {
            return Err(self.defect(
                c.line,
                "the goal renamed apart does not read back as the goal",
            ));
        };
        let there = self.rpn(&apart);
        let turned = self.b.ap(
            "sylibr",
            &binds! {"ph" => &c.inner, "ps" => goal, "ch" => &there},
            &[&proof, &back],
        );
        let made = self.discharged(c, &turned, &there);
        Ok(self.b.ap(
            "sylib",
            &binds! {"ph" => &c.scope, "ps" => &there, "ch" => goal},
            &[&made, &back],
        ))
    }

    /// Each `define` above line `before` as a name and its equation.
    ///
    /// A textbook's "let x₁ = min(b, c + δ/2)" introduces a number and says
    /// what it is, and the steps after it are about x₁. So a define is taken
    /// the way an `obtain` is: from `∃x x = E`, which `elisset` gives once E
    /// is a set, the scope is widened by `x = E` and the existential is
    /// discharged where the scope ends (`exlimdv`).
    ///
    /// The defines are read one at a time where they stand, each with the
    /// names the ones before it gave: what the theorem sees from outside it
    /// first, then its own, stopping at the first below `before`.
    pub fn define(
        &mut self,
        before: usize,
        scope: &Rpn,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        let mut scope = scope.clone();
        let mut facts = facts.clone();
        let mut closers = closers;
        // What the theorem sees from outside it comes first, before its own
        // first step: written out where it was defined, and from here on a
        // name like any the theorem defines itself.
        if !self.file_given {
            self.file_given = true;
            let written = self.checked.outside.clone();
            for v in self.visible_outside() {
                let Some(made) = written.get(&v.name) else {
                    continue;
                };
                let label = self.outside_label(&v.name, &v.define, v.scope);
                let line = if v.scope == self.thm.scope {
                    v.define.line
                } else {
                    self.thm.line
                };
                let body = self.outside_term(made)?;
                (scope, facts, closers) = self.one_define(
                    &label, line, &v.name, &body, &scope, &facts, closers,
                )?;
            }
        }
        while self.unread < self.thm.defines.len() {
            let d = self.thm.defines[self.unread].clone();
            if d.line >= before {
                break;
            }
            self.unread += 1;
            let said = match define_parts(&d.text) {
                Built(said) => said,
                Declined(why) => {
                    return Err(self.unreached(
                        d.line,
                        format!("define {}: {}", d.label, why.reason()),
                    ));
                }
            };
            for name in said.names() {
                if self.names.contains_key(&name) {
                    return Err(
                        self.unreached(d.line, format!("{name} is already named"))
                    );
                }
            }
            match &said {
                // Sequences by recursion are one define giving several names,
                // each the map to its part of the one recursion.
                DefineParts::Recursion(r) => {
                    let maps = self.recursion_terms(&d.label, d.line, r)?;
                    for (name, made) in maps {
                        (scope, facts, closers) = self.one_define(
                            &d.label, d.line, &name, &made, &scope, &facts, closers,
                        )?;
                    }
                }
                DefineParts::One(one) => {
                    // A function is the map sending its parameters, each in
                    // its domain, to its rule, as the checker read them: the
                    // rule and the names with what the domains say the
                    // parameters are (`define_sorts`).
                    let rule = self.read_one(&d.rule(&one.body))?;
                    let mut held = Vec::new();
                    for p in &one.params {
                        held.push(self.read_one(&d.formula(&p.name))?);
                        held.push(self.read_one(&d.domain(p))?);
                    }
                    let pattern = match one.params.len() {
                        0 => None,
                        1 => Some("the map sending _ ∈ _ to _"),
                        2 => Some("the map sending _ ∈ _, _ ∈ _ to _"),
                        _ => {
                            return Err(self.unreached(
                                d.line,
                                format!(
                                    "define {} takes more arguments than two",
                                    d.label
                                ),
                            ))
                        }
                    };
                    let node = match pattern {
                        None => rule,
                        Some(pattern) => {
                            held.push(rule);
                            made_as(self.g, pattern, held).expect("the map notations")
                        }
                    };
                    let term = self.term(&node)?;
                    // A define names a thing, a number, a set or a map, and a
                    // statement is none: there is nothing for the name to be
                    // equal to.
                    if self.is_wff(&self.to_term(&term)) {
                        return Err(self.unreached(
                            d.line,
                            format!(
                                "define {}: {} is a statement, and a define names a thing",
                                d.label,
                                one.body.text()
                            ),
                        ));
                    }
                    let made = self.apart(&term)?;
                    (scope, facts, closers) = self.one_define(
                        &d.label, d.line, &one.name, &made, &scope, &facts, closers,
                    )?;
                    if let Some(kinded) = d.kinded(&self.thm.path, &self.g.members)? {
                        self.kind_shown(&kinded, &made, &scope, &facts)?;
                    }
                }
                // A phrase gives no name for a proof to hold: it is its
                // meaning wherever it is written (`Elaborator::term`).
                DefineParts::Phrase(_) => {}
            }
        }
        Ok((scope, facts, closers))
    }

    /// What a let saying a kind of number says of its name, `m ∈ ℕ`: the
    /// term it names is in the set by its reason, read as a requires line of
    /// the step below the let (`as_a_step`), and the name is equal to the
    /// term. The name is then in the set as a letter `let m ∈ ℕ` puts there
    /// is: a step has the membership without citing the let
    /// (`introduced_membership`), and a step citing the let has it as a line
    /// the let says.
    pub(super) fn kind_shown(
        &mut self,
        kinded: &Kinded,
        body: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        let line = kinded.shown.line;
        // The step's own requires lines are below the let and nothing the
        // reason rests on; the let's own are what it rests on, read as the
        // step's (`Reason::under`).
        let requires = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == kinded.label)
            .and_then(|d| d.reason.as_ref())
            .map(|r| r.requires.clone())
            .unwrap_or_default();
        let Some(after) = self.thm.step_after(line).map(|s| Step {
            requires,
            reason_of: Some(kinded.label.clone()),
            ..s.clone()
        }) else {
            return Err(self.unreached(
                line,
                format!(
                    "let {} stands below every step, where no step uses it",
                    kinded.label
                ),
            ));
        };
        // Only a let with requires lines has anything to add to the facts.
        let supplied = if after.requires.is_empty() {
            facts.clone()
        } else {
            self.supplied(Some(&after), scope, facts)?
        };
        let facts = &supplied;
        let node = self.read_one(&kinded.shown.fact)?;
        let shown = self.term(&node)?;
        let set = self.rpn(&self.to_term(&shown).children()[1]);
        let what = format!("the reason under let {}", kinded.label);
        // A reason that is the lines it cites, `from 5`, is proved as a
        // requires line with that reason is; any other is the step it
        // would be.
        let shown_by = if kinded.shown.is_lines() {
            self.side(&node, &kinded.shown, scope, facts, Some(&after))?
        } else {
            self.as_a_step(&after, &kinded.shown, &what, scope, facts)?
        };
        let in_set = match shown_by {
            Built(proof) => proof,
            Declined(why) => {
                return Err(self.defect(
                    line,
                    format!(
                        "the reason under let {} does not show {}: {}",
                        kinded.label,
                        kinded.shown.fact,
                        self.say(&why)
                    ),
                ));
            }
        };
        // The let's term is read with the letters it binds kept apart from
        // the proof's (`apart`), and its reason's fact as the page writes
        // it; where the two differ in a bound letter, the one is carried to
        // the other.
        let want = t!(body, set, "wcel");
        let in_set = if want == shown {
            in_set
        } else {
            let (given, wanted) = (self.to_term(&shown), self.to_term(&want));
            let Built(alike) =
                self.same(&given, &wanted, scope, facts, Some(&after))?
            else {
                return Err(self.defect(
                    line,
                    format!(
                        "the reason under let {} shows {}, which is not carried to what the let names",
                        kinded.label, kinded.shown.fact
                    ),
                ));
            };
            pf!(self.b; scope, shown, want, in_set, alike, "mpbid")
        };
        let name = self.names[&kinded.name].clone();
        let equation = t!(name, body, "wceq");
        let equal = self
            .held(facts, &equation, scope)?
            .expect("the equation the let laid down");
        let membership = t!(name, set, "wcel");
        let proof = self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => &name, "B" => body, "C" => &set},
            &[&equal, &in_set],
        );
        let proof = self.seal(proof, &kinded.label);
        self.know(facts, membership.clone(), proof.clone());
        // The let's line says both, as a hypothesis line of two sentences
        // does, so a step citing it reads the membership as it reads the
        // equation, written out where it writes the name out.
        let line = self
            .lines
            .get(&kinded.label)
            .expect("the line the let laid down");
        let said = self
            .line_written(&kinded.label, &self.lines)
            .expect("the line the let laid down");
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &said.claim, "ch" => &membership},
            &[&said.proof, &proof],
        );
        let term = t!(said.claim, membership, "wa");
        // Held as a fact too, so it is carried into each scope opened below.
        self.know(facts, term.clone(), both.clone());
        self.lines
            .set(kinded.label.clone(), line.restated(term, both));
        self.sets.insert(kinded.name.clone(), set);
        self.note_introduced(scope, facts)
    }

    /// One define taken: its name a spare variable, its equation laid down,
    /// and its existential left to discharge where the scope ends.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn one_define(
        &mut self,
        label: &str,
        line: usize,
        name: &str,
        body: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        closers: Vec<Closer>,
    ) -> Checked<(Rpn, Facts, Vec<Closer>)> {
        self.at = line;
        // A define stands where the first step after it does
        // (`CheckedTheorem::defines`), and its reason reads what is in scope
        // there.
        self.step_now = self.thm.steps.iter().position(|s| s.line > line);
        self.note_said_sums()?;
        let body = body.clone();
        let var = self.spare_var()?;
        let said = t!(var, "cv", body, "wceq");
        let ex = t!(said, var, "wex");
        let p_ex = match self.apply_lemma(
            "elisset",
            &self.to_term(&ex),
            scope,
            facts,
            None,
            false,
            None,
        )? {
            Built(p) => p,
            Declined(d) => {
                return Err(self.defect(
                    line,
                    format!(
                        "cannot show that what {label} names is a set: {}",
                        self.say(&d)
                    ),
                ));
            }
        };
        // That the body is a set is the define's own and rests on the
        // define.
        let p_ex = self.seal(p_ex, label);
        let (outer, held) = self.widen(scope, facts, &said, Some(label));
        self.names.insert(name.to_string(), t!(var, "cv"));
        self.definitions.insert(var.clone(), body);
        self.defined_by.insert(var.clone(), label.to_string());
        // What a term comes to in standard form now reads this name as its
        // body, and a form worked out before could hold the name as it stood.
        self.standards.clear();
        let proof = self
            .held(&held, &said, &outer)?
            .expect("the equation just laid down");
        self.lines
            .set(label, Line::new(said.clone(), proof, Vec::new()));
        let mut closers = closers;
        closers.push(Closer::Define(Rc::new(DefineCloser {
            scope: scope.clone(),
            said,
            var,
            ex,
            p_ex,
            line,
            label: label.to_string(),
        })));
        Ok((outer, held, closers))
    }

    /// Whether two statements differ only in the letters they bind: a set
    /// variable is bound where it stands directly under a constructor other
    /// than `cv`, within that constructor, and every other letter must be the
    /// same on both sides. A bound letter may be one the statement also uses
    /// free, as the page's `x ∈ {x ∈ A : x ∉ f(x)}` does, and is paired with
    /// its partner only inside what binds it. A class variable stands
    /// directly under a constructor as an operand, as P does in P − Q, and
    /// is bound by nothing: read as bound, it would make |PQ| and |RS| one
    /// term renamed (`letters_bound` draws the same line).
    pub fn rebound(&self, stated: &Rpn, claimed: &Rpn) -> bool {
        let setvar = |v: &str| self.is_setvar(&self.float_of(v));
        let mut bound: Vec<BoundPair> = Vec::new();
        alike_rebound(
            &self.to_term(stated),
            &self.to_term(claimed),
            &mut bound,
            &setvar,
        )
    }

    /// The "there is" an obtain's claim states: the claim states each name's
    /// membership as a sentence of its own, which is where the name runs;
    /// the other sentences are what is said of it, in the order written.
    pub(super) fn existence_claimed(
        &mut self,
        step: &Step,
        got: &[String],
    ) -> Checked<Rpn> {
        let mut domains: IndexMap<String, Node> = IndexMap::new();
        let mut rest: Vec<Node> = Vec::new();
        for sentence in step.claim.sentences() {
            let said = self.read(&sentence)?;
            let named = |n: &Node| {
                n.is_name()
                    && got.iter().any(|g| *g == n.text)
                    && !domains.contains_key(n.text.as_str())
            };
            match (said.notation(), said.spelling(), said.children.as_slice()) {
                // A function's membership is its type, `f : X → Y`, which
                // says it is among the functions from X to Y, where "there
                // is f : X → Y" runs.
                (FUNCTION_TYPE, _, [f, from, to]) if named(f) => {
                    let functions = self.functions_from(from, to)?;
                    domains.insert(f.text.to_string(), functions);
                }
                (_, IN, [x, set]) if named(x) => {
                    domains.insert(x.text.to_string(), set.clone());
                }
                _ => rest.push(said),
            }
        }
        let missing: Vec<&str> = got
            .iter()
            .filter(|n| !domains.contains_key(*n))
            .map(String::as_str)
            .collect();
        if !missing.is_empty() {
            return Err(self.unreached(
                step.line,
                format!(
                    "step {} states no membership of {}",
                    step.number,
                    missing.join(", ")
                ),
            ));
        }
        if rest.is_empty() {
            return Err(self.unreached(
                step.line,
                format!("step {} states nothing of what it obtains", step.number),
            ));
        }
        self.names_kept(|me| -> Checked<Rpn> {
            for name in got {
                let var = me.binder_var(name)?;
                me.names.insert(name.clone(), t!(var, "cv"));
            }
            // What is said of them is one claim of several sentences, their
            // conjunction in the order written (`claim_of`).
            let mut said = Vec::new();
            for node in &rest {
                said.push(me.term(node)?);
            }
            let mut body = said[0].clone();
            for extra in &said[1..] {
                body = t!(body, extra, "wa");
            }
            for name in got.iter().rev() {
                let var = me.binder_var(name)?;
                let over = me.term(&domains[name])?;
                body = t!(body, var, over, "wrex");
            }
            Ok(body)
        })
    }

    /// An existential rewritten to bind variables nothing else holds, the
    /// existential included: a letter its body already binds, as a cited
    /// theorem's letter moved apart from a value is, is passed over.
    pub fn renamed(&mut self, ex: &Rpn, depth: usize) -> Checked<Rpn> {
        let whole = self.to_term(ex);
        let spelt: BTreeSet<String> =
            ex.tokens().iter().map(|t| t.to_string()).collect();
        let mut term = whole.clone();
        let mut binding = Binding::new();
        for _ in 0..depth {
            if term.label() != Some("wrex") {
                break;
            }
            let Some(var) = term.children()[1].variable().map(Symbol::of) else {
                break;
            };
            let mut fresh = self.spare_var()?;
            while spelt.contains(&fresh) {
                fresh = self.spare_var()?;
            }
            binding.insert(var, self.var_of(&fresh));
            term = term.children()[0].clone();
        }
        Ok(self.rpn(&whole.substitute(&binding)))
    }

    /// The variables an existential's own binders introduce, outermost first.
    pub fn bound_in(&self, term: &Term) -> Vec<Symbol> {
        let mut out = Vec::new();
        let mut rest = term.clone();
        while matches!(rest.label(), Some("wrex") | Some("wreu")) {
            let Some(var) = rest.children()[1].variable() else {
                break;
            };
            out.push(Symbol::of(var));
            rest = rest.children()[0].clone();
        }
        out
    }

    /// The innermost scope a lemma's disjointness conditions permit.
    ///
    /// `fsump1` forbids its summation variable in the antecedent, and the
    /// induction hypothesis is an equation between sums, so it holds that
    /// variable. The step is proved one frame out and carried back in.
    pub fn allowed(
        &self,
        sig: &Signature,
        binding: &Binding,
    ) -> (Route<Rpn>, Option<usize>) {
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        let mut forbidden: BTreeSet<String> = BTreeSet::new();
        for (a, b) in &sig.disjoint {
            for (one, other) in [(a, b), (b, a)] {
                if kinds.get(other.as_str()) == Some(&"setvar") {
                    continue;
                }
                if let (Some(held), false) =
                    (binding.get(one), binding.contains_key(other))
                {
                    for n in held.names().iter() {
                        forbidden.insert(self.float_of(n));
                    }
                }
            }
        }
        for index in (0..self.frames.len()).rev() {
            let term = &self.frames[index].scope;
            if !term.tokens().iter().any(|t| forbidden.contains(t.as_str())) {
                return (Built(term.clone()), Some(index));
            }
        }
        (Route::no("no scope satisfies the lemma"), None)
    }

    /// What the proof being built may use at one frame: `facts` at the
    /// innermost, and at an outer one what was known when the next frame
    /// opened, narrowed as `facts` is (`in_hand`).
    pub fn frames_facts(&self, frame: usize, facts: &Facts) -> Facts {
        if frame == self.frames.len() - 1 {
            facts.clone()
        } else {
            self.in_hand(&self.frames[frame].facts)
        }
    }

    /// Bring a proof from an outer frame back to the innermost one.
    pub fn carry(&self, proof: Proof, claim: &Rpn, frame: usize) -> Proof {
        let mut proof = proof;
        for index in frame..self.frames.len().saturating_sub(1) {
            let outer = &self.frames[index].scope;
            let added = self.frames[index + 1].added.clone().unwrap_or_default();
            proof = pf!(self.b; outer, claim, added, proof, "adantr");
        }
        proof
    }

    /// Two lines paired, `jca`, the lines paired by what they claim.
    pub fn join(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let lines = self.lines.clone();
        let wanted = self.claim_of(&step.claim)?;
        let held = Facts::new();
        // A line joined supplies each of its sentences, and each group of
        // them it nests together, so that the claim may group them otherwise.
        for r in &step.just.refs {
            let line = self.line_written(r, &lines).expect("a line joined");
            let proof = self.carried(r, facts, &lines);
            self.know_conjuncts(&held, &line.claim, &proof, scope);
            self.know(&held, line.claim, proof);
        }
        // The checker recorded where each part of the claim stands
        // (`CheckedTheorem::joined`, by sentence and part, of a join or a
        // restate of several sentences; `restated`, the claim of a restate
        // of one, whole). Each is that line's statement there, carried by
        // `same` where the line spells it otherwise, a define's name read as
        // what it names, and the parts are put together as the claim nests
        // them.
        let restated = self
            .checked
            .restated
            .get(&step.just.line)
            .filter(|_| step.just.head.is(Method::Restate))
            .and_then(|r| r.at())
            .map(|at| vec![at.clone()]);
        let parts_placed = self
            .checked
            .joined
            .get(&step.just.line)
            .map(|sentences| sentences.iter().flatten().cloned().collect());
        let restate = restated.is_some();
        let Some(parts) = restated.or(parts_placed) else {
            return Err(self.defect(
                step.line,
                "the checker recorded no place for the claim among the lines joined",
            ));
        };
        {
            let wholes = self
                .checked
                .joined_wholes
                .get(&step.just.line)
                .cloned()
                .unwrap_or_default();
            let count = parts.len();
            let written = self
                .checked
                .joined_claim
                .get(&step.just.line)
                .cloned()
                .unwrap_or_default();
            let mut claim = Vec::new();
            for part in &written {
                claim.push(self.term(part)?);
            }
            let mut places = JoinPlaces {
                parts,
                wholes,
                next: 0,
                held: held.clone(),
                claim,
            };
            let built =
                self.joined_by_places(&wanted, &mut places, restate, scope, facts)?;
            match (built, places.next == count) {
                (Some(p), true) => Ok(Some(p)),
                _ => Err(self.defect(
                    step.line,
                    "the lines the checker placed the claim's parts in do not make it",
                )),
            }
        }
    }

    /// ( scope -> term ) from the places the checker recorded, taken in
    /// order: the whole of `term` from the first where `whole`, a `restate`;
    /// otherwise a run of the claim's parts one line states whole
    /// (`JoinedWhole`) from that line, and each other conjunct, as the
    /// claim nests them, from its own place, paired by `jca`. None where a
    /// place does not say its part.
    fn joined_by_places(
        &mut self,
        term: &Rpn,
        places: &mut JoinPlaces,
        whole: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let node = self.to_term(term);
        if !whole {
            let count = self.parts_spanned(term, &places.claim, places.next);
            let run = places
                .wholes
                .iter()
                .find(|w| Some(w.count) == count && w.first == places.next)
                .map(|w| w.at.clone());
            if let (Some(at), Some(count)) = (run, count) {
                places.next += count;
                let held = places.held.clone();
                return self.placed_proof(&at, term, &held, scope, facts);
            }
            // A part of the claim as the record has it is one part, though
            // its meaning be an "and", `a is odd`; an "and" of several parts
            // is taken apart.
            let one_part = places.claim.get(places.next) == Some(term);
            if !one_part && node.label() == Some("wa") {
                let pair: Vec<Rpn> =
                    node.children().iter().map(|c| self.rpn(c)).collect();
                let first =
                    self.joined_by_places(&pair[0], places, false, scope, facts)?;
                let second =
                    self.joined_by_places(&pair[1], places, false, scope, facts)?;
                let (Some(first), Some(second)) = (first, second) else {
                    return Ok(None);
                };
                return Ok(Some(
                    pf!(self.b; scope, pair[0], pair[1], first, second, "jca"),
                ));
            }
        }
        let Some(at) = places.parts.get(places.next).cloned() else {
            return Ok(None);
        };
        places.next += 1;
        let held = places.held.clone();
        self.placed_proof(&at, term, &held, scope, facts)
    }

    /// How many of the claim's parts as the record has them (`claim`) `term`
    /// holds, from part `first` on: one where it is that part, the sum of
    /// its two sides where it is an "and" of them; None where it is neither.
    fn parts_spanned(&self, term: &Rpn, claim: &[Rpn], first: usize) -> Option<usize> {
        if claim.get(first) == Some(term) {
            return Some(1);
        }
        let node = self.to_term(term);
        if node.label() != Some("wa") {
            return None;
        }
        let left = self.rpn(&node.children()[0]);
        let right = self.rpn(&node.children()[1]);
        let one = self.parts_spanned(&left, claim, first)?;
        let other = self.parts_spanned(&right, claim, first + one)?;
        Some(one + other)
    }
}

/// The places the checker recorded for a `join` or `restate` step's claim,
/// and how many of its parts are taken so far (`joined_by_places`).
struct JoinPlaces {
    /// Where each part stands, in the order the claim writes them.
    parts: Vec<FirstAt>,
    /// The runs of parts one line states whole.
    wholes: Vec<JoinedWhole>,
    /// The next part to take.
    next: usize,
    /// What the lines joined hold: each line's claim and its conjuncts.
    held: Facts,
    /// Each part of the claim as the record has it, in set.mm
    /// (`CheckedTheorem::joined_claim`); empty for a `restate`.
    claim: Vec<Rpn>,
}
