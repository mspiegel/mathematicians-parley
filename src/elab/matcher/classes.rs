//! Classes, renaming within and witnesses.

use std::iter;

use super::*;
use crate::checker::record::{Supplied, SuppliedBy, Unfolded};
use crate::citing;
use crate::matching::{Binding as NodeBinding, FxIndexSet};
use crate::notations::PROPERTY_OF;

/// What the checker recorded as showing a "there is" (`Exhibit::shown`,
/// `Cited::unfolded`): each letter's membership in its domain, from the
/// outermost in, then each part of the body, and the values the facts are
/// said at where they are written in the claim's letters.
pub(in crate::elab) struct WitnessFacts {
    pub(in crate::elab) facts: Vec<Supplied>,
    pub(in crate::elab) values: NodeBinding,
    /// Whether set.mm writes the body's equation the other way round from
    /// the page, as a definition's lemma may (`metamath-reads turned`).
    pub(in crate::elab) turned: bool,
}

/// A fact of a definition's right side as `Cited::unfolded` records it, as
/// a hypothesis's supplier is recorded: no item's hypothesis, and met as
/// it stands.
fn unfolded_supplied(fact: &Node, by: &SuppliedBy) -> Supplied {
    Supplied {
        want: fact.clone(),
        by: by.clone(),
        at: None,
        meeting: None,
        narrowed: None,
    }
}

impl<'a> Elaborator<'a> {
    /// The closed `lemma` applied so that it states `one` against `other`,
    /// its variables read off matching the two; else None.
    pub(super) fn by_lemma(
        &self,
        lemma: &str,
        one: &Term,
        other: &Term,
        given: &[&Proof],
    ) -> Option<Proof> {
        let says = self.statement(lemma);
        let variables = names_of(&says);
        let binding = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], other, &b, &variables))?;
        Some(self.b.ap(lemma, &self.spelt(&binding), given))
    }

    /// A closed proof of `one = other`, two classes that differ only in the
    /// letters they bind; None where they differ in more, or not at all.
    pub fn class_alpha(&mut self, one: &Term, other: &Term) -> Checked<Option<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        if a == b
            || one.variable().is_some()
            || other.variable().is_some()
            || one.label() != other.label()
            || one.children().len() != other.children().len()
        {
            return Ok(None);
        }
        let Some(label) = one.label().map(str::to_string) else {
            return Ok(None);
        };
        if lookup(rules::CLASS_BOUND, &label).is_some() {
            // The renaming lemmas hold their two letters apart, so they are
            // asked only where the letters differ.
            let letters = label != "cmpt"
                || self.rpn(&one.children()[0]) != self.rpn(&other.children()[0]);
            if letters && (label == "cmpt" || label == "crab") {
                if let Some(p) = self.renamed_over_a_domain_apart(one, other)? {
                    return Ok(Some(p));
                }
            }
            let renamed = if letters {
                self.class_renamed(one, other)?
            } else {
                None
            };
            if !letters {
                // One letter over both: the domain and the rule are carried
                // each by itself, and `mpteq12i` asks nothing of the letter.
                let mut parts = Vec::new();
                for (x, y) in one.children()[1..].iter().zip(&other.children()[1..]) {
                    if self.rpn(x) == self.rpn(y) {
                        let x = self.rpn(x);
                        parts.push(Some(self.b.ap("eqid", &binds! {"A" => &x}, &[])));
                    } else {
                        parts.push(self.class_alpha(x, y)?);
                    }
                }
                if parts.iter().any(Option::is_none) {
                    return Ok(None);
                }
                let parts: Vec<Proof> = parts.into_iter().flatten().collect();
                let k: Vec<Rpn> = one.children().iter().map(|c| self.rpn(c)).collect();
                let o: Vec<Rpn> =
                    other.children().iter().map(|c| self.rpn(c)).collect();
                return Ok(Some(self.b.ap(
                    "mpteq12i",
                    &binds! {"x" => &k[0], "A" => &k[1], "B" => &k[2], "C" => &o[1], "D" => &o[2]},
                    &[&parts[0], &parts[1]],
                )));
            }
            if renamed.is_some() || lookup(rules::DOMAIN, &label).is_none() {
                return Ok(renamed);
            }
            // The domain may differ too, in the letters it binds: the domain
            // is made the other's first, and the letter renamed over the
            // domain the two then share. A map holds its domain after its
            // letter, and a set-builder after its condition and its letter.
            let at = if label == "crab" { 2 } else { 1 };
            let (x, y) = (&one.children()[at], &other.children()[at]);
            let Some(inner) = self.class_alpha(x, y)? else {
                return Ok(None);
            };
            let mut kids = one.children().to_vec();
            kids[at] = y.clone();
            let there = Term::apply(&label, kids);
            let lemma = lookup(rules::DOMAIN, &label).unwrap();
            let Some(moved) = self.by_lemma(lemma, one, &there, &[&inner]) else {
                return Ok(None);
            };
            let there_rpn = self.rpn(&there);
            if there_rpn == b {
                return Ok(Some(moved));
            }
            let rest = if letters {
                self.class_renamed(&there, other)?
            } else {
                None
            };
            let Some(rest) = rest else {
                return Ok(None);
            };
            return Ok(Some(self.b.ap(
                "eqtri",
                &binds! {"A" => &a, "B" => &there_rpn, "C" => &b},
                &[&moved, &rest],
            )));
        }
        let mut here = one.clone();
        let mut proof: Option<Proof> = None;
        for (i, (x, y)) in one.children().iter().zip(other.children()).enumerate() {
            if self.rpn(x) == self.rpn(y) {
                continue;
            }
            let lemma = class_lift(&label, i);
            let inner = self.class_alpha(x, y)?;
            let (Some(lemma), Some(inner)) = (lemma, inner) else {
                return Ok(None);
            };
            let mut kids = here.children().to_vec();
            kids[i] = y.clone();
            let there = here.with_children(kids);
            let Some(step) = self.by_lemma(lemma, &here, &there, &[&inner]) else {
                return Ok(None);
            };
            proof = Some(match proof {
                None => step,
                Some(p) => self.b.ap(
                    "eqtri",
                    &binds! {"A" => &a, "B" => self.rpn(&here), "C" => self.rpn(&there)},
                    &[&p, &step],
                ),
            });
            here = there;
        }
        Ok(proof)
    }

    /// `class_renamed` where a binder sits inside the one renamed: the outer
    /// letter of `other` is put back to `one`'s, the bodies are then one
    /// class by renaming the inner binder, which `rules::CLASS_BODY` carries
    /// up through the outer, and the outer is renamed last.
    pub(super) fn class_renamed_within(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        if one.label() == Some("crab") {
            return self.selection_renamed_within(one, other);
        }
        let Some(body_lemma) = one.label().and_then(|l| lookup(rules::CLASS_BODY, l))
        else {
            return Ok(None);
        };
        let letters: Vec<(usize, Term)> = one
            .children()
            .iter()
            .enumerate()
            .filter(|(_, c)| {
                c.variable().is_some()
                    && self.typecode(self.rpn(c).alone().unwrap_or_default())
                        == "setvar"
            })
            .map(|(i, c)| (i, c.clone()))
            .collect();
        if letters.len() != 1 {
            return Ok(None);
        }
        let (at, ours) = letters[0].clone();
        let theirs = other.children()[at].clone();
        if theirs.variable().is_none() || theirs.variable() == ours.variable() {
            return Ok(None);
        }
        let mut put = Binding::new();
        put.insert(theirs.variable_symbol().unwrap(), ours.clone());
        let middle = other.substitute(&put);
        let differ: Vec<usize> = (0..one.children().len())
            .filter(|&i| {
                self.rpn(&one.children()[i]) != self.rpn(&middle.children()[i])
            })
            .collect();
        if differ.len() != 1 {
            return Ok(None);
        }
        let Some(inner) = self
            .class_renamed(&one.children()[differ[0]], &middle.children()[differ[0]])?
        else {
            return Ok(None);
        };
        let says = self.statement(body_lemma);
        let variables = names_of(&says);
        let Some(binding) = fit(&says.children()[0], one, &Binding::new(), &variables)
            .and_then(|b| fit(&says.children()[1], &middle, &b, &variables))
        else {
            return Ok(None);
        };
        let sig = self.sig(body_lemma).clone();
        let asked = self.essential(&sig.essentials[0]).substitute(&binding);
        let (under, equal) = (
            self.rpn(&asked.children()[0]),
            self.rpn(&asked.children()[1]),
        );
        let carried =
            self.b
                .ap("a1i", &binds! {"ph" => &equal, "ps" => &under}, &[&inner]);
        let lifted = self.b.ap(body_lemma, &self.spelt(&binding), &[&carried]);
        let Some(outer) = self.class_renamed(&middle, other)? else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(one), "B" => self.rpn(&middle), "C" => self.rpn(other)},
            &[&lifted, &outer],
        )))
    }

    /// `class_renamed_within` of a selection, {y ∈ B | φ}, whose body is a
    /// statement: the body's own bound letters are renamed first, under the
    /// selection's letter as it stands (`renaming`, carried in by `rabbii`),
    /// and then the selection's letter (`class_renamed`). {y ∈ B : there is
    /// x ∈ X with F(x) = y} is so {j ∈ B : there is i ∈ X with F(i) = j}.
    pub(super) fn selection_renamed_within(
        &mut self,
        one: &Term,
        other: &Term,
    ) -> Checked<Option<Proof>> {
        let [_, ours, _] = one.children() else {
            return Ok(None);
        };
        let theirs = &other.children()[1];
        let (Some(_), Some(their_letter)) = (ours.variable(), theirs.variable()) else {
            return Ok(None);
        };
        if ours.variable() == theirs.variable() {
            return Ok(None);
        }
        let mut put = Binding::new();
        put.insert(Symbol::of(their_letter), ours.clone());
        let middle = other.substitute(&put);
        if self.rpn(&one.children()[2]) != self.rpn(&middle.children()[2]) {
            return Ok(None);
        }
        let Some(inner) = self.renaming(&one.children()[0], &middle.children()[0])?
        else {
            return Ok(None);
        };
        let Some(lifted) = self.by_lemma("rabbii", one, &middle, &[&inner]) else {
            return Ok(None);
        };
        let Some(outer) = self.class_renamed(&middle, other)? else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "eqtri",
            &binds! {"A" => self.rpn(one), "B" => self.rpn(&middle), "C" => self.rpn(other)},
            &[&lifted, &outer],
        )))
    }

    /// ( where -> y <-> x ), or `=`, from a proof of `x` against `y`.
    pub fn flipped(&self, where_: &Rpn, x: &Term, y: &Term, proof: &Proof) -> Proof {
        let (a, b) = (self.rpn(x), self.rpn(y));
        if self.is_wff(x) {
            self.b.ap(
                "bicomd",
                &binds! {"ph" => where_, "ps" => &a, "ch" => &b},
                &[proof],
            )
        } else {
            self.b.ap(
                "eqcomd",
                &binds! {"ph" => where_, "A" => &a, "B" => &b},
                &[proof],
            )
        }
    }

    /// Two terms a conditional rule makes one, at this place; else None: the
    /// rule is applied to either side where it stands, what it asks is
    /// settled here, and what it gives must then have the other side's
    /// standard form.
    pub(super) fn conditioned(
        &mut self,
        one: &Term,
        other: &Term,
        where_: &Rpn,
        held: &Facts,
    ) -> Checked<Option<Proof>> {
        for rule in self.rewrites(true).iter() {
            for (a, b, forward) in [(one, other, true), (other, one, false)] {
                let Some(bound) = fit(&rule.given, a, &Binding::new(), &rule.names)
                else {
                    continue;
                };
                if !rule.gives.names().iter().all(|n| bound.contains_key(&**n)) {
                    continue;
                }
                let became = rule.gives.substitute(&bound);
                let ours = self.standard(&became);
                let ours = self.rpn(&ours);
                let theirs = self.standard(b);
                let theirs = self.rpn(&theirs);
                if ours != theirs && !self.rebound(&ours, &theirs) {
                    continue;
                }
                let Built(made) = self.standard_proof(
                    a,
                    &How::Rule(rule.label.clone()),
                    &became,
                    where_,
                    held,
                )?
                else {
                    continue;
                };
                let mut links = vec![ChainLink {
                    from: a.clone(),
                    to: became.clone(),
                    proof: made,
                }];
                if self.rpn(&became) != self.rpn(b) {
                    let Built(rest) = self.congruence(
                        &became,
                        b,
                        where_,
                        held,
                        None,
                        &Leaf::Rows(vec![Row::Standard]),
                    )?
                    else {
                        continue;
                    };
                    links.push(ChainLink {
                        from: became,
                        to: b.clone(),
                        proof: rest,
                    });
                }
                let proof = self.chained(where_, &links);
                return Ok(Some(if forward {
                    proof
                } else {
                    self.flipped(where_, a, b, &proof)
                }));
            }
        }
        Ok(None)
    }

    // --- a lemma's own substitutions ------------------------------------

    /// A wff slot an essential fixes by saying it is a substitution: `elrab`
    /// asks `( x = A -> ( ph <-> ps ) )`, and where the claim has not filled
    /// `ps` this hypothesis is the only thing that says what it is.
    pub fn substituted_slot(&self, asked: &Term, binding: &Binding) -> Option<Binding> {
        if asked.label() != Some("wi") || asked.children().len() != 2 {
            return None;
        }
        let (same_, iff) = (&asked.children()[0], &asked.children()[1]);
        if same_.label() != Some("wceq") || iff.label() != Some("wb") {
            return None;
        }
        let over = same_.children()[0].substitute(binding);
        let element = same_.children()[1].substitute(binding);
        let (body, slot) = (&iff.children()[0], &iff.children()[1]);
        let held = slot.variable().and_then(|v| binding.get(v));
        if slot.variable().is_none()
            || over.label() != Some("cv")
            || over.children()[0].variable().is_none()
            || held.is_some_and(|h| h.variable() != slot.variable())
            || !body.names().iter().all(|n| binding.contains_key(&**n))
        {
            return None;
        }
        // The body holds the variable as a binder writes it, `cv` over a
        // setvar; the element is a class. Stripping the `cv` is what lets the
        // one stand in for the other.
        let name = over.children()[0].variable().unwrap().to_string();
        let marks: BTreeSet<String> = iter::once(name.clone()).collect();
        let said = as_class(&body.substitute(binding), &marks);
        let mut put = Binding::new();
        put.insert(Symbol::of(&name), element);
        let mut out = Binding::new();
        out.insert(slot.variable_symbol().unwrap(), said.substitute(&put));
        Some(out)
    }

    /// The side of an equation, the innermost body of an existential, that
    /// names none of its witnesses, where the other names one; else None.
    pub(super) fn witnessless_side(
        &self,
        body: &Term,
        layers: &[(Term, Rpn, Rpn)],
    ) -> Option<Rpn> {
        if body.label() != Some("wceq") || body.children().len() != 2 {
            return None;
        }
        let names = |t: &Term| {
            let spelt = self.rpn(t);
            layers
                .iter()
                .any(|(_, v, _)| v.alone().is_some_and(|v| spelt.has(v)))
        };
        let (left, right) = (&body.children()[0], &body.children()[1]);
        match (names(left), names(right)) {
            (false, true) => Some(self.rpn(left)),
            (true, false) => Some(self.rpn(right)),
            _ => None,
        }
    }

    /// A restricted existential a citation asks, or the right side a
    /// definition concludes from (`conclude`), proved at the witnesses the
    /// checker read the citation as naming (`witnesses_read`), from the
    /// lines the step cites and its `requires` lines. Built from the
    /// innermost quantifier out, which is the order the witnesses go in.
    pub fn witnessed(
        &mut self,
        step: &Step,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let layers = self.layers_of(wanted);
        let mut sources = self.witness_sources(step, scope, facts, lines)?;
        if let Some(p) = self.claim_cited(&sources, wanted, scope, facts)? {
            return Ok(Built(p));
        }
        let rest = layers[layers.len() - 1].0.clone();
        // An equation the body asks whose one side names no witness is the
        // same on both sides once the witnesses are read off the other, and
        // needs no line (`SYNTAX.md`, the literal-instance rule): a·x + b·y =
        // a·m + b·n is met by m := x and n := y.
        if let Some(sides) = self.witnessless_side(&rest, &layers) {
            let said = t!(sides, sides, "wceq");
            let proof = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &sides}, &[]);
            sources.push((said, proof));
        }
        // The witnesses are as many as the checker read, from the outermost
        // quantifier in (`witnesses_read`).
        let found = take!(self.witnesses_read(step, wanted, &layers)?);
        let layers = &layers[..found.len()];
        self.witnessed_at(
            step, wanted, layers, &found, scope, facts, lines, &sources, None,
        )
    }

    /// What an `exhibit` step of several letters proves: `witnessed`, with
    /// the witnesses the values the checker read the step as showing
    /// (`exhibited_here`), not searched for among the lines.
    pub fn exhibited(
        &mut self,
        step: &Step,
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let layers = self.layers_of(wanted);
        let sources = self.witness_sources(step, scope, facts, lines)?;
        let found = self.exhibited_here(step)?;
        if layers
            .iter()
            .any(|(_, v, _)| !found.contains_key(&t!(v, "cv")))
        {
            return Err(self.unreached(
                step.line,
                "the checker reads no value for a letter this exhibit binds",
            ));
        }
        let read = self.exhibit_read(step)?;
        let recorded = WitnessFacts {
            facts: read.shown,
            values: read.values.into_iter().collect(),
            turned: false,
        };
        self.witnessed_at(
            step,
            wanted,
            &layers,
            &found,
            scope,
            facts,
            lines,
            &sources,
            Some(&recorded),
        )
    }

    /// A definition's right side read backwards, a "there is" the checker
    /// shows at the witnesses it read (`witnesses_read`), each fact of it
    /// from where the checker recorded it (`Cited::unfolded`): each
    /// letter's membership in its domain, from the outermost in, then each
    /// part of the body, turned where the lemma writes its equation the
    /// other way round (`turned`).
    pub fn folded_at_witness(
        &mut self,
        step: &Step,
        wanted: &Term,
        turned: bool,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no reading of this citation",
            ));
        };
        let Some(parts) = cited.unfolded.iter().flatten().next() else {
            return Err(self.unreached(
                step.line,
                "the checker recorded no unfolding of the right side",
            ));
        };
        let mut members = Vec::new();
        let mut body = Vec::new();
        let mut at: &[Unfolded] = parts;
        loop {
            match at {
                [Unfolded::Witness {
                    member,
                    body: inner,
                    ..
                }] => {
                    let Unfolded::Fact { fact, by } = member.as_ref() else {
                        return Err(self.unreached(
                            step.line,
                            "the checker recorded a witness's domain as no fact",
                        ));
                    };
                    members.push(unfolded_supplied(fact, by));
                    at = inner;
                }
                rest => {
                    for part in rest {
                        let Unfolded::Fact { fact, by } = part else {
                            return Err(self.unreached(
                                step.line,
                                "the checker recorded a \"there is\" inside the body beside other parts",
                            ));
                        };
                        body.push(unfolded_supplied(fact, by));
                    }
                    break;
                }
            }
        }
        let layers = self.layers_of(wanted);
        let found = take!(self.witnesses_read(step, wanted, &layers)?);
        if found.len() != members.len() {
            return Err(self.unreached(
                step.line,
                "the checker read as many witnesses as it recorded domains for",
            ));
        }
        let layers = &layers[..found.len()];
        members.extend(body);
        let recorded = WitnessFacts {
            facts: members,
            values: NodeBinding::new(),
            turned,
        };
        self.witnessed_at(
            step,
            wanted,
            layers,
            &found,
            scope,
            facts,
            lines,
            &[],
            Some(&recorded),
        )
    }

    /// The witnesses the checker read the citation `step` makes as naming
    /// for `wanted`, a "there is" the cited item asks or a definition it
    /// folds says (`Cited::bound`): what each of its letters is put to,
    /// from the outermost in, by the variable the letter stands for in
    /// `layers`, the quantifiers of `wanted`. The item writes the "there is"
    /// in its own letters, which the build may have renamed, so it is found
    /// among the item's by how many letters it binds. A "there is" inside
    /// the body that a line says whole, the "there is f" of "n ∈ ℕ₀ and
    /// there is f with …", has no witness read, and the witnesses are of
    /// the quantifiers outside it. Declined where the checker read no
    /// witness for it: a step whose citation proves its "there is" another
    /// way, unfolding a definition, asks it as a side condition first.
    pub(super) fn witnesses_read(
        &mut self,
        step: &Step,
        wanted: &Term,
        layers: &[(Term, Rpn, Rpn)],
    ) -> Checked<Route<IndexMap<Rpn, Rpn>>> {
        let Some(cited) = self.citation_read(step).cloned() else {
            return Ok(Route::no("the checker reads no citation on this line"));
        };
        let library = self.item_library();
        let groups = library.groups(&cited.item).unwrap_or_default();
        let Some(group) = groups.get(cited.group) else {
            return Err(
                self.unreached(step.line, "the checker reads a group the item has not")
            );
        };
        // A "there is" is read in the letters the checker matched it in: the
        // item's own, and where a letter standing for a rule is applied, the
        // rule's at what it is applied to (`citing::filled`), which may keep
        // its letter apart from a value. Nothing else is filled in, so a
        // value that spells an item's letter does not rename it.
        let ctx = &library.ctx;
        let applied = |node: &Node| {
            ctx.props.contains_key(&node.notation())
                && node.children.len() == 2
                && node.children[0].is_name()
                && cited
                    .binding
                    .get(&node.children[0].text)
                    .is_some_and(|v| v.notation() == PROPERTY_OF)
        };
        let mut nodes = Vec::new();
        for s in group.asked().chain(&group.gives) {
            for node in s.walk() {
                if applied(&node) {
                    nodes.extend(citing::filled(&node, &cited.binding, ctx).walk());
                }
                nodes.push(node);
            }
        }
        let mut read: Vec<Vec<Node>> = Vec::new();
        let mut shapes: IndexSet<Vec<ByShape>> = IndexSet::new();
        for node in nodes {
            let letters = Self::existential_letters(&node, &library.exists);
            if letters.len() != layers.len() {
                continue;
            }
            let values: Vec<Node> = letters
                .iter()
                .map_while(|l| cited.bound.get(l).cloned())
                .collect();
            if !values.is_empty()
                && shapes.insert(values.iter().map(Node::by_shape).collect())
            {
                read.push(values);
            }
        }
        let values = match read.as_slice() {
            [one] => one.clone(),
            [] => {
                return Ok(Route::no(format!(
                    "the checker reads no witness for {}",
                    self.render(&self.rpn(wanted))
                )))
            }
            _ => {
                return Err(self.unreached(
                    step.line,
                    format!(
                        "the checker reads witnesses for more than one \"there is\" like {}",
                        self.render(&self.rpn(wanted))
                    ),
                ))
            }
        };
        let mut found = IndexMap::new();
        for ((_, variable, _), value) in layers.iter().zip(&values) {
            found.insert(t!(variable, "cv"), self.term(value)?);
        }
        Ok(Built(found))
    }

    /// The letters a nest of "there is" binds, from the outermost in; none
    /// where `node` is no "there is".
    pub(super) fn existential_letters(
        node: &Node,
        exists: &FxIndexSet<NotationId>,
    ) -> Vec<Symbol> {
        let mut letters = Vec::new();
        let mut at = node;
        while exists.contains(&at.notation()) && at.children.len() >= 2 {
            letters.push(at.children[0].text);
            match at.children.get(2) {
                Some(body) => at = body,
                None => break,
            }
        }
        letters
    }

    /// The quantifiers of a nest of "there is", from the outermost in: the
    /// body each binds over, its variable, and its domain.
    pub(super) fn layers_of(&self, wanted: &Term) -> Vec<(Term, Rpn, Rpn)> {
        let mut layers = Vec::new();
        let mut rest = wanted.clone();
        while rest.label() == Some("wrex") {
            let kids = rest.children().to_vec();
            layers.push((kids[0].clone(), self.rpn(&kids[1]), self.rpn(&kids[2])));
            rest = kids[0].clone();
        }
        layers
    }

    /// The lines a step cites and its requires lines, with their proofs:
    /// where witnesses are read. A line proved before a block opened holds
    /// inside it too, and the scope's own copy is what says so where the
    /// step sits.
    pub(super) fn witness_sources(
        &mut self,
        step: &Step,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Vec<(Rpn, Proof)>> {
        let mut sources: Vec<(Rpn, Proof)> = Vec::new();
        for r in &step.just.refs {
            let Some(cited) = self.line_written(r, lines) else {
                continue;
            };
            let proof = match self.held(facts, &cited.claim, scope)? {
                Some(p) => p,
                None => cited.proof,
            };
            sources.push((cited.claim, proof));
        }
        for r in &step.requires {
            let said = self.claim_of(&r.fact)?;
            if let Some(proof) = self.held(facts, &said, scope)? {
                sources.push((said, proof));
            }
        }
        Ok(sources)
    }

    /// A cited line that is the claim once identity elements are dropped
    /// and bound letters renamed names no witness: it is the claim
    /// (`reached`), as "there is q ∈ ℤ with q·N = A" is "there is z ∈ ℤ
    /// with z·N + 0 = A".
    pub(super) fn claim_cited(
        &mut self,
        sources: &[(Rpn, Proof)],
        wanted: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let want = self.rpn(wanted);
        for (said, proof) in sources {
            if self.to_term(said).label() != Some("wrex") {
                continue;
            }
            if let Some(p) = self.reached(proof, said, &want, scope, facts)? {
                return Ok(Some(p));
            }
        }
        Ok(None)
    }

    /// `witnessed` with the witnesses `found` for the claim's letters, by
    /// the variable each stands for, and the lines the step cites and
    /// requires, with their proofs. Where the checker recorded what shows
    /// the "there is" (`recorded`), each fact is taken from there and from
    /// nowhere else.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn witnessed_at(
        &mut self,
        step: &Step,
        wanted: &Term,
        layers: &[(Term, Rpn, Rpn)],
        found: &IndexMap<Rpn, Rpn>,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        sources: &[(Rpn, Proof)],
        recorded: Option<&WitnessFacts>,
    ) -> Checked<Route<Proof>> {
        // A witness may spell a letter the claim binds, as the n obtained
        // for "there are m, n ∈ ℕ with …" does, and `rspcev` keeps its
        // letter apart from what the body says. So the claim is shown under
        // letters nothing holds and renamed back, as `exhibit` does for one.
        let letters: Vec<Rpn> = layers.iter().map(|(_, v, _)| v.clone()).collect();
        let meets = found
            .values()
            .any(|w| letters.iter().any(|v| v.alone().is_some_and(|v| w.has(v))));
        if meets {
            let witnesses: Vec<Term> =
                found.values().map(|w| self.to_term(w)).collect();
            let mut seen: Vec<&Term> = witnesses.iter().collect();
            seen.push(wanted);
            let names: Vec<Symbol> = letters
                .iter()
                .filter_map(|l| {
                    self.var_of(l.alone().unwrap_or_default()).variable_symbol()
                })
                .collect();
            let Some(moved) = self.unheld_for(names, &seen) else {
                return Err(
                    self.defect(step.line, "no letter left to exhibit the witness by")
                );
            };
            let renamed = wanted.substitute(&moved);
            // The same witnesses, for the letters the claim is renamed to.
            let apart = self.layers_of(&renamed);
            let carried: IndexMap<Rpn, Rpn> = layers
                .iter()
                .zip(&apart)
                .map(|((_, was, _), (_, now, _))| {
                    (t!(now, "cv"), found[&t!(was, "cv")].clone())
                })
                .collect();
            let made = take!(self.witnessed_at(
                step, &renamed, &apart, &carried, scope, facts, lines, sources,
                recorded
            )?);
            let Some(back) = self.renaming(&renamed, wanted)? else {
                return Err(self.defect(
                    step.line,
                    "the renamed claim does not read back as the claim",
                ));
            };
            return Ok(Built(self.b.ap(
                "sylib",
                &binds! {"ph" => scope, "ps" => &self.rpn(&renamed), "ch" => &self.rpn(wanted)},
                &[&made, &back],
            )));
        }
        // Where a line the step cites is all the claim says of the witnesses,
        // its own proof is taken, turned where it faces the other way.
        let mut innermost = layers[layers.len() - 1].0.clone();
        for (_, v, _) in layers {
            let mark = t!(v, "cv");
            innermost = self.restated(&innermost, &mark, &found[&mark]);
        }
        let inner_rpn = self.rpn(&innermost);
        let turned = turned_equation(&innermost).map(|t| self.rpn(&t));
        let said = |want: &Rpn| sources.iter().find(|(s, _)| s == want).map(|(_, p)| p);
        // An exhibit's facts are the ones the checker recorded it as shown
        // by (`Exhibit::shown`): each letter in its domain, outermost first,
        // then each part of the body joined by "and".
        let values = recorded.map(|r| r.values.clone()).unwrap_or_default();
        let lemma_turned = recorded.is_some_and(|r| r.turned);
        let recorded: Option<&Vec<Supplied>> = recorded.map(|r| &r.facts);
        let (in_domains, in_body): (&[Supplied], &[Supplied]) = match recorded {
            Some(all) if all.len() >= layers.len() => all.split_at(layers.len()),
            Some(_) => {
                return Err(self.unreached(
                    step.line,
                    "the checker recorded fewer facts than the exhibit's letters",
                ))
            }
            None => (&[], &[]),
        };
        let mut proof = if recorded.is_some() {
            self.shown_body(
                step,
                &innermost,
                in_body,
                &values,
                lemma_turned,
                scope,
                facts,
            )?
        } else if inner_rpn.alone() == Some("wtru") {
            // A body that says nothing of its variable holds outright, by
            // the one lemma that states truth.
            pf!(self.b; "wtru", scope, "tru", "a1i")
        } else if let Some(p) = said(&inner_rpn) {
            p.clone()
        } else if let Some(p) = turned.as_ref().and_then(said) {
            let (a, b) = (
                self.rpn(&innermost.children()[0]),
                self.rpn(&innermost.children()[1]),
            );
            pf!(self.b; scope, b, a, p, "eqcomd")
        } else {
            take!(self.settle_or_bare(
                &innermost,
                scope,
                facts,
                Some(step),
                Some(lines)
            )?)
        };
        for i in (0..layers.len()).rev() {
            let (body, var, over) = layers[i].clone();
            let mark = t!(var, "cv");
            let mut held = body;
            let mut over = self.to_term(&over);
            // The quantifiers further out are still open here, and the ones
            // already closed have their witnesses in place: in the body, and
            // in the domain, which may run over one of them, as a walk's
            // vertices run over {0, …, n}.
            for (_, v, _) in &layers[..i] {
                let m = t!(v, "cv");
                held = self.restated(&held, &m, &found[&m]);
                over = self.restated(&over, &m, &found[&m]);
            }
            let over = self.rpn(&over);
            let witness = found[&mark].clone();
            let here = self.restated(&held, &mark, &witness);
            let (ph, ps) = (self.rpn(&held), self.rpn(&here));
            let instance = if ph == ps {
                // The body does not mention the variable, so the witness
                // changes nothing in it: `biidd` says so outright.
                pf!(self.b; t!(mark, witness, "wceq"), ph, "biidd")
            } else {
                let tie = self.to_term(&t!(
                    t!(mark, witness, "wceq"),
                    t!(ph, ps, "wb"),
                    "wi"
                ));
                take!(self.prove_essential(&tie, scope, facts)?)
            };
            let member = t!(witness, over, "wcel");
            let supplied = match in_domains.get(i) {
                Some(shown) => self.shown_proof(step, shown, &member, scope, facts)?,
                None => self.required(step, &member, scope, facts)?,
            };
            let both = pf!(self.b; scope, member, ps, supplied, proof, "jca");
            proof = pf!(self.b; scope, t!(member, ps, "wa"), t!(ph, var, over, "wrex"), both,
                ph, ps, var, witness, over, instance, "rspcev", "syl");
        }
        Ok(Built(proof))
    }

    /// `term` with every occurrence of the subterm `was` reading `now`, both
    /// given in reverse Polish, because a term is compared by what it spells.
    pub fn restated(&self, term: &Term, was: &Rpn, now: &Rpn) -> Term {
        if self.rpn(term) == *was {
            return self.to_term(now);
        }
        if term.variable().is_some() {
            return term.clone();
        }
        term.with_children(
            term.children()
                .iter()
                .map(|c| self.restated(c, was, now))
                .collect(),
        )
    }

    /// What a lemma's naming hypothesis says its own variables are: where a
    /// lemma names a map in a hypothesis and speaks of its range in the
    /// conclusion, what the map binds, where that runs and what it builds are
    /// read back out of it; and the other way, where the naming is what says
    /// what a variable is.
    pub fn read_off(
        &self,
        sig: &Signature,
        binding: Binding,
        variables: &Vars,
    ) -> Binding {
        let mut binding = binding;
        for text in &sig.essentials {
            let asked = self.essential(text);
            if asked.label() != Some("wceq") || asked.children().len() != 2 {
                continue;
            }
            let name = asked.children()[0].variable_symbol();
            if let Some(name) = &name {
                if !binding.contains_key(name)
                    && asked.children()[1]
                        .names()
                        .iter()
                        .all(|n| binding.contains_key(&**n))
                {
                    let value = asked.children()[1].substitute(&binding);
                    binding.insert(*name, value);
                    continue;
                }
            }
            let Some(name) = name.filter(|n| binding.contains_key(n)) else {
                continue;
            };
            let mut vars = variables.clone();
            vars.extend(asked.names().iter().cloned());
            if let Some(said) = fit(
                &asked.children()[1],
                &binding[&name].clone(),
                &binding,
                &vars,
            ) {
                binding = said;
            }
        }
        binding
    }

    /// What a lemma asking `( x = A -> ( ph <-> ps ) )` means by `ps`: `ps`
    /// is `ph` with the variable reading the term. Worked out and not taken
    /// from the step. A hypothesis relating two terms says the same thing of
    /// them as one relating two formulas.
    pub fn instanced(&self, sig: &Signature, binding: Binding) -> Binding {
        let mut out = binding;
        let kinds: IndexMap<&str, &str> = sig
            .floats
            .iter()
            .map(|(t, v)| (v.as_str(), t.as_str()))
            .collect();
        for text in &sig.essentials {
            let asked = self.essential(text);
            if asked.label() != Some("wi") {
                continue;
            }
            let (at, says) = (&asked.children()[0], &asked.children()[1]);
            if at.label() != Some("wceq")
                || !matches!(says.label(), Some("wb") | Some("wceq"))
                || at.children()[0].label() != Some("cv")
            {
                continue;
            }
            let Some(name) = says.children()[1].variable_symbol() else {
                continue;
            };
            let summand = says.children()[0].variable_symbol();
            let index = at.children()[0].children()[0].clone();
            let other = at.children()[1].clone();
            // Read the other way where the claim fixed the instance and not
            // the summand: A is B with the claim's index moved to a letter
            // nothing holds.
            if let Some(summand) = &summand {
                if !out.contains_key(summand)
                    && kinds.get(summand.as_str()) == Some(&"class")
                    && out.contains_key(&name)
                    && !index.variable().is_some_and(|v| out.contains_key(v))
                    && other.label() == Some("cv")
                    && other.children()[0]
                        .variable()
                        .is_some_and(|v| out.contains_key(v))
                {
                    let Some(index_letter) = index.variable().map(Symbol::of) else {
                        continue;
                    };
                    let held: Vec<&Term> = out.values().collect();
                    let Some(letter) = self.unheld(&held) else {
                        continue;
                    };
                    let was = self.rpn(&Term::apply(
                        "cv",
                        vec![out[other.children()[0].variable().unwrap()].clone()],
                    ));
                    let now = self.rpn(&Term::apply("cv", vec![letter.clone()]));
                    let value = self.restated(&out[&name].clone(), &was, &now);
                    out.insert(index_letter, letter);
                    out.insert(*summand, value);
                    continue;
                }
            }
            if at
                .names()
                .iter()
                .any(|v| !out.contains_key(&**v) && kinds.get(&**v) == Some(&"class"))
            {
                continue;
            }
            let was = self.rpn(&at.children()[0].substitute(&out));
            let now = self.rpn(&at.children()[1].substitute(&out));
            let value = self.restated(&says.children()[0].substitute(&out), &was, &now);
            out.insert(name, value);
        }
        out
    }

    // --- one claim spelt two ways ---------------------------------------

    /// A proof that two terms written differently agree: `same` says so.
    pub fn bridging(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &Rpn,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        self.same(given, want, scope, facts, step)
    }
}
