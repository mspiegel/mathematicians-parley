//! `inspection`: a claim about a set listed in full, checked element by
//! element against what the cited lines say (`METHODS.md`).
//!
//! A listed set is read in one standard form, the singletons of its
//! elements joined from the left, `(({a} ∪ {b}) ∪ {c})`, which is how set.mm
//! defines its pair and triple (`df-pr`, `df-tp`). A set the lines give by an
//! equation is read through it. Every proof here is in deduction form under
//! the step's scope.

use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::{t, take};

/// A set read in the standard form: its elements in order, and a proof
/// that the set is the union of their singletons.
struct Listing {
    elements: Vec<Term>,
    /// ( scope -> set = the union of the elements' singletons ).
    proof: Proof,
}

/// What the cited lines settle of a property at one element.
enum Settled {
    Holds(Proof),
    Fails(Proof),
}

/// The elements of a set-builder over a listed set that its property keeps,
/// and a proof that the set-builder is the union of their singletons, or
/// the empty set where none is kept.
struct Kept {
    elements: Vec<Term>,
    proof: Proof,
}

impl Elaborator<'_> {
    /// The step's claim, by inspection of the sets the cited lines list.
    pub fn inspection(
        &mut self,
        step: &Step,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let supplied = self.supplied(Some(step), scope, facts)?;
        let cited = self.with_cited(Some(step), scope, &supplied, None);
        let known = facts.with(&cited);
        // A graph given in full says dozens of things in one line, and each
        // is a fact the inspection reads: the line is taken apart to the end.
        for (fact, proof) in known.entries() {
            self.unpack(&fact, &proof, scope, &known, usize::MAX);
        }
        let claim = self.to_term(term);
        let made = self.inspected(&claim, scope, &known)?;
        match made {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "step {} is not seen by inspection of what it cites: {}",
                    fmt(&step.number),
                    self.say(&d)
                ),
            )),
        }
    }

    fn inspected(
        &mut self,
        claim: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = claim.children().to_vec();
        match claim.label() {
            Some("wcel") if claim.variable().is_none() => {
                let (element, set) = (&kids[0], &kids[1]);
                let listing = take!(self.listing(set, scope, known)?);
                let Some(at) = self.position(element, &listing.elements) else {
                    return Ok(Route::no(format!(
                        "{} is not one of the things {} lists",
                        self.render(&self.rpn(element)),
                        self.render(&self.rpn(set))
                    )));
                };
                let inside = take!(self.in_union(
                    element,
                    &listing.elements,
                    at,
                    scope,
                    known
                )?);
                Ok(Built(self.b.ap(
                    "eleqtrrd",
                    &binds! {"ph" => scope, "A" => &self.rpn(element),
                    "B" => &self.union_of(&listing.elements), "C" => &self.rpn(set)},
                    &[&inside, &listing.proof],
                )))
            }
            Some("wn") if kids[0].label() == Some("wcel") => {
                let inner = kids[0].children().to_vec();
                let (element, set) = (&inner[0], &inner[1]);
                let listing = take!(self.listing(set, scope, known)?);
                let outside = take!(self.not_in_union(
                    element,
                    &listing.elements,
                    scope,
                    known
                )?);
                self.carried_out(element, set, &listing, outside, scope)
                    .map(Built)
            }
            Some("wceq") if kids[0].label() == Some("crab") => {
                self.set_builder(&kids[0], &kids[1], scope, known)
            }
            Some("wceq")
                if kids[0].label() == Some("cfv")
                    && self.rpn(&kids[0].children()[1]) == "chash" =>
            {
                self.size(&kids[0].children()[0], &kids[1], scope, known)
            }
            _ => Ok(Route::no(
                "inspection says what is in a listed set, which of its elements \
                 have a property, or how many it has",
            )),
        }
    }

    /// ( scope -> ¬ t ∈ set ), from ( scope -> ¬ t ∈ the set's listing ).
    fn carried_out(
        &mut self,
        element: &Term,
        set: &Term,
        listing: &Listing,
        outside: Proof,
        scope: &str,
    ) -> Checked<Proof> {
        let (t, s, u) = (
            self.rpn(element),
            self.rpn(set),
            self.union_of(&listing.elements),
        );
        let same = self.b.ap(
            "eleq2d",
            &binds! {"ph" => scope, "A" => &s, "B" => &u, "C" => &t},
            &[&listing.proof],
        );
        Ok(self.b.ap(
            "mtbird",
            &binds! {"ph" => scope, "ps" => &t!(t, s, "wcel"), "ch" => &t!(t, u, "wcel")},
            &[&outside, &same],
        ))
    }

    /// The union of the singletons of `elements`, joined from the left.
    fn union_of(&self, elements: &[Term]) -> String {
        let mut out = t!(self.rpn(&elements[0]), "csn");
        for e in &elements[1..] {
            out = t!(out, t!(self.rpn(e), "csn"), "cun");
        }
        out
    }

    /// Where `element` stands among `elements`, as written.
    fn position(&self, element: &Term, elements: &[Term]) -> Option<usize> {
        let said = self.rpn(element);
        elements.iter().position(|e| self.rpn(e) == said)
    }

    /// A set as the cited lines list it: written as a listing, or given by
    /// an equation with one.
    fn listing(
        &mut self,
        set: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Listing>> {
        if let Some((elements, closed)) = self.written_listing(set) {
            let union = self.union_of(&elements);
            let proof = self.b.ap(
                "a1i",
                &binds! {"ph" => &t!(self.rpn(set), union, "wceq"), "ps" => scope},
                &[&closed],
            );
            return Ok(Built(Listing { elements, proof }));
        }
        let said = self.rpn(set);
        for (fact, proof) in known.entries() {
            let held = self.to_term(&fact);
            if held.label() != Some("wceq") || held.variable().is_some() {
                continue;
            }
            let sides = held.children().to_vec();
            let (other, flipped) = if self.rpn(&sides[0]) == said {
                (sides[1].clone(), false)
            } else if self.rpn(&sides[1]) == said {
                (sides[0].clone(), true)
            } else {
                continue;
            };
            let Some((elements, closed)) = self.written_listing(&other) else {
                continue;
            };
            let union = self.union_of(&elements);
            let named = self.rpn(&other);
            let to_listed = if flipped {
                self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => &named, "B" => &said},
                    &[&proof],
                )
            } else {
                proof
            };
            let proof = self.b.ap(
                "eqtrdi",
                &binds! {"ph" => scope, "A" => &said, "B" => &named, "C" => &union},
                &[&to_listed, &closed],
            );
            return Ok(Built(Listing { elements, proof }));
        }
        Ok(Route::no(format!(
            "nothing cited lists {}",
            self.render(&self.rpn(set))
        )))
    }

    /// A set written as a listing, its elements and the closed proof that
    /// it is the union of their singletons: a singleton, a pair, a triple,
    /// or a listing joined with one more singleton.
    fn written_listing(&self, set: &Term) -> Option<(Vec<Term>, Proof)> {
        if set.variable().is_some() {
            return None;
        }
        let kids = set.children().to_vec();
        match set.label()? {
            "csn" => {
                let one = self.rpn(set);
                Some((kids, self.b.ap("eqid", &binds! {"A" => &one}, &[])))
            }
            "cpr" => {
                let (a, b) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
                Some((
                    kids,
                    self.b.ap("df-pr", &binds! {"A" => &a, "B" => &b}, &[]),
                ))
            }
            "ctp" => {
                let (a, b, c) =
                    (self.rpn(&kids[0]), self.rpn(&kids[1]), self.rpn(&kids[2]));
                let tp =
                    self.b
                        .ap("df-tp", &binds! {"A" => &a, "B" => &b, "C" => &c}, &[]);
                let pr = self.b.ap("df-pr", &binds! {"A" => &a, "B" => &b}, &[]);
                let pair = t!(a, b, "cpr");
                let pair_union = t!(t!(a, "csn"), t!(b, "csn"), "cun");
                let single = t!(c, "csn");
                let lifted = self.b.ap(
                    "uneq1i",
                    &binds! {"A" => &pair, "B" => &pair_union, "C" => &single},
                    &[&pr],
                );
                let proof = self.b.ap(
                    "eqtri",
                    &binds! {"A" => &self.rpn(set), "B" => &t!(pair, single, "cun"),
                    "C" => &t!(pair_union, single, "cun")},
                    &[&tp, &lifted],
                );
                Some((kids, proof))
            }
            "cun" if kids[1].label() == Some("csn") => {
                let (mut elements, inner) = self.written_listing(&kids[0])?;
                let last = kids[1].children()[0].clone();
                let (was, single) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
                let now = self.union_of(&elements);
                let proof = self.b.ap(
                    "uneq1i",
                    &binds! {"A" => &was, "B" => &now, "C" => &single},
                    &[&inner],
                );
                elements.push(last);
                Some((elements, proof))
            }
            _ => None,
        }
    }

    /// ( scope -> t ∈ the union of `elements`' singletons ), t being the
    /// element at `at`.
    fn in_union(
        &mut self,
        element: &Term,
        elements: &[Term],
        at: usize,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let t = self.rpn(element);
        if elements.len() == 1 {
            let is_set = take!(self.a_set(element, scope, known)?);
            let law = self.b.ap("snidg", &binds! {"A" => &t, "V" => "cvv"}, &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &t!(t, "cvv", "wcel"),
                "ch" => &t!(t, t!(t, "csn"), "wcel")},
                &[&is_set, &law],
            )));
        }
        let (init, last) = elements.split_at(elements.len() - 1);
        let (front, back) = (self.union_of(init), self.union_of(last));
        let whole = t!(front, back, "cun");
        let (inner, law) = if at == elements.len() - 1 {
            (
                take!(self.in_union(element, last, 0, scope, known)?),
                self.b.ap(
                    "elun2",
                    &binds! {"A" => &t, "B" => &back, "C" => &front},
                    &[],
                ),
            )
        } else {
            (
                take!(self.in_union(element, init, at, scope, known)?),
                self.b.ap(
                    "elun1",
                    &binds! {"A" => &t, "B" => &front, "C" => &back},
                    &[],
                ),
            )
        };
        let part = if at == elements.len() - 1 {
            back
        } else {
            front
        };
        Ok(Built(self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => &t!(t, part, "wcel"), "ch" => &t!(t, whole, "wcel")},
            &[&inner, &law],
        )))
    }

    /// ( scope -> ¬ t ∈ the union of `elements`' singletons ), from the
    /// cited lines saying t differs from each.
    fn not_in_union(
        &mut self,
        element: &Term,
        elements: &[Term],
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let t = self.rpn(element);
        if elements.len() == 1 {
            let c = self.rpn(&elements[0]);
            let apart = take!(self.differs(element, &elements[0], scope, known)?);
            let law = self.b.ap("nelsn", &binds! {"A" => &t, "B" => &c}, &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &t!(t, c, "wne"),
                "ch" => &t!(t!(t, t!(c, "csn"), "wcel"), "wn")},
                &[&apart, &law],
            )));
        }
        let (init, last) = elements.split_at(elements.len() - 1);
        let (front, back) = (self.union_of(init), self.union_of(last));
        let not_front = take!(self.not_in_union(element, init, scope, known)?);
        let not_back = take!(self.not_in_union(element, last, scope, known)?);
        let (in_front, in_back) = (t!(t, front, "wcel"), t!(t, back, "wcel"));
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &t!(in_front, "wn"), "ch" => &t!(in_back, "wn")},
            &[&not_front, &not_back],
        );
        let either = t!(in_front, in_back, "wo");
        let law =
            self.b
                .ap("ioran", &binds! {"ph" => &in_front, "ps" => &in_back}, &[]);
        let neither = self.b.ap(
            "sylibr",
            &binds! {"ph" => scope,
            "ps" => &t!(t!(in_front, "wn"), t!(in_back, "wn"), "wa"),
            "ch" => &t!(either, "wn")},
            &[&both, &law],
        );
        let whole = t!(front, back, "cun");
        let split = self.b.ap(
            "elun",
            &binds! {"A" => &t, "B" => &front, "C" => &back},
            &[],
        );
        let split = self.b.ap(
            "a1i",
            &binds! {"ph" => &t!(t!(t, whole, "wcel"), either, "wb"), "ps" => scope},
            &[&split],
        );
        Ok(Built(self.b.ap(
            "mtbird",
            &binds! {"ph" => scope, "ps" => &t!(t, whole, "wcel"), "ch" => &either},
            &[&neither, &split],
        )))
    }

    /// ( scope -> t ≠ c ), from a cited line saying the two differ, either
    /// way round.
    fn differs(
        &mut self,
        one: &Term,
        other: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        for (x, y) in [(&a, &b), (&b, &a)] {
            let said = if let Some(p) = self.held(known, &t!(x, y, "wne"), scope)? {
                Some(p)
            } else if let Some(p) =
                self.held(known, &t!(t!(x, y, "wceq"), "wn"), scope)?
            {
                let law = self.b.ap("df-ne", &binds! {"A" => x, "B" => y}, &[]);
                Some(self.b.ap(
                    "sylibr",
                    &binds! {"ph" => scope, "ps" => &t!(t!(x, y, "wceq"), "wn"),
                    "ch" => &t!(x, y, "wne")},
                    &[&p, &law],
                ))
            } else {
                None
            };
            let Some(said) = said else { continue };
            if x == &a {
                return Ok(Built(said));
            }
            return Ok(Built(self.b.ap(
                "necomd",
                &binds! {"ph" => scope, "A" => &b, "B" => &a},
                &[&said],
            )));
        }
        Ok(Route::no(format!(
            "nothing cited says {} and {} differ",
            self.render(&a),
            self.render(&b)
        )))
    }

    /// ( scope -> t ∈ V ): a listed thing is a set.
    fn a_set(
        &mut self,
        element: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let said = self.to_term(&t!(self.rpn(element), "cvv", "wcel"));
        self.settle(&said, scope, known, 3, None, None)
    }

    /// What the cited lines settle of the property `body`, which binds
    /// `letter`, at `element`: a line saying it or its denial, or the
    /// property read through what the lines say the element is, down to a
    /// membership of a listed set.
    fn settled_at(
        &mut self,
        body: &Term,
        letter: &str,
        element: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Settled>> {
        let at = self.restated(body, &format!("{letter} cv"), &self.rpn(element));
        let said = self.rpn(&at);
        if let Some(p) = self.held(known, &said, scope)? {
            return Ok(Built(Settled::Holds(p)));
        }
        if let Some(p) = self.held(known, &t!(said, "wn"), scope)? {
            return Ok(Built(Settled::Fails(p)));
        }
        if at.label() != Some("wcel") || at.variable().is_some() {
            return Ok(Route::no(format!(
                "nothing cited settles {}",
                self.render(&said)
            )));
        }
        let kids = at.children().to_vec();
        let (member, set) = (&kids[0], &kids[1]);
        let listing = take!(self.listing(set, scope, known)?);
        if let Some(i) = self.position(member, &listing.elements) {
            let inside =
                take!(self.in_union(member, &listing.elements, i, scope, known)?);
            return Ok(Built(Settled::Holds(self.b.ap(
                "eleqtrrd",
                &binds! {"ph" => scope, "A" => &self.rpn(member),
                "B" => &self.union_of(&listing.elements), "C" => &self.rpn(set)},
                &[&inside, &listing.proof],
            ))));
        }
        let outside =
            take!(self.not_in_union(member, &listing.elements, scope, known)?);
        Ok(Built(Settled::Fails(
            self.carried_out(member, set, &listing, outside, scope)?,
        )))
    }

    /// ( scope -> {x ∈ the union of `elements`' singletons : body} = the
    /// union of the kept ones' singletons ), the empty set where none is.
    fn kept(
        &mut self,
        body: &Term,
        letter: &str,
        elements: &[Term],
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Kept>> {
        let p = self.rpn(body);
        let builder = |over: &str| t!(p, letter, over, "crab");
        if elements.len() == 1 {
            let c = self.rpn(&elements[0]);
            let single = t!(c, "csn");
            let at = self.rpn(&self.restated(body, &format!("{letter} cv"), &c));
            let tie = self.to_term(&t!(
                t!(format!("{letter} cv"), c, "wceq"),
                t!(p, at, "wb"),
                "wi"
            ));
            let tie = take!(self.prove_essential(&tie, "", &Facts::new())?);
            let cases = self.b.ap(
                "rabsnif",
                &binds! {"x" => letter, "A" => &c, "ph" => &p, "ps" => &at},
                &[&tie],
            );
            let chosen = t!(at, single, "c0", "cif");
            let (lemma, kept, case, result) = match take!(self.settled_at(
                body,
                letter,
                &elements[0],
                scope,
                known
            )?) {
                Settled::Holds(q) => {
                    ("iftrue", vec![elements[0].clone()], q, single.clone())
                }
                Settled::Fails(q) => ("iffalse", Vec::new(), q, "c0".to_string()),
            };
            let law = self.b.ap(
                lemma,
                &binds! {"ph" => &at, "A" => &single, "B" => "c0"},
                &[],
            );
            let condition = if lemma == "iftrue" {
                at.clone()
            } else {
                t!(at, "wn")
            };
            let picked = self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &condition,
                "ch" => &t!(chosen, result, "wceq")},
                &[&case, &law],
            );
            let proof = self.b.ap(
                "eqtrid",
                &binds! {"ph" => scope, "A" => &builder(&single), "B" => &chosen, "C" => &result},
                &[&cases, &picked],
            );
            return Ok(Built(Kept {
                elements: kept,
                proof,
            }));
        }
        let (init, last) = elements.split_at(elements.len() - 1);
        let (front, back) = (self.union_of(init), self.union_of(last));
        let first = take!(self.kept(body, letter, init, scope, known)?);
        let second = take!(self.kept(body, letter, last, scope, known)?);
        let made_of = |me: &Self, kept: &[Term]| -> String {
            if kept.is_empty() {
                "c0".to_string()
            } else {
                me.union_of(kept)
            }
        };
        let (a, b) = (
            made_of(self, &first.elements),
            made_of(self, &second.elements),
        );
        let split = self.b.ap(
            "rabun2",
            &binds! {"x" => letter, "A" => &front, "B" => &back, "ph" => &p},
            &[],
        );
        let joined = self.b.ap(
            "uneq12d",
            &binds! {"ph" => scope, "A" => &builder(&front), "B" => &a,
            "C" => &builder(&back), "D" => &b},
            &[&first.proof, &second.proof],
        );
        let whole = builder(&t!(front, back, "cun"));
        let halves = t!(builder(&front), builder(&back), "cun");
        let union = t!(a, b, "cun");
        let mut proof = self.b.ap(
            "eqtrid",
            &binds! {"ph" => scope, "A" => &whole, "B" => &halves, "C" => &union},
            &[&split, &joined],
        );
        // An empty part drops out of the union.
        let mut elements = first.elements.clone();
        let tidy = if second.elements.is_empty() {
            Some(("un0", a.clone()))
        } else if first.elements.is_empty() {
            elements = second.elements.clone();
            Some(("0un", b.clone()))
        } else {
            elements.extend(second.elements.iter().cloned());
            None
        };
        if let Some((lemma, left)) = tidy {
            let law = self.b.ap(lemma, &binds! {"A" => &left}, &[]);
            proof = self.b.ap(
                "eqtrdi",
                &binds! {"ph" => scope, "A" => &whole, "B" => &union, "C" => &left},
                &[&proof, &law],
            );
        }
        Ok(Built(Kept { elements, proof }))
    }

    /// {x ∈ S : P(x)} = L: S read as its listing, each element kept or not,
    /// and what is kept compared with L.
    fn set_builder(
        &mut self,
        builder: &Term,
        listed: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = builder.children().to_vec();
        let (body, letter, over) = (&kids[0], self.rpn(&kids[1]), &kids[2]);
        let source = take!(self.listing(over, scope, known)?);
        let target = take!(self.listing(listed, scope, known)?);
        let kept = take!(self.kept(body, &letter, &source.elements, scope, known)?);
        if kept.elements.is_empty() {
            return Ok(Route::no(format!(
                "no element of {} has the property, and the claim lists some",
                self.render(&self.rpn(over))
            )));
        }
        let p = self.rpn(body);
        let (s, u_source) = (self.rpn(over), self.union_of(&source.elements));
        let moved = self.b.ap(
            "rabeqdv",
            &binds! {"ph" => scope, "ps" => &p, "x" => &letter, "A" => &s, "B" => &u_source},
            &[&source.proof],
        );
        let (whole, over_listing) =
            (self.rpn(builder), t!(p, letter, u_source, "crab"));
        let u_kept = self.union_of(&kept.elements);
        let mut reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &whole, "B" => &over_listing, "C" => &u_kept},
            &[&moved, &kept.proof],
        );
        // The claim may list what is kept in any order: the two listings
        // are one set where each is inside the other.
        let u_target = self.union_of(&target.elements);
        if u_kept != u_target {
            let forth = take!(self.listed_within(
                &kept.elements,
                &target.elements,
                scope,
                known
            )?);
            let back = take!(self.listed_within(
                &target.elements,
                &kept.elements,
                scope,
                known
            )?);
            let same = self.b.ap(
                "eqssd",
                &binds! {"ph" => scope, "A" => &u_kept, "B" => &u_target},
                &[&forth, &back],
            );
            reached = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &whole, "B" => &u_kept, "C" => &u_target},
                &[&reached, &same],
            );
        }
        Ok(Built(self.b.ap(
            "eqtr4d",
            &binds! {"ph" => scope, "A" => &whole, "B" => &u_target, "C" => &self.rpn(listed)},
            &[&reached, &target.proof],
        )))
    }

    /// ( scope -> the union of `from`'s singletons ⊆ the union of `into`'s
    /// ), each element of the one being an element of the other.
    fn listed_within(
        &mut self,
        from: &[Term],
        into: &[Term],
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let whole = self.union_of(into);
        if from.len() == 1 {
            let Some(at) = self.position(&from[0], into) else {
                return Ok(Route::no(format!(
                    "{} is kept and the claim does not list it",
                    self.render(&self.rpn(&from[0]))
                )));
            };
            let inside = take!(self.in_union(&from[0], into, at, scope, known)?);
            return Ok(Built(self.b.ap(
                "snssd",
                &binds! {"ph" => scope, "A" => &self.rpn(&from[0]), "B" => &whole},
                &[&inside],
            )));
        }
        let (init, last) = from.split_at(from.len() - 1);
        let front = take!(self.listed_within(init, into, scope, known)?);
        let back = take!(self.listed_within(last, into, scope, known)?);
        Ok(Built(self.b.ap(
            "unssd",
            &binds! {"ph" => scope, "A" => &self.union_of(init), "B" => &self.union_of(last),
            "C" => &whole},
            &[&front, &back],
        )))
    }

    /// |L| = m: one for the first element, and one more for each element
    /// the lines say differs from those before it.
    fn size(
        &mut self,
        set: &Term,
        count: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let listing = take!(self.listing(set, scope, known)?);
        let (counted, sum) = take!(self.counted(&listing.elements, scope, known)?);
        let (s, u) = (self.rpn(set), self.union_of(&listing.elements));
        let moved = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &s, "B" => &u, "F" => "chash"},
            &[&listing.proof],
        );
        let (size_of_set, size_of_union) =
            (t!(s, "chash", "cfv"), t!(u, "chash", "cfv"));
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &size_of_set, "B" => &size_of_union, "C" => &sum},
            &[&moved, &counted],
        );
        let m = self.rpn(count);
        let worked = t!(sum, m, "wceq");
        let what = format!("{} counts {}", self.render(&m), self.render(&s));
        let numeral = self.closed_fact(&worked, scope, known, &what, None)?;
        Ok(Built(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &size_of_set, "B" => &sum, "C" => &m},
            &[&reached, &numeral],
        )))
    }

    /// ( scope -> |the union of `elements`' singletons| = 1 + 1 + … ), and
    /// that sum.
    fn counted(
        &mut self,
        elements: &[Term],
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<(Proof, String)>> {
        let first = self.rpn(&elements[0]);
        if elements.len() == 1 {
            let is_set = take!(self.a_set(&elements[0], scope, known)?);
            let law = self
                .b
                .ap("hashsng", &binds! {"A" => &first, "V" => "cvv"}, &[]);
            let size = t!(t!(first, "csn"), "chash", "cfv");
            return Ok(Built((
                self.b.ap(
                    "syl",
                    &binds! {"ph" => scope, "ps" => &t!(first, "cvv", "wcel"),
                    "ch" => &t!(size, "c1", "wceq")},
                    &[&is_set, &law],
                ),
                "c1".to_string(),
            )));
        }
        let (init, last) = elements.split_at(elements.len() - 1);
        let (before, sum_before) = take!(self.counted(init, scope, known)?);
        let front = self.union_of(init);
        let c = self.rpn(&last[0]);
        let finite = self.finite(init);
        let absent = take!(self.not_in_union(&last[0], init, scope, known)?);
        let in_fin = t!(front, "cfn", "wcel");
        let not_in = t!(t!(c, front, "wcel"), "wn");
        let finite =
            self.b
                .ap("a1i", &binds! {"ph" => &in_fin, "ps" => scope}, &[&finite]);
        let both = self.b.ap(
            "jca",
            &binds! {"ph" => scope, "ps" => &in_fin, "ch" => &not_in},
            &[&finite, &absent],
        );
        let is_set = take!(self.a_set(&last[0], scope, known)?);
        let whole = t!(front, t!(c, "csn"), "cun");
        let size_whole = t!(whole, "chash", "cfv");
        let size_front = t!(front, "chash", "cfv");
        let one_more = t!(size_front, "c1", "caddc", "co");
        let law = self.b.ap(
            "hashunsng",
            &binds! {"A" => &front, "B" => &c, "V" => "cvv"},
            &[],
        );
        let step = self.b.ap(
            "sylc",
            &binds! {"ph" => scope, "ps" => &t!(c, "cvv", "wcel"),
            "ch" => &t!(in_fin, not_in, "wa"), "th" => &t!(size_whole, one_more, "wceq")},
            &[&is_set, &both, &law],
        );
        let sum = t!(sum_before, "c1", "caddc", "co");
        let carried = self.b.ap(
            "oveq1d",
            &binds! {"ph" => scope, "A" => &size_front, "B" => &sum_before, "C" => "c1", "F" => "caddc"},
            &[&before],
        );
        Ok(Built((
            self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &size_whole, "B" => &one_more, "C" => &sum},
                &[&step, &carried],
            ),
            sum,
        )))
    }

    /// |- the union of `elements`' singletons is finite.
    fn finite(&self, elements: &[Term]) -> Proof {
        let first = self.rpn(&elements[0]);
        let mut proof = self.b.ap("snfi", &binds! {"A" => &first}, &[]);
        let mut union = t!(first, "csn");
        for e in &elements[1..] {
            let single = t!(self.rpn(e), "csn");
            let one = self.b.ap("snfi", &binds! {"A" => &self.rpn(e)}, &[]);
            let (left, right) = (t!(union, "cfn", "wcel"), t!(single, "cfn", "wcel"));
            let both = self.b.ap(
                "pm3.2i",
                &binds! {"ph" => &left, "ps" => &right},
                &[&proof, &one],
            );
            let law = self
                .b
                .ap("unfi", &binds! {"A" => &union, "B" => &single}, &[]);
            union = t!(union, single, "cun");
            proof = self.b.ap(
                "ax-mp",
                &binds! {"ph" => &t!(left, right, "wa"), "ps" => &t!(union, "cfn", "wcel")},
                &[&both, &law],
            );
        }
        proof
    }
}
