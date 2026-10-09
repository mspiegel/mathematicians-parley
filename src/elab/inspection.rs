//! `inspection`: a claim about sets listed in full, checked element by
//! element against what the cited lines say (`METHODS.md`). Each side of the
//! claim is worked out to a listing or a count (`value`), and the two are
//! compared.
//!
//! A listed set is read in one standard form, the singletons of its
//! elements joined from the left, `(({a} ∪ {b}) ∪ {c})`, which is how set.mm
//! defines its pair and triple (`df-pr`, `df-tp`). A set the lines give by an
//! equation is read through it. Every proof here is in deduction form under
//! the step's scope.

use super::field::{self, Verdict};
use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules;
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

/// What a term comes to by the cited lines (`value`).
enum Value {
    /// A set, as the elements it lists.
    Set {
        elements: Vec<Term>,
        /// ( scope -> term = the union of the elements' singletons ), the
        /// empty set where there are none.
        proof: Proof,
    },
    /// A number, as the sum of ones that counts it, or a closed numeral.
    Count {
        sum: String,
        /// ( scope -> term = sum ), or None where the term is the sum.
        proof: Option<Proof>,
    },
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

    /// The claim, a membership or an equation, with each side worked out to
    /// what the cited lines make it (`value`) and the two compared.
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
                let listing = take!(self.set_value(set, scope, known)?);
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
                let listing = take!(self.set_value(set, scope, known)?);
                let outside = take!(self.not_in_union(
                    element,
                    &listing.elements,
                    scope,
                    known
                )?);
                self.carried_out(element, set, &listing, outside, scope)
                    .map(Built)
            }
            Some("wceq") => self.equation(&kids[0], &kids[1], scope, known),
            _ => Ok(Route::no(
                "inspection says what is in a listed set, or that two things it \
                 can work out are equal",
            )),
        }
    }

    /// What `term` comes to by what the cited lines say: a set listed, or
    /// given by an equation with a listing; the empty set, listing nothing;
    /// a set-builder over a listed set, the elements its property keeps; the
    /// size of such a set, counted; a term spelt with numerals alone
    /// (`rules::numeric`), itself; or a term a cited "for all" equation over
    /// a listed set gives at one of its elements, the other side worked out.
    fn value(
        &mut self,
        term: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Value>> {
        if let Built(listing) = self.listing(term, scope, known)? {
            return Ok(Built(Value::Set {
                elements: listing.elements,
                proof: listing.proof,
            }));
        }
        let kids = term.children().to_vec();
        if term.variable().is_none() && term.label() == Some("crab") {
            let (body, letter, over) = (&kids[0], self.rpn(&kids[1]), &kids[2]);
            let source = take!(self.listing(over, scope, known)?);
            let kept =
                take!(self.kept(body, &letter, &source.elements, scope, known)?);
            let p = self.rpn(body);
            let (s, u_source) = (self.rpn(over), self.union_of(&source.elements));
            let moved = self.b.ap(
                "rabeqdv",
                &binds! {"ph" => scope, "ps" => &p, "x" => &letter, "A" => &s, "B" => &u_source},
                &[&source.proof],
            );
            let over_listing = t!(p, letter, u_source, "crab");
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &self.rpn(term), "B" => &over_listing,
                "C" => &self.listed(&kept.elements)},
                &[&moved, &kept.proof],
            );
            return Ok(Built(Value::Set {
                elements: kept.elements,
                proof,
            }));
        }
        if term.variable().is_none()
            && term.label() == Some("cfv")
            && self.rpn(&kids[1]) == "chash"
        {
            let set = &kids[0];
            let listing = take!(self.set_value(set, scope, known)?);
            let (s, u) = (self.rpn(set), self.listed(&listing.elements));
            let moved = self.b.ap(
                "fveq2d",
                &binds! {"ph" => scope, "A" => &s, "B" => &u, "F" => "chash"},
                &[&listing.proof],
            );
            let (size_of_set, size_of_union) =
                (t!(s, "chash", "cfv"), t!(u, "chash", "cfv"));
            let (counted, sum) = if listing.elements.is_empty() {
                let none = self.b.ap("hash0", &binds! {}, &[]);
                let none = self.b.ap(
                    "a1i",
                    &binds! {"ph" => &t!(size_of_union, "cc0", "wceq"), "ps" => scope},
                    &[&none],
                );
                (none, "cc0".to_string())
            } else {
                take!(self.counted(&listing.elements, scope, known)?)
            };
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &size_of_set, "B" => &size_of_union, "C" => &sum},
                &[&moved, &counted],
            );
            return Ok(Built(Value::Count {
                sum,
                proof: Some(proof),
            }));
        }
        let said = self.rpn(term);
        if said == "c0" {
            let none = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => "c0"}, &[]);
            return Ok(Built(Value::Set {
                elements: Vec::new(),
                proof: none,
            }));
        }
        if said.split_whitespace().all(rules::numeric) {
            return Ok(Built(Value::Count {
                sum: said,
                proof: None,
            }));
        }
        self.through_all(term, scope, known)
    }

    /// `value` of a term that must come to a listed set.
    fn set_value(
        &mut self,
        term: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Listing>> {
        match take!(self.value(term, scope, known)?) {
            Value::Set { elements, proof } => Ok(Built(Listing { elements, proof })),
            Value::Count { .. } => Ok(Route::no(format!(
                "{} is a number, and a set is wanted",
                self.render(&self.rpn(term))
            ))),
        }
    }

    /// `term` as a cited line "for all x ∈ S, l(x) = r(x)" gives it, where S
    /// is listed and `term` is l at one of its elements: the instance by
    /// `rspcdva`, and r there worked out by `value`.
    fn through_all(
        &mut self,
        term: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Value>> {
        let said = self.rpn(term);
        for (fact, all) in known.entries() {
            let held = self.to_term(&fact);
            if held.variable().is_some() || held.label() != Some("wral") {
                continue;
            }
            let kids = held.children().to_vec();
            let (body, letter, domain) = (&kids[0], self.rpn(&kids[1]), &kids[2]);
            if body.variable().is_some() || body.label() != Some("wceq") {
                continue;
            }
            let sides = body.children().to_vec();
            let bound = format!("{letter} cv");
            let Built(listing) = self.listing(domain, scope, known)? else {
                continue;
            };
            let Some(at) = listing.elements.iter().position(|e| {
                self.rpn(&self.restated(&sides[0], &bound, &self.rpn(e))) == said
            }) else {
                continue;
            };
            let element = listing.elements[at].clone();
            let c = self.rpn(&element);
            let instance = self.restated(body, &bound, &c);
            let other = instance.children()[1].clone();
            let inside =
                take!(self.in_union(&element, &listing.elements, at, scope, known)?);
            let member = self.b.ap(
                "eleqtrrd",
                &binds! {"ph" => scope, "A" => &c,
                "B" => &self.union_of(&listing.elements), "C" => &self.rpn(domain)},
                &[&inside, &listing.proof],
            );
            let (p, at_c) = (self.rpn(body), self.rpn(&instance));
            let tie = self.to_term(&t!(t!(bound, c, "wceq"), t!(p, at_c, "wb"), "wi"));
            let tie = take!(self.prove_essential(&tie, "", &Facts::new())?);
            let given = self.b.ap(
                "rspcdva",
                &binds! {"x" => &letter, "ps" => &p, "ch" => &at_c, "ph" => scope,
                "A" => &self.rpn(domain), "C" => &c},
                &[&tie, &all, &member],
            );
            let worked = take!(self.value(&other, scope, known)?);
            let r = self.rpn(&other);
            let joined = |me: &Self, to: &str, rest: Option<Proof>| -> Proof {
                match rest {
                    None => given.clone(),
                    Some(rest) => me.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => &said, "B" => &r, "C" => to},
                        &[&given, &rest],
                    ),
                }
            };
            return Ok(Built(match worked {
                Value::Set { elements, proof } => {
                    let to = self.listed(&elements);
                    Value::Set {
                        proof: joined(self, &to, Some(proof)),
                        elements,
                    }
                }
                Value::Count { sum, proof } => Value::Count {
                    proof: Some(joined(self, &sum, proof)),
                    sum,
                },
            }));
        }
        Ok(Route::no(format!(
            "nothing cited lists {} or says what it is",
            self.render(&said)
        )))
    }

    /// One side equal to the other: both worked out by `value`, two sets
    /// compared as sets, so their order is never asked, and two numbers by
    /// working out the sum that counts one against the other.
    fn equation(
        &mut self,
        left: &Term,
        right: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let one = take!(self.value(left, scope, known)?);
        let other = take!(self.value(right, scope, known)?);
        let (a, b) = (self.rpn(left), self.rpn(right));
        match (one, other) {
            (
                Value::Set {
                    elements: ea,
                    proof: pa,
                },
                Value::Set {
                    elements: eb,
                    proof: pb,
                },
            ) => {
                let (ua, ub) = (self.listed(&ea), self.listed(&eb));
                let mut reached = pa;
                if ua != ub {
                    let forth = take!(self.listed_within(&ea, &eb, scope, known)?);
                    let back = take!(self.listed_within(&eb, &ea, scope, known)?);
                    let same = self.b.ap(
                        "eqssd",
                        &binds! {"ph" => scope, "A" => &ua, "B" => &ub},
                        &[&forth, &back],
                    );
                    reached = self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => &a, "B" => &ua, "C" => &ub},
                        &[&reached, &same],
                    );
                }
                Ok(Built(self.b.ap(
                    "eqtr4d",
                    &binds! {"ph" => scope, "A" => &a, "B" => &ub, "C" => &b},
                    &[&reached, &pb],
                )))
            }
            (
                Value::Count { sum: sa, proof: pa },
                Value::Count { sum: sb, proof: pb },
            ) => {
                let what = format!("{} is {}", self.render(&a), self.render(&b));
                let worked = if sa == sb {
                    None
                } else {
                    Some(self.closed_fact(
                        &t!(sa, sb, "wceq"),
                        scope,
                        known,
                        &what,
                        None,
                    )?)
                };
                // a = sa, then sa = sb, then sb = b, each where it says
                // something.
                let mut reached: Option<(Proof, String)> = pa.map(|p| (p, sa.clone()));
                if let Some(w) = worked {
                    reached = Some(match reached {
                        None => (w, sb.clone()),
                        Some((p, _)) => (
                            self.b.ap(
                                "eqtrd",
                                &binds! {"ph" => scope, "A" => &a, "B" => &sa, "C" => &sb},
                                &[&p, &w],
                            ),
                            sb.clone(),
                        ),
                    });
                }
                let proof = match (reached, pb) {
                    (Some((p, _)), None) => p,
                    (Some((p, _)), Some(q)) => self.b.ap(
                        "eqtr4d",
                        &binds! {"ph" => scope, "A" => &a, "B" => &sb, "C" => &b},
                        &[&p, &q],
                    ),
                    (None, Some(q)) => self.b.ap(
                        "eqcomd",
                        &binds! {"ph" => scope, "A" => &b, "B" => &a},
                        &[&q],
                    ),
                    (None, None) => {
                        self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &a}, &[])
                    }
                };
                Ok(Built(proof))
            }
            _ => Ok(Route::no(format!(
                "one of {} and {} is a set and the other a number",
                self.render(&a),
                self.render(&b)
            ))),
        }
    }

    /// The union of the singletons of `elements`, or the empty set where
    /// there are none.
    fn listed(&self, elements: &[Term]) -> String {
        if elements.is_empty() {
            "c0".to_string()
        } else {
            self.union_of(elements)
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
            self.listed(&listing.elements),
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
        if elements.is_empty() {
            let none = self.b.ap("noel", &binds! {"A" => &t}, &[]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => &t!(t!(t, "c0", "wcel"), "wn"), "ps" => scope},
                &[&none],
            )));
        }
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
        if let Some(settled) = self.decided_at_value(&at, scope, known)? {
            return Ok(Built(settled));
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

    /// A word `at` says, settled at the values the cited lines give its
    /// terms, where its record names `inspection` in its `decided` field
    /// (`METHODS.md`, inspection): "deg(A) is odd" from "deg(A) = 5", decided
    /// at 5 as `arithmetic` decides it and carried back by the equation
    /// (`breq12d`). None where the word is not such a one, or a term has no
    /// such value.
    fn decided_at_value(
        &mut self,
        at: &Term,
        scope: &str,
        known: &Facts,
    ) -> Checked<Option<Settled>> {
        let negated = at.label() == Some("wn") && at.children().len() == 1;
        let core = if negated {
            at.children()[0].clone()
        } else {
            at.clone()
        };
        if core.variable().is_some()
            || core.label() != Some("wbr")
            || core.children().len() != 3
            || core.children()[2].label() != Some("cdvds")
            || !self.decided_by("inspection", at)?
        {
            return Ok(None);
        }
        // Each side, and ( scope -> side = its value ).
        let mut sides: Vec<(String, String, Proof)> = Vec::new();
        for side in &core.children()[..2] {
            let written = self.rpn(side);
            if written.split_whitespace().all(rules::numeric) {
                let same =
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &written}, &[]);
                sides.push((written.clone(), written, same));
                continue;
            }
            let Some((value, proof)) = self.cited_value(&written, scope, known)? else {
                return Ok(None);
            };
            sides.push((written, value, proof));
        }
        let at_values = t!(sides[0].1, sides[1].1, "cdvds", "wbr");
        let Built(Verdict::Holds(holds)) =
            field::decide_closed(&self.to_term(&at_values))
        else {
            return Ok(None);
        };
        let Built(shown) =
            self.numeral_divides(&self.to_term(&at_values), !holds, scope)
        else {
            return Ok(None);
        };
        let written = self.rpn(&core);
        let mut same = self.b.ap(
            "breq12d",
            &binds! {"ph" => scope, "A" => &sides[0].0, "B" => &sides[0].1,
            "C" => &sides[1].0, "D" => &sides[1].1, "R" => "cdvds"},
            &[&sides[0].2, &sides[1].2],
        );
        let (claim, value_claim) = if holds {
            (written.clone(), at_values.clone())
        } else {
            same = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => &written, "ch" => &at_values},
                &[&same],
            );
            (t!(written, "wn"), t!(at_values, "wn"))
        };
        let proved = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &claim, "ch" => &value_claim},
            &[&shown, &same],
        );
        // `proved` says the divisibility or its denial; `at` is one of the two.
        Ok(Some(match (negated, holds) {
            (false, true) | (true, false) => Settled::Holds(proved),
            (false, false) => Settled::Fails(proved),
            (true, true) => Settled::Fails(self.b.ap(
                "notnotd",
                &binds! {"ph" => scope, "ps" => &written},
                &[&proved],
            )),
        }))
    }

    /// The value of numerals alone a cited equation gives `side`, and
    /// ( scope -> side = value ), the equation turned where it is written
    /// the other way round. None where no cited line gives one.
    fn cited_value(
        &mut self,
        side: &str,
        scope: &str,
        known: &Facts,
    ) -> Checked<Option<(String, Proof)>> {
        let numeric = |x: &str| x.split_whitespace().all(rules::numeric);
        for claim in known.keys() {
            let said = self.to_term(&claim);
            if said.variable().is_some()
                || said.label() != Some("wceq")
                || said.children().len() != 2
            {
                continue;
            }
            let (l, r) = (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
            let (value, turned) = if l == side && numeric(&r) {
                (r, false)
            } else if r == side && numeric(&l) {
                (l, true)
            } else {
                continue;
            };
            let Some(proof) = self.held(known, &claim, scope)? else {
                continue;
            };
            if !turned {
                return Ok(Some((value, proof)));
            }
            let back = self.b.ap(
                "eqcomd",
                &binds! {"ph" => scope, "A" => &value, "B" => side},
                &[&proof],
            );
            return Ok(Some((value, back)));
        }
        Ok(None)
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

    /// ( scope -> the union of `from`'s singletons ⊆ the union of `into`'s
    /// ), each element of the one being an element of the other.
    fn listed_within(
        &mut self,
        from: &[Term],
        into: &[Term],
        scope: &str,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let whole = self.listed(into);
        if from.is_empty() {
            let law = self.b.ap("0ss", &binds! {"A" => &whole}, &[]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => &t!("c0", whole, "wss"), "ps" => scope},
                &[&law],
            )));
        }
        if from.len() == 1 {
            let Some(at) = self.position(&from[0], into) else {
                return Ok(Route::no(format!(
                    "{} is on one side and not the other",
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

    /// ( scope -> |the union of `elements`' singletons| = 1 + 1 + … ), and
    /// that sum: one for the first element, and one more for each element
    /// the lines say differs from those before it.
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
