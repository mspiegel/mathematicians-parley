//! `inspection`: a claim about sets listed in full, checked element by
//! element against what the cited lines say (`METHODS.md`). Each side of the
//! claim is worked out to a listing or a count (`value`), and the two are
//! compared.
//!
//! A listed set is read in one standard form, the singletons of its
//! elements joined from the left, `(({a} ∪ {b}) ∪ {c})`, which is how set.mm
//! defines its pair and triple (`df-pr`, `df-tp`), and a range of numerals
//! is read in the same form, its numerals in order. A set the lines give by
//! an equation is read through it. A line of "or"s is read against a cited
//! membership, as the listing of the set it names (`one_of`). Every proof
//! here is in deduction form under the step's scope.

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use super::field::{self, Verdict};
use super::numerals;
use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::methods::inspection::{disjuncts, integer_value, range_elements};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules;
use crate::{pf, t, take};

/// A set read in the standard form: its elements in order, and a proof
/// that the set is the union of their singletons.
struct Listing {
    elements: Vec<Term>,
    /// ( scope -> set = the union of the elements' singletons ).
    proof: Proof,
}

/// The sentences a line joins with "and", however it groups them.
fn conjuncts(line: &Term) -> Vec<Term> {
    if line.variable().is_some() {
        return vec![line.clone()];
    }
    match line.label() {
        Some("wa" | "w3a") => line.children().iter().flat_map(conjuncts).collect(),
        _ => vec![line.clone()],
    }
}

/// The least factor of n above 1, n itself where n is prime; n at least 2.
fn least_factor(n: &BigUint) -> BigUint {
    let mut d = BigUint::from(2u32);
    while &d * &d <= *n {
        if (n % &d) == BigUint::ZERO {
            return d;
        }
        d += 1u32;
    }
    n.clone()
}

/// Whether n is prime.
fn is_prime(n: &BigUint) -> bool {
    *n >= BigUint::from(2u32) && least_factor(n) == *n
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

/// A cited line `t ∈ S` that a line of "or"s is read against, and what each
/// of that line's equations says t is.
struct Member {
    element: Term,
    set: Term,
    /// ( scope -> t ∈ S ).
    proof: Proof,
    /// One for each equation of the line, in its order.
    named: Vec<Named>,
}

/// What one equation of a line of "or"s says t is.
struct Named {
    /// The equation's other side.
    is: Term,
    /// Whether the equation is written `s = t`, t on the right.
    turned: bool,
}

/// The cited membership a line of equations is read against
/// (`listed_membership`).
struct Membership {
    /// The cited `t ∈ S`.
    said: Term,
    /// One for each equation of the line, in its order.
    named: Vec<Named>,
    /// S, listed.
    listing: Listing,
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
        sum: Rpn,
        /// ( scope -> term = sum ), or None where the term is the sum.
        proof: Option<Proof>,
    },
}

impl Elaborator<'_> {
    /// The step's claim, by inspection of the sets the cited lines list.
    pub fn inspection(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
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
        let lines: Vec<Rpn> = step
            .just
            .refs
            .iter()
            .filter_map(|r| self.lines.get(r).map(|l| l.term.clone()))
            .collect();
        let made = self.inspected(&claim, scope, &known, &lines)?;
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
    /// what the cited lines make it (`value`) and the two compared; or a
    /// line of "or"s read against a membership `lines`, the cited lines,
    /// say (`one_of`).
    fn inspected(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        known: &Facts,
        lines: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let kids = claim.children().to_vec();
        // "n is prime", a word whose record names inspection in `decided`.
        let of_primes = |t: &Term| {
            t.variable().is_none()
                && t.label() == Some("wcel")
                && t.children().get(1).and_then(Term::label) == Some("cprime")
        };
        if of_primes(claim) || (claim.label() == Some("wn") && of_primes(&kids[0])) {
            let negated = !of_primes(claim);
            let element = if negated {
                kids[0].children()[0].clone()
            } else {
                kids[0].clone()
            };
            if self.decided_by("inspection", claim)? {
                return self.prime_decided(&element, negated, scope, known);
            }
        }
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
            // A line of equations joined by "or", or one equation alone, is
            // read against a cited membership in a listed set where there is
            // one, and an equation is otherwise read as an equation.
            Some("wceq" | "wo") if claim.variable().is_none() => {
                match self.listed_membership(claim, scope, known, lines)? {
                    Some(found) => self.one_of(claim, found, scope, known),
                    None if claim.label() == Some("wceq") => {
                        self.equation(&kids[0], &kids[1], scope, known)
                    }
                    None => Ok(Route::no(
                        "nothing cited puts in a listed set the one term every equation of the claim names",
                    )),
                }
            }
            _ => Ok(Route::no(
                "inspection says what is in a listed set, that two things it \
                 can work out are equal, or which element of a listed set a \
                 thing in it is",
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
        scope: &Rpn,
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
            let (s, u_source) = (self.rpn(over), self.listed(&source.elements));
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
            && self.rpn(&kids[1]).alone() == Some("chash")
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
                (none, t!("cc0"))
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
        if said.alone() == Some("c0") {
            let none = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => "c0"}, &[]);
            return Ok(Built(Value::Set {
                elements: Vec::new(),
                proof: none,
            }));
        }
        if said.tokens().iter().all(|t| rules::numeric(t.as_str())) {
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
        scope: &Rpn,
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
        scope: &Rpn,
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
            let bound = t!(letter, "cv");
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
            let tie =
                take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
            let given = self.b.ap(
                "rspcdva",
                &binds! {"x" => &letter, "ps" => &p, "ch" => &at_c, "ph" => scope,
                "A" => &self.rpn(domain), "C" => &c},
                &[&tie, &all, &member],
            );
            let worked = take!(self.value(&other, scope, known)?);
            let r = self.rpn(&other);
            let joined = |me: &Self, to: &Rpn, rest: Option<Proof>| -> Proof {
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
        scope: &Rpn,
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
                let mut reached: Option<(Proof, Rpn)> = pa.map(|p| (p, sa.clone()));
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

    /// The cited `t ∈ S` a line of equations joined by "or", or one equation
    /// alone, is read against, as the checker reads it: the first whose t
    /// is one side of every equation and whose S comes to a listed set
    /// (`set_value`). None where nothing cited does.
    fn listed_membership(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        known: &Facts,
        lines: &[Rpn],
    ) -> Checked<Option<Membership>> {
        let sentences = disjuncts(claim);
        let cited: Vec<Term> = lines
            .iter()
            .flat_map(|l| conjuncts(&self.to_term(l)))
            .collect();
        for said in cited {
            if said.variable().is_some() || said.label() != Some("wcel") {
                continue;
            }
            let element = &said.children()[0];
            let named: Option<Vec<Named>> =
                sentences.iter().map(|s| self.says_of(s, element)).collect();
            let Some(named) = named else {
                continue;
            };
            let set = said.children()[1].clone();
            if let Built(listing) = self.set_value(&set, scope, known)? {
                return Ok(Some(Membership {
                    said,
                    named,
                    listing,
                }));
            }
        }
        Ok(None)
    }

    /// A line of "or"s, `t = s₁ or … or t = sₙ`, or one equation `t = s`,
    /// from the cited line `t ∈ S` that `listed_membership` finds, S being a set
    /// the cited lines list (`METHODS.md`, inspection): an equation for each
    /// element and for nothing else, in any order, each written `t = s` or
    /// `s = t`, s the element or a term of numerals alone of its value. t is
    /// in the union of the elements' singletons (`eleqtrd`), the line
    /// follows from each singleton (`singleton_into`), and the singletons
    /// are joined from the left as the union is (`elun`, `jaod`).
    fn one_of(
        &mut self,
        claim: &Term,
        found: Membership,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let sentences = disjuncts(claim);
        let Membership {
            said,
            named,
            listing,
        } = found;
        let element = said.children()[0].clone();
        let Some(proof) = self.held(known, &self.rpn(&said), scope)? else {
            return Ok(Route::no(format!(
                "{} is cited and not held",
                self.render(&self.rpn(&said))
            )));
        };
        let member = Member {
            set: said.children()[1].clone(),
            element,
            proof,
            named,
        };
        let elements = listing.elements.clone();
        if let Some(stray) = member
            .named
            .iter()
            .find(|n| !elements.iter().any(|e| self.one_value(&n.is, e)))
        {
            return Ok(Route::no(format!(
                "{} is not an element of {}",
                self.render(&self.rpn(&stray.is)),
                self.render(&self.rpn(&member.set))
            )));
        }
        let t = self.rpn(&member.element);
        let line = self.rpn(claim);
        // ( scope -> ( t ∈ the first k singletons' union -> line ) ).
        let mut joined: Option<Proof> = None;
        for (k, s) in elements.iter().enumerate() {
            let Some(at) = member.named.iter().position(|n| self.one_value(s, &n.is))
            else {
                return Ok(Route::no(format!(
                    "the claim leaves out {}, an element of {}",
                    self.render(&self.rpn(s)),
                    self.render(&self.rpn(&member.set))
                )));
            };
            let from_one =
                self.singleton_into(&member, s, at, &sentences, claim, scope, known)?;
            joined = Some(match joined {
                None => from_one,
                Some(before) => {
                    let front = self.union_of(&elements[..k]);
                    let single = t!(self.rpn(s), "csn");
                    let (in_front, in_single) =
                        (t!(t, front, "wcel"), t!(t, single, "wcel"));
                    let either = self.b.ap(
                        "jaod",
                        &binds! {"ph" => scope, "ps" => &in_front, "ch" => &line,
                        "th" => &in_single},
                        &[&before, &from_one],
                    );
                    let split = self.b.ap(
                        "elun",
                        &binds! {"A" => &t, "B" => &front, "C" => &single},
                        &[],
                    );
                    self.b.ap(
                        "biimtrid",
                        &binds! {"ph" => &t!(t, t!(front, single, "cun"), "wcel"),
                        "ps" => &t!(in_front, in_single, "wo"), "ch" => scope, "th" => &line},
                        &[&split, &either],
                    )
                }
            });
        }
        let Some(joined) = joined else {
            return Ok(Route::no(format!(
                "{} lists nothing",
                self.render(&self.rpn(&member.set))
            )));
        };
        let union = self.union_of(&elements);
        let inside = self.b.ap(
            "eleqtrd",
            &binds! {"ph" => scope, "A" => &t, "B" => &self.rpn(&member.set), "C" => &union},
            &[&member.proof, &listing.proof],
        );
        Ok(Built(self.b.ap(
            "mpd",
            &binds! {"ph" => scope, "ps" => &t!(t, union, "wcel"), "ch" => &line},
            &[&inside, &joined],
        )))
    }

    /// ( scope -> ( t ∈ { s } -> line ) ), the line's equation at `at` naming
    /// s: t is s (`elsni`), so t is what that equation writes for s, a term
    /// of numerals alone of its value turned to (`eqeq2d`) and the equation
    /// turned round where it is written `s = t` (`eqcom`), and the line holds
    /// where one of its equations does (`widened`).
    #[allow(clippy::too_many_arguments)]
    fn singleton_into(
        &mut self,
        member: &Member,
        s: &Term,
        at: usize,
        sentences: &[Term],
        claim: &Term,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Proof> {
        let (t, sv, line) = (self.rpn(&member.element), self.rpn(s), self.rpn(claim));
        let in_single = t!(t, t!(sv, "csn"), "wcel");
        let is_s = t!(t, sv, "wceq");
        let named = &member.named[at];
        let c = self.rpn(&named.is);
        let mut reached = self.b.ap(
            "a1i",
            &binds! {"ph" => &t!(in_single, is_s, "wi"), "ps" => scope},
            &[&self.b.ap("elsni", &binds! {"A" => &t, "B" => &sv}, &[])],
        );
        // ( scope -> ( t = s <-> now ) ), now the equation as the line writes it.
        let mut same: Option<Proof> = None;
        let mut now = is_s.clone();
        if c != sv {
            let what = format!(
                "inspection takes {} for {}",
                self.render(&c),
                self.render(&sv)
            );
            let valued =
                self.closed_fact(&t!(sv, c, "wceq"), scope, known, &what, None)?;
            same = Some(self.b.ap(
                "eqeq2d",
                &binds! {"ph" => scope, "A" => &sv, "B" => &c, "C" => &t},
                &[&valued],
            ));
            now = t!(t, c, "wceq");
        }
        if named.turned {
            let flip = self.b.ap("eqcom", &binds! {"A" => &t, "B" => &c}, &[]);
            let turned = t!(c, t, "wceq");
            same = Some(match same {
                None => self.b.ap(
                    "a1i",
                    &binds! {"ph" => &t!(now, turned, "wb"), "ps" => scope},
                    &[&flip],
                ),
                Some(p) => self.b.ap(
                    "bitrdi",
                    &binds! {"ph" => scope, "ps" => &is_s, "ch" => &now, "th" => &turned},
                    &[&p, &flip],
                ),
            });
            now = turned;
        }
        if let Some(same) = same {
            reached = self.b.ap(
                "sylibd",
                &binds! {"ph" => scope, "ps" => &in_single, "ch" => &is_s, "th" => &now},
                &[&reached, &same],
            );
        }
        let into = self.widened(at, sentences, claim);
        let into = self.b.ap(
            "a1i",
            &binds! {"ph" => &t!(now, line, "wi"), "ps" => scope},
            &[&into],
        );
        Ok(self.b.ap(
            "syld",
            &binds! {"ph" => scope, "ps" => &in_single, "ch" => &now, "th" => &line},
            &[&reached, &into],
        ))
    }

    /// |- ( the line's sentence at `at` -> line ): the sentence itself
    /// (`id`), or the part of an "or" that holds it, widened by `orc` where
    /// it is the left part and `olc` where it is the right.
    fn widened(&self, at: usize, sentences: &[Term], line: &Term) -> Proof {
        let (said, whole) = (self.rpn(&sentences[at]), self.rpn(line));
        let kids = line.children();
        if line.variable().is_some() || line.label() != Some("wo") || kids.len() != 2 {
            return self.b.ap("id", &binds! {"ph" => &whole}, &[]);
        }
        let (left, right) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
        let on_left = disjuncts(&kids[0]).len();
        let (inner, law, part) = if at < on_left {
            (
                self.widened(at, &sentences[..on_left], &kids[0]),
                self.b
                    .ap("orc", &binds! {"ph" => &left, "ps" => &right}, &[]),
                left,
            )
        } else {
            (
                self.widened(at - on_left, &sentences[on_left..], &kids[1]),
                self.b
                    .ap("olc", &binds! {"ph" => &right, "ps" => &left}, &[]),
                right,
            )
        };
        self.b.ap(
            "syl",
            &binds! {"ph" => &said, "ps" => &part, "ch" => &whole},
            &[&inner, &law],
        )
    }

    /// What an equation says `t` is, where t is one of its sides as written.
    fn says_of(&self, sentence: &Term, t: &Term) -> Option<Named> {
        if sentence.variable().is_some() || sentence.label() != Some("wceq") {
            return None;
        }
        let (a, b) = (&sentence.children()[0], &sentence.children()[1]);
        let at = self.rpn(t);
        if self.rpn(a) == at {
            return Some(Named {
                is: b.clone(),
                turned: false,
            });
        }
        (self.rpn(b) == at).then(|| Named {
            is: a.clone(),
            turned: true,
        })
    }

    /// Whether two elements are one: the same term, or two terms of
    /// numerals alone of one value.
    fn one_value(&self, a: &Term, b: &Term) -> bool {
        if self.rpn(a) == self.rpn(b) {
            return true;
        }
        matches!(
            (field::closed_value(a), field::closed_value(b)),
            (Built(field::Value::Exact(x)), Built(field::Value::Exact(y))) if x == y
        )
    }

    /// The union of the singletons of `elements`, or the empty set where
    /// there are none.
    fn listed(&self, elements: &[Term]) -> Rpn {
        if elements.is_empty() {
            t!("c0")
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
        scope: &Rpn,
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
    fn union_of(&self, elements: &[Term]) -> Rpn {
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
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Listing>> {
        if let Some((elements, closed)) = self.written_listing(set)? {
            let union = self.listed(&elements);
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
            let Some((elements, closed)) = self.written_listing(&other)? else {
                continue;
            };
            let union = self.listed(&elements);
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
    fn written_listing(&mut self, set: &Term) -> Checked<Option<(Vec<Term>, Proof)>> {
        if set.variable().is_some() {
            return Ok(None);
        }
        let kids = set.children().to_vec();
        let Some(label) = set.label() else {
            return Ok(None);
        };
        Ok(match label {
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
                let Some((mut elements, inner)) = self.written_listing(&kids[0])?
                else {
                    return Ok(None);
                };
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
            "co" if kids.len() == 3 && kids[2].label() == Some("cfz") => {
                return self.range_listing(set);
            }
            _ => None,
        })
    }

    /// A range `{a, …, b}` whose ends work out to integers, as the integers
    /// from a to b, and the closed proof that it is the union of their
    /// singletons, or the empty set where b is below a: the ends worked out
    /// (`range_end`, carried in by `oveq12i`) where they are not spelt so
    /// already, and the range built up an integer at a time
    /// (`integer_range`, `empty_range`). None for an end that is no
    /// integer, or a range longer than `RANGE_LISTED`, which the checker
    /// refuses.
    fn range_listing(&mut self, set: &Term) -> Checked<Option<(Vec<Term>, Proof)>> {
        let kids = set.children().to_vec();
        let Some((from, from_is)) = self.range_end(&kids[0])? else {
            return Ok(None);
        };
        let Some((to, to_is)) = self.range_end(&kids[1])? else {
            return Ok(None);
        };
        let Some(elements) = range_elements(&from, &to) else {
            return Ok(None);
        };
        let (sf, st) = (numerals::spell_integer(&from), numerals::spell_integer(&to));
        let of_numerals = t!(sf, st, "cfz", "co");
        let (union, listed) = if elements.is_empty() {
            (t!("c0"), self.empty_range(&from, &to)?)
        } else {
            (singletons(&from, &to), self.integer_range(&from, &to)?)
        };
        let written = self.rpn(set);
        if written == of_numerals {
            return Ok(Some((elements, listed)));
        }
        let ends = self.b.ap(
            "oveq12i",
            &binds! {"A" => self.rpn(&kids[0]), "B" => &sf,
            "C" => self.rpn(&kids[1]), "D" => &st, "F" => "cfz"},
            &[&from_is, &to_is],
        );
        Ok(Some((
            elements,
            self.b.ap(
                "eqtri",
                &binds! {"A" => &written, "B" => &of_numerals, "C" => &union},
                &[&ends, &listed],
            ),
        )))
    }

    /// A range's end, the integer it works out to as the checker reads it
    /// (`integer_value`), and |- end = that integer: `eqid` where the end is
    /// spelt so, and otherwise the equation proved as `arithmetic` proves one
    /// of numerals (`closed`). None for an end that is no integer.
    fn range_end(&mut self, end: &Term) -> Checked<Option<(BigInt, Proof)>> {
        let Some(value) = integer_value(end) else {
            return Ok(None);
        };
        let said = self.rpn(end);
        let spelt = numerals::spell_integer(&value);
        if said == spelt {
            let same = self.b.ap("eqid", &binds! {"A" => &said}, &[]);
            return Ok(Some((value, same)));
        }
        let what = format!("a range ends at {}", self.render(&said));
        let p = self.closed(&t!(&said, &spelt, "wceq"), &what)?;
        Ok(Some((value, p)))
    }

    /// |- claim, a closed fact of numerals proved as `arithmetic` proves one
    /// (`closed_fact`), under truth and taken out of it (`mptru`).
    fn closed(&mut self, claim: &Rpn, what: &str) -> Checked<Proof> {
        let p = self.closed_fact(claim, &t!("wtru"), &Facts::new(), what, None)?;
        Ok(pf!(self.b; claim, p, "mptru"))
    }

    /// |- ( from ... to ) = the singletons of the integers from `from` to
    /// `to`, joined from the left (`singletons`), for `from` at most `to`: the
    /// range of one integer is its singleton (`fzsn`), and a longer one is
    /// the range below its top joined with the top's singleton (`fzsuc`), the
    /// top spelt as one less, plus one, and worked out. What each step asks
    /// of the integers, that each is one, their order and the sum, is a
    /// closed fact of numerals (`closed`).
    fn integer_range(&mut self, from: &BigInt, to: &BigInt) -> Checked<Proof> {
        let (sf, st) = (numerals::spell_integer(from), numerals::spell_integer(to));
        let what = "a range is listed";
        let range_to = |top: &Rpn| t!(&sf, top, "cfz", "co");
        if to == from {
            let integer = self.closed(&t!(&sf, "cz", "wcel"), what)?;
            return Ok(self.b.ap(
                "ax-mp",
                &binds! {
                    "ph" => t!(&sf, "cz", "wcel"),
                    "ps" => t!(range_to(&sf), t!(&sf, "csn"), "wceq"),
                },
                &[&integer, &self.b.ap("fzsn", &binds! {"M" => &sf}, &[])],
            ));
        }
        let less = to - 1u32;
        let sl = numerals::spell_integer(&less);
        let next = t!(&sl, "c1", "caddc", "co");
        let split = t!(range_to(&sl), t!(&next, "csn"), "cun");
        let law = self.b.ap("fzsuc", &binds! {"M" => &sf, "N" => &sl}, &[]);
        // less e. ( ZZ>= ` from ): both integers, and from ≤ less (`eluz2`).
        let upper = t!(&sl, t!(&sf, "cuz", "cfv"), "wcel");
        let (from_z, less_z) = (
            self.closed(&t!(&sf, "cz", "wcel"), what)?,
            self.closed(&t!(&sl, "cz", "wcel"), what)?,
        );
        let ordered = self.closed(&t!(&sf, &sl, "cle", "wbr"), what)?;
        let reaches = self.b.ap(
            "mpbir3an",
            &binds! {
                "ph" => &upper, "ps" => t!(&sf, "cz", "wcel"), "ch" => t!(&sl, "cz", "wcel"),
                "th" => t!(&sf, &sl, "cle", "wbr"),
            },
            &[
                &from_z,
                &less_z,
                &ordered,
                &self.b.ap("eluz2", &binds! {"M" => &sf, "N" => &sl}, &[]),
            ],
        );
        // ( from ... ( less + 1 ) ) = ( ( from ... less ) u. { ( less + 1 ) } )
        let step = self.b.ap(
            "ax-mp",
            &binds! {"ph" => &upper, "ps" => t!(range_to(&next), &split, "wceq")},
            &[&reaches, &law],
        );
        let added = self.closed(&t!(&next, &st, "wceq"), what)?;
        let ends = self.b.ap(
            "oveq2i",
            &binds! {"A" => &next, "B" => &st, "C" => &sf, "F" => "cfz"},
            &[&added],
        );
        let peeled = self.b.ap(
            "eqtr3i",
            &binds! {"A" => range_to(&next), "B" => range_to(&st), "C" => &split},
            &[&ends, &step],
        );
        let below = singletons(from, &less);
        let top = self
            .b
            .ap("sneqi", &binds! {"A" => &next, "B" => &st}, &[&added]);
        let lower = self.integer_range(from, &less)?;
        let joined = self.b.ap(
            "uneq12i",
            &binds! {
                "A" => range_to(&sl), "B" => &below,
                "C" => t!(&next, "csn"), "D" => t!(&st, "csn"),
            },
            &[&lower, &top],
        );
        let split_listed = t!(&below, t!(&st, "csn"), "cun");
        let first = self.b.ap(
            "eqtri",
            &binds! {"A" => range_to(&st), "B" => &split, "C" => &split_listed},
            &[&peeled, &joined],
        );
        Ok(first)
    }

    /// |- ( from ... to ) = (/), for `to` below `from` (`fzn`), each an
    /// integer and their order closed facts of numerals (`closed`).
    fn empty_range(&mut self, from: &BigInt, to: &BigInt) -> Checked<Proof> {
        let (sf, st) = (numerals::spell_integer(from), numerals::spell_integer(to));
        let what = "a range is listed";
        let below = t!(&st, &sf, "clt", "wbr");
        let empty = t!(t!(&sf, &st, "cfz", "co"), "c0", "wceq");
        let from_z = self.closed(&t!(&sf, "cz", "wcel"), what)?;
        let to_z = self.closed(&t!(&st, "cz", "wcel"), what)?;
        let law = self.b.ap(
            "mp2an",
            &binds! {
                "ph" => t!(&sf, "cz", "wcel"), "ps" => t!(&st, "cz", "wcel"),
                "ch" => t!(&below, &empty, "wb"),
            },
            &[
                &from_z,
                &to_z,
                &self.b.ap("fzn", &binds! {"M" => &sf, "N" => &st}, &[]),
            ],
        );
        let ordered = self.closed(&below, what)?;
        Ok(self.b.ap(
            "mpbi",
            &binds! {"ph" => &below, "ps" => &empty},
            &[&ordered, &law],
        ))
    }

    /// ( scope -> t ∈ the union of `elements`' singletons ), t being the
    /// element at `at`.
    fn in_union(
        &mut self,
        element: &Term,
        elements: &[Term],
        at: usize,
        scope: &Rpn,
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
        scope: &Rpn,
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

    /// ( scope -> t ≠ c ): two numerals by their values, as `arithmetic`
    /// decides it, since a numeral is a value and not a name; anything else
    /// from a cited line saying the two differ, either way round.
    fn differs(
        &mut self,
        one: &Term,
        other: &Term,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let (a, b) = (self.rpn(one), self.rpn(other));
        let valued =
            |t: &Term| matches!(field::closed_value(t), Built(field::Value::Exact(_)));
        if valued(one) && valued(other) {
            let apart = take!(self.prove_numeral(
                &t!(t!(&a, &b, "wceq"), "wn"),
                scope,
                known
            )?);
            let law = self.b.ap("df-ne", &binds! {"A" => &a, "B" => &b}, &[]);
            return Ok(Built(self.b.ap(
                "sylibr",
                &binds! {"ph" => scope, "ps" => &t!(t!(&a, &b, "wceq"), "wn"),
                "ch" => &t!(&a, &b, "wne")},
                &[&apart, &law],
            )));
        }
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
        scope: &Rpn,
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
        letter: &Rpn,
        element: &Term,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Settled>> {
        let at = self.restated(body, &t!(letter, "cv"), &self.rpn(element));
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
        scope: &Rpn,
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
        let mut sides: Vec<(Rpn, Rpn, Proof)> = Vec::new();
        for side in &core.children()[..2] {
            let written = self.rpn(side);
            if written.tokens().iter().all(|t| rules::numeric(t.as_str())) {
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
            self.divides_proved(&self.to_term(&at_values), !holds, scope, known)?
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

    /// ( scope -> t is prime ), or its denial where `negated`, for a term
    /// that is a number spelt in numerals or that a cited line gives such a
    /// value (`METHODS.md`, inspection): a prime below 841 by trial division
    /// by the primes up to 23 (`prmlem1`, `prmlem2`), and a number that is
    /// not by its least factor (`nprmi`), each at the value and carried back
    /// to the term as written (`eleq1i`, `eleq1d`). A decline where what is
    /// asked is not what the number is, or the number is 841 or more, past
    /// what trial division by 23 settles.
    pub(super) fn prime_decided(
        &mut self,
        element: &Term,
        negated: bool,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let written = self.rpn(element);
        // The value, and the equation from the term to it: closed where the
        // term is numerals, under the scope where a cited line gives it.
        let (value, closed_equal, cited_equal) =
            match numerals::worked(&self.b, element, &labels) {
                Some((value, is)) => (value, Some(is), None),
                None => {
                    let Some((said, is)) = self.cited_value(&written, scope, known)?
                    else {
                        return Ok(Route::no(format!(
                            "{} is not a number the cited lines give a value",
                            self.render(&written)
                        )));
                    };
                    let Some(value) = numerals::value(&self.to_term(&said)) else {
                        return Ok(Route::no(format!(
                            "{} is not a whole number",
                            self.render(&said)
                        )));
                    };
                    (value, None, Some(is))
                }
            };
        let prime = is_prime(&value);
        if prime == negated {
            return Ok(Route::no(format!(
                "{value} is {}prime",
                if prime { "" } else { "not " }
            )));
        }
        let Some(shown) = self.primality(&value) else {
            return Ok(Route::no(format!(
                "inspection settles whether a number below 841 is prime, by trial division by the primes up to 23, and {value} is not below 841"
            )));
        };
        let spelt = numerals::spell(value.clone());
        let said = |t: Rpn| if negated { t!(t, "wn") } else { t };
        let (claim, at_value) = (
            said(t!(&written, "cprime", "wcel")),
            said(t!(&spelt, "cprime", "wcel")),
        );
        if let Some(is) = closed_equal {
            let closed = if claim == at_value {
                shown
            } else {
                let mut same = self.b.ap(
                    "eleq1i",
                    &binds! {"A" => &written, "B" => &spelt, "C" => "cprime"},
                    &[&is],
                );
                if negated {
                    same = self.b.ap(
                        "notbii",
                        &binds! {"ph" => t!(&written, "cprime", "wcel"),
                        "ps" => t!(&spelt, "cprime", "wcel")},
                        &[&same],
                    );
                }
                self.b.ap(
                    "mpbir",
                    &binds! {"ph" => &claim, "ps" => &at_value},
                    &[&shown, &same],
                )
            };
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => &claim, "ps" => scope},
                &[&closed],
            )));
        }
        let is = cited_equal.expect("the value a cited line gives");
        let mut same = self.b.ap(
            "eleq1d",
            &binds! {"ph" => scope, "A" => &written, "B" => &spelt, "C" => "cprime"},
            &[&is],
        );
        if negated {
            same = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => t!(&written, "cprime", "wcel"),
                "ch" => t!(&spelt, "cprime", "wcel")},
                &[&same],
            );
        }
        let held =
            self.b
                .ap("a1i", &binds! {"ph" => &at_value, "ps" => scope}, &[&shown]);
        Ok(Built(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &claim, "ch" => &at_value},
            &[&held, &same],
        )))
    }

    /// |- n e. Prime for a prime below 841, and |- -. n e. Prime for a
    /// number that is not prime: 2 and 3 by name, a prime below 25 by its
    /// not being even or a multiple of 3 (`prmlem1`), one below 841 by its
    /// being no multiple of a prime up to 23 (`prmlem2`); 0 and 1 by name,
    /// and any other by its least factor and what is left (`nprmi`). None
    /// for a prime of 841 or more.
    fn primality(&self, n: &BigUint) -> Option<Proof> {
        let b = &self.b;
        let sn = numerals::spell(n.clone());
        let small = n.to_u32();
        match small {
            Some(0) => return Some(b.step("0nprm")),
            Some(1) => return Some(b.step("1nprm")),
            Some(2) => return Some(b.step("2prm")),
            Some(3) => return Some(b.step("3prm")),
            _ => {}
        }
        if !is_prime(n) {
            let factor = least_factor(n);
            let rest = n / &factor;
            let (sa, sb) = (
                numerals::spell(factor.clone()),
                numerals::spell(rest.clone()),
            );
            return Some(b.ap(
                "nprmi",
                &binds! {"A" => &sa, "B" => &sb, "N" => &sn},
                &[
                    &numerals::nn(b, factor.clone()),
                    &numerals::nn(b, rest.clone()),
                    &numerals::below(b, 1u32, factor.clone()),
                    &numerals::below(b, 1u32, rest.clone()),
                    &numerals::product(b, factor, rest),
                ],
            ));
        }
        let whole = numerals::nn(b, n.clone());
        let above_one = numerals::below(b, 1u32, n.clone());
        let not_by = |p: u32| self.divides_at_values(&BigUint::from(p), n);
        // Each lemma's hypotheses in the order it states them: prmlem1 its
        // bound last, prmlem2 its bound second.
        let (lemma, hyps) = if *n < BigUint::from(25u32) {
            let below = numerals::below(b, n.clone(), 25u32);
            (
                "prmlem1",
                vec![whole, above_one, not_by(2), not_by(3), below],
            )
        } else if *n < BigUint::from(841u32) {
            let below = numerals::below(b, n.clone(), 841u32);
            let mut hyps = vec![whole, below, above_one];
            hyps.extend([2, 3, 5, 7, 11, 13, 17, 19, 23].map(not_by));
            ("prmlem2", hyps)
        } else {
            return None;
        };
        let refs: Vec<&Proof> = hyps.iter().collect();
        Some(b.ap(lemma, &binds! {"N" => &sn}, &refs))
    }

    /// The value of numerals alone a cited equation gives `side`, and
    /// ( scope -> side = value ), the equation turned where it is written
    /// the other way round. None where no cited line gives one.
    fn cited_value(
        &mut self,
        side: &Rpn,
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Option<(Rpn, Proof)>> {
        let numeric = |x: &Rpn| x.tokens().iter().all(|t| rules::numeric(t.as_str()));
        for claim in known.keys() {
            let said = self.to_term(&claim);
            if said.variable().is_some()
                || said.label() != Some("wceq")
                || said.children().len() != 2
            {
                continue;
            }
            let (l, r) = (self.rpn(&said.children()[0]), self.rpn(&said.children()[1]));
            let (value, turned) = if l == *side && numeric(&r) {
                (r, false)
            } else if r == *side && numeric(&l) {
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
        letter: &Rpn,
        elements: &[Term],
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<Kept>> {
        let p = self.rpn(body);
        let builder = |over: &Rpn| t!(p, letter, over, "crab");
        if elements.is_empty() {
            let none = self.b.ap("rab0", &binds! {"x" => letter, "ph" => &p}, &[]);
            return Ok(Built(Kept {
                elements: Vec::new(),
                proof: self.b.ap(
                    "a1i",
                    &binds! {"ph" => &t!(builder(&t!("c0")), "c0", "wceq"), "ps" => scope},
                    &[&none],
                ),
            }));
        }
        if elements.len() == 1 {
            let c = self.rpn(&elements[0]);
            let single = t!(c, "csn");
            let at = self.rpn(&self.restated(body, &t!(letter, "cv"), &c));
            let tie =
                self.to_term(&t!(t!(letter, "cv", c, "wceq"), t!(p, at, "wb"), "wi"));
            let tie =
                take!(self.prove_essential(&tie, &Rpn::default(), &Facts::new())?);
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
                Settled::Fails(q) => ("iffalse", Vec::new(), q, t!("c0")),
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
        let made_of = |me: &Self, kept: &[Term]| -> Rpn {
            if kept.is_empty() {
                t!("c0")
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
        scope: &Rpn,
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
    /// that sum: one for the first element, one more for each element the
    /// lines say differs from those before it, and none for one written
    /// before it.
    fn counted(
        &mut self,
        elements: &[Term],
        scope: &Rpn,
        known: &Facts,
    ) -> Checked<Route<(Proof, Rpn)>> {
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
                t!("c1"),
            )));
        }
        let (init, last) = elements.split_at(elements.len() - 1);
        let (before, sum_before) = take!(self.counted(init, scope, known)?);
        let front = self.union_of(init);
        let c = self.rpn(&last[0]);
        let whole = t!(front, t!(c, "csn"), "cun");
        let size_whole = t!(whole, "chash", "cfv");
        let size_front = t!(front, "chash", "cfv");
        // A thing listed already adds nothing: its singleton is inside what
        // is listed before it, so the union is that (`ssequn2`), and so is
        // its size. {2, 2, 3} is two things.
        if let Some(at) = self.position(&last[0], init) {
            let inside = take!(self.in_union(&last[0], init, at, scope, known)?);
            let single = t!(c, "csn");
            let within = self.b.ap(
                "snssd",
                &binds! {"ph" => scope, "A" => &c, "B" => &front},
                &[&inside],
            );
            let law =
                self.b
                    .ap("ssequn2", &binds! {"A" => &single, "B" => &front}, &[]);
            let same = self.b.ap(
                "sylib",
                &binds! {"ph" => scope, "ps" => t!(single, front, "wss"),
                "ch" => t!(whole, front, "wceq")},
                &[&within, &law],
            );
            let sized = self.b.ap(
                "fveq2d",
                &binds! {"ph" => scope, "A" => &whole, "B" => &front, "F" => "chash"},
                &[&same],
            );
            return Ok(Built((
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &size_whole, "B" => &size_front, "C" => &sum_before},
                    &[&sized, &before],
                ),
                sum_before,
            )));
        }
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

/// The singletons of the integers from `from` to `to`, joined from the
/// left: `( ( { -u 1 } u. { 0 } ) u. { 1 } )`.
fn singletons(from: &BigInt, to: &BigInt) -> Rpn {
    let mut out = t!(numerals::spell_integer(from), "csn");
    let mut k = from + 1u32;
    while k <= *to {
        out = t!(out, t!(numerals::spell_integer(&k), "csn"), "cun");
        k += 1u32;
    }
    out
}
