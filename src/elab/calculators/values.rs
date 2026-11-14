//! Values, numerals and divisibility.

use super::*;

impl<'a> Elaborator<'a> {
    /// ( scope -> claim ) for a closed claim, said of its sides' values: each
    /// side is worked to its value written plainly (`closed_valued`), the
    /// claim is proved of the values by the routes above, and the law that
    /// carries an equation through the relation brings it back to the sides
    /// as written (`breq12d`, `eqeq12d`, `eleq1d`). A claim whose sides are
    /// values already is one those routes did not prove.
    pub(super) fn by_values(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut goal = self.to_term(term);
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        if negated {
            goal = goal.children()[0].clone();
        }
        let kids = goal.children().to_vec();
        let side = |me: &mut Self, t: &Term| me.closed_valued(t, scope, facts);
        let (valued, iff) = match (goal.label(), kids.as_slice()) {
            (Some("wcel"), [x, set]) => {
                let (_, cx, px) = take!(side(self, x)?);
                let (sx, ss) = (self.rpn(x), self.rpn(set));
                let iff = self.b.ap(
                    "eleq1d",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &cx, "C" => &ss},
                    &[&px],
                );
                (t!(&cx, &ss, "wcel"), iff)
            }
            (Some("wceq"), [a, b]) => {
                let (_, ca, pa) = take!(side(self, a)?);
                let (_, cb, pb) = take!(side(self, b)?);
                let iff = self.b.ap(
                    "eqeq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &ca, "C" => self.rpn(b), "D" => &cb},
                    &[&pa, &pb],
                );
                (t!(&ca, &cb, "wceq"), iff)
            }
            (Some("wbr"), [a, b, relation]) => {
                let (_, ca, pa) = take!(side(self, a)?);
                let (_, cb, pb) = take!(side(self, b)?);
                let r = self.rpn(relation);
                let iff = self.b.ap(
                    "breq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(a), "B" => &ca, "C" => self.rpn(b), "D" => &cb, "R" => &r},
                    &[&pa, &pb],
                );
                (t!(&ca, &cb, &r, "wbr"), iff)
            }
            _ => return Ok(Route::no("not a relation of closed terms")),
        };
        let said = self.rpn(&goal);
        if valued == said {
            return Ok(Route::no("its sides are their values already"));
        }
        let at = self.denied_if(Revalued { said, valued, iff }, negated, scope);
        let held = match self.prove_numeral(&at.valued, scope, facts)? {
            Built(p) => p,
            Declined(_) => {
                take!(self.prove_field(
                    None,
                    &at.valued,
                    scope,
                    facts,
                    &Lines::new()
                )?)
            }
        };
        Ok(Built(self.carried_back(&at, &held, scope)))
    }

    /// The same of the two claims' denials, where `negated` (`notbid`).
    pub(in crate::elab) fn denied_if(
        &self,
        at: Revalued,
        negated: bool,
        scope: &Rpn,
    ) -> Revalued {
        if !negated {
            return at;
        }
        let iff = self.b.ap(
            "notbid",
            &binds! {"ph" => scope, "ps" => &at.said, "ch" => &at.valued},
            &[&at.iff],
        );
        Revalued {
            said: t!(&at.said, "wn"),
            valued: t!(&at.valued, "wn"),
            iff,
        }
    }

    /// ( scope -> said ) from ( scope -> valued ), `held` (`mpbird`).
    pub(in crate::elab) fn carried_back(
        &self,
        at: &Revalued,
        held: &Proof,
        scope: &Rpn,
    ) -> Proof {
        self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &at.said, "ch" => &at.valued},
            &[held, &at.iff],
        )
    }

    /// ( scope -> -. x e. S ) for a closed x whose value v is no whole
    /// number, and S one of ℤ, ℕ and ℕ₀: v lies strictly between the whole
    /// number below it and the next (`btwnnz`), so x is not in ℤ, and ℕ and
    /// ℕ₀ lie in ℤ (`nnz`, `nn0z`).
    pub(super) fn not_whole(
        &mut self,
        member: &Term,
        v: &Q,
        system: Option<&str>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let lift = match system {
            Some("cz") => None,
            Some("cn") => Some("nnz"),
            Some("cn0") => Some("nn0z"),
            _ => return Ok(Route::no("a non-membership of a system a fraction is in")),
        };
        let floor = v.floor().to_integer();
        let low = numerals::spell_integer(&floor);
        let sm = self.rpn(member);
        let next = t!(&low, "c1", "caddc", "co");
        let closed = |me: &mut Self, claim: Rpn| -> Checked<Route<Proof>> {
            Ok(match me.prove_numeral(&claim, scope, facts)? {
                Built(p) => Built(p),
                Declined(_) => me.by_values(&claim, scope, facts)?,
            })
        };
        let whole = take!(closed(self, t!(&low, "cz", "wcel"))?);
        let above = take!(closed(self, t!(&low, &sm, "clt", "wbr"))?);
        let below = take!(closed(self, t!(&sm, &next, "clt", "wbr"))?);
        let law = self.b.ap("btwnnz", &binds! {"A" => &low, "B" => &sm}, &[]);
        let not_integer = self.b.ap(
            "syl3anc",
            &binds! {"ph" => scope, "ps" => t!(&low, "cz", "wcel"), "ch" => t!(&low, &sm, "clt", "wbr"),
            "th" => t!(&sm, &next, "clt", "wbr"), "ta" => t!(t!(&sm, "cz", "wcel"), "wn")},
            &[&whole, &above, &below, &law],
        );
        let Some(lift) = lift else {
            return Ok(Built(not_integer));
        };
        let set = system.unwrap_or_default();
        let lift = self.b.ap(lift, &binds! {"N" => &sm}, &[]);
        let lift = pf!(self.b; t!(t!(&sm, set, "wcel"), t!(&sm, "cz", "wcel"), "wi"), scope, lift, "a1i");
        Ok(Built(self.b.ap(
            "mtod",
            &binds! {"ph" => scope, "ps" => t!(&sm, set, "wcel"), "ch" => t!(&sm, "cz", "wcel")},
            &[&not_integer, &lift],
        )))
    }

    /// ( scope -> t = v ) for a closed term t, with its value and v: the
    /// value written plainly, a numeral, its negation, a fraction of two
    /// numerals or the negation of one. The normaliser works out sums,
    /// differences, products, quotients and whole powers (`prove_field`); a
    /// remainder and a product over a range it holds as an atom, so each is
    /// worked first (`numerals::worked`), from the inside out, and carried up
    /// through the operations above it (`oveq12d`, `negeqd`).
    pub(in crate::elab) fn closed_valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Q, Rpn, Proof)>> {
        let Built(Value::Exact(v)) = field::closed_value(t) else {
            return Ok(Route::no("it has no exact value"));
        };
        let plain = |n: &BigInt| numerals::spell(n.magnitude().clone());
        let body = if v.is_integer() {
            plain(v.numer())
        } else {
            t!(plain(v.numer()), plain(v.denom()), DIV, "co")
        };
        let canon = if v.is_negative() {
            t!(body, "cneg")
        } else {
            body
        };
        let said = self.rpn(t);
        if said == canon {
            let same = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &said}, &[]);
            return Ok(Built((v, canon, same)));
        }
        let labels = self.b.flabel.clone();
        let lifted = |me: &Self, is: Proof, from: &Rpn| pf!(me.b; t!(from, &canon, "wceq"), scope, is, "a1i");
        // The term whole, where the normaliser reaches it; else part by part.
        if !self.normaliser_opaque(t) {
            if let Built(equal) = self.prove_field(
                None,
                &t!(&said, &canon, "wceq"),
                scope,
                facts,
                &Lines::new(),
            )? {
                return Ok(Built((v, canon, equal)));
            }
        }
        if let Some((_, is)) = numerals::worked(&self.b, t, &labels) {
            return Ok(Built((v, canon.clone(), lifted(self, is, &said))));
        }
        let kids = t.children().to_vec();
        let (moved, middle) = match (t.label(), kids.as_slice()) {
            (Some("co"), [x, y, op]) => {
                let (_, cx, px) = take!(self.closed_valued(x, scope, facts)?);
                let (_, cy, py) = take!(self.closed_valued(y, scope, facts)?);
                let op = self.rpn(op);
                let moved = self.b.ap(
                    "oveq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &cx, "C" => self.rpn(y), "D" => &cy, "F" => &op},
                    &[&px, &py],
                );
                (moved, t!(&cx, &cy, &op, "co"))
            }
            (Some("cneg"), [x]) => {
                let (_, cx, px) = take!(self.closed_valued(x, scope, facts)?);
                let moved = self.b.ap(
                    "negeqd",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &cx},
                    &[&px],
                );
                (moved, t!(&cx, "cneg"))
            }
            _ => return Ok(Route::no("an operation its value is not carried through")),
        };
        // What is left is an operation on values: a remainder of two whole
        // numbers is worked, a division by a value below 0 is the negation
        // of one by its opposite (`divneg2d`), and anything else is the
        // normaliser's.
        let field = |me: &mut Self, from: &Rpn| {
            me.prove_field(None, &t!(from, &canon, "wceq"), scope, facts, &Lines::new())
        };
        let middle_term = self.to_term(&middle);
        let by_negative = match (middle_term.label(), middle_term.children()) {
            (Some("co"), [x, y, op])
                if op.label() == Some(DIV) && y.label() == Some("cneg") =>
            {
                Some((self.rpn(x), self.rpn(&y.children()[0])))
            }
            _ => None,
        };
        // A power to −n is one over the power to n (`expnegd`), which the
        // normaliser multiplies out.
        let by_reciprocal = match (middle_term.label(), middle_term.children()) {
            (Some("co"), [x, y, op])
                if op.label() == Some(field::EXP) && y.label() == Some("cneg") =>
            {
                Some((self.rpn(x), self.rpn(&y.children()[0])))
            }
            _ => None,
        };
        let rest = match (
            numerals::worked(&self.b, &middle_term, &labels),
            by_negative,
            by_reciprocal,
        ) {
            (Some((_, is)), _, _) => lifted(self, is, &middle),
            (None, None, Some((base, n))) => {
                let goal = self.to_term(&t!(&base, "cc", "wcel"));
                let base_cc = take!(self.numeral_within(&goal, scope, facts)?);
                let apart = self.not_zero(scope, facts, &base)?;
                let goal = self.to_term(&t!(&n, "cz", "wcel"));
                let n_z = take!(self.numeral_within(&goal, scope, facts)?);
                let turned = self.b.ap(
                    "expnegd",
                    &binds! {"ph" => scope, "A" => &base, "N" => &n},
                    &[&base_cc, &apart, &n_z],
                );
                let over = t!("c1", t!(&base, &n, field::EXP, "co"), DIV, "co");
                let valued = take!(field(self, &over)?);
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &middle, "B" => &over, "C" => &canon},
                    &[&turned, &valued],
                )
            }
            (None, Some((top, bottom)), _) => {
                let within = |me: &mut Self, s: &Rpn| {
                    let goal = me.to_term(&t!(s, "cc", "wcel"));
                    me.numeral_within(&goal, scope, facts)
                };
                let top_cc = take!(within(self, &top)?);
                let bottom_cc = take!(within(self, &bottom)?);
                let apart = self.not_zero(scope, facts, &bottom)?;
                let moved_in = self.b.ap(
                    "divneg2d",
                    &binds! {"ph" => scope, "A" => &top, "B" => &bottom},
                    &[&top_cc, &bottom_cc, &apart],
                );
                let negated = t!(t!(&top, &bottom, DIV, "co"), "cneg");
                let turned = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => &negated, "B" => &middle},
                    &[&moved_in],
                );
                let valued = take!(field(self, &negated)?);
                self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &middle, "B" => &negated, "C" => &canon},
                    &[&turned, &valued],
                )
            }
            (None, None, None) => take!(field(self, &middle)?),
        };
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &said, "B" => &middle, "C" => &canon},
            &[&moved, &rest],
        );
        Ok(Built((v, canon, joined)))
    }

    /// The defect for a claim `arithmetic` could not prove: it is never taken
    /// as stated instead.
    pub fn unshown(&self, term: &Rpn, what: &str) -> Problem {
        match field::decide_closed(&self.to_term(term)) {
            Declined(_) => self.defect(
                self.at,
                format!("{what}, which is not a fact about numerals alone, and arithmetic decides nothing else"),
            ),
            Built(Verdict::Holds(false)) => {
                self.defect(self.at, format!("{what}, which is false"))
            }
            Built(Verdict::Unworked(why)) => {
                self.defect(self.at, format!("{what}, which {why}"))
            }
            Built(Verdict::Holds(true)) => self.defect(
                self.at,
                format!("{what}, which is true, and arithmetic cannot show it yet; cite a theorem that states it"),
            ),
        }
    }

    /// A closed numeral fact, decided by working it out and then said: that
    /// one number is below another is what set.mm names for every pair, and
    /// everything else is that weakened or turned.
    pub fn prove_numeral(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let mut goal = self.to_term(term);
        // set.mm's other spelling of a disequation, A =/= B, is the page's
        // ¬ (A = B) proved and turned (`neqned`).
        if goal.variable().is_none()
            && goal.label() == Some("wne")
            && goal.children().len() == 2
        {
            let (a, b) = (self.rpn(&goal.children()[0]), self.rpn(&goal.children()[1]));
            let denied = t!(t!(&a, &b, "wceq"), "wn");
            let proof = take!(self.prove_numeral(&denied, scope, facts)?);
            return Ok(Built(self.b.ap(
                "neqned",
                &binds! {"ph" => scope, "A" => &a, "B" => &b},
                &[&proof],
            )));
        }
        let mut negated = false;
        if goal.variable().is_none()
            && goal.label() == Some("wn")
            && goal.children().len() == 1
        {
            negated = true;
            goal = goal.children()[0].clone();
        }
        // Belonging to a number system is the other thing a claim with no
        // atom can say.
        if !negated
            && goal.variable().is_none()
            && goal.label() == Some("wcel")
            && goal.children().len() == 2
        {
            return self.numeral_within(&goal, scope, facts);
        }
        // A divisibility, which is what "is even" and "is odd" are too, where
        // the word's record says `arithmetic` decides it.
        if goal.variable().is_none()
            && goal.label() == Some("wbr")
            && goal.children().len() == 3
            && goal.children()[2].label() == Some("cdvds")
        {
            let whole = if negated {
                Term::apply("wn", vec![goal.clone()])
            } else {
                goal.clone()
            };
            if !self.decided_by("arithmetic", &whole)? {
                return Ok(Route::no(
                    "no record of a word says arithmetic decides this divisibility",
                ));
            }
            return self.divides_proved(&goal, negated, scope, facts);
        }
        // Not in ℕ₀ for a value below 0, whose members are at least 0
        // (`nn0ge0`); not in ℕ for one at most 0, whose members are above it
        // (`nngt0`).
        if negated
            && goal.variable().is_none()
            && goal.label() == Some("wcel")
            && goal.children().len() == 2
        {
            let (member, system) = (&goal.children()[0], goal.children()[1].label());
            if let Built(Value::Exact(v)) = field::closed_value(member) {
                if !v.is_integer() {
                    return self.not_whole(member, &v, system, scope, facts);
                }
            }
            let (how, law) = match system {
                Some("cn0") => ("<=", "nn0ge0"),
                Some("cn") => ("<", "nngt0"),
                _ => {
                    return Ok(Route::no(
                        "a non-membership of a system other than ℕ or ℕ₀",
                    ))
                }
            };
            let zero = Term::apply("cc0", Vec::new());
            let below = take!(
                self.order_by_difference(&zero, member, how, true, scope, facts)?
            );
            let m = self.rpn(member);
            let relation = if how == "<" { "clt" } else { "cle" };
            let held = t!("cc0", &m, relation, "wbr");
            let law = self.b.ap(law, &binds! {"N" => &m, "A" => &m}, &[]);
            let law = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(self.rpn(&goal), &held, "wi"), "ps" => scope},
                &[&law],
            );
            return Ok(Built(self.b.ap(
                "mtod",
                &binds! {"ph" => scope, "ps" => self.rpn(&goal), "ch" => &held},
                &[&below, &law],
            )));
        }
        let Some((first, second, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        let (Some(a), Some(b)) = (numerals::value(&first), numerals::value(&second))
        else {
            // An equation of whole numbers each side works out to, a
            // remainder among them, is the two worked out and joined
            // (`eqtr4i`).
            if how == "=" && !negated {
                let labels = self.b.flabel.clone();
                if let (Some((a, a_is)), Some((b, b_is))) = (
                    numerals::worked(&self.b, &first, &labels),
                    numerals::worked(&self.b, &second, &labels),
                ) {
                    if a == b {
                        let (sf, ss) = (self.rpn(&first), self.rpn(&second));
                        let joined = self.b.ap(
                            "eqtr4i",
                            &binds! {"A" => &sf, "B" => numerals::spell(a), "C" => &ss},
                            &[&a_is, &b_is],
                        );
                        return Ok(Built(self.b.ap(
                            "a1i",
                            &binds! {"ph" => t!(sf, ss, "wceq"), "ps" => scope},
                            &[&joined],
                        )));
                    }
                }
            }
            // A disequation with a side below 0 is the lower below the
            // higher (`order_by_difference`), and so apart (`ltne`).
            let below_zero = |side: &Term| matches!(field::closed_value(side), Built(Value::Exact(v)) if v.is_negative());
            if how == "=" && negated && (below_zero(&first) || below_zero(&second)) {
                return self.closed_apart(&first, &second, scope, facts);
            }
            // A disequation of whole numbers each side works out to is the
            // two values apart, carried to the sides as written (`eqeq12i`).
            if how == "=" && negated {
                let labels = self.b.flabel.clone();
                if let (Some((a, a_is)), Some((b, b_is))) = (
                    numerals::worked(&self.b, &first, &labels),
                    numerals::worked(&self.b, &second, &labels),
                ) {
                    if a != b {
                        let apart = self.numerals_differ(scope, &a, &b);
                        let (sf, ss) = (self.rpn(&first), self.rpn(&second));
                        let (na, nb) = (numerals::spell(a), numerals::spell(b));
                        let same = self.b.ap(
                            "eqeq12i",
                            &binds! {"A" => &sf, "B" => &na, "C" => &ss, "D" => &nb},
                            &[&a_is, &b_is],
                        );
                        let (said, valued) =
                            (t!(&sf, &ss, "wceq"), t!(&na, &nb, "wceq"));
                        let turned = self.b.ap(
                            "notbii",
                            &binds! {"ph" => &said, "ps" => &valued},
                            &[&same],
                        );
                        return Ok(Built(self.b.ap(
                            "sylibr",
                            &binds! {"ph" => scope, "ps" => t!(valued, "wn"), "ch" => t!(said, "wn")},
                            &[&apart, &turned],
                        )));
                    }
                }
            }
            // A disequation of sides that are not both whole numbers, a
            // fraction among them, is the lower below the higher too.
            if how == "=" && negated {
                return self.closed_apart(&first, &second, scope, facts);
            }
            // An equation is the normaliser's, which works fractions too.
            if how == "=" {
                return Ok(Route::no(
                    "a side works out to a whole number but is one only after working out",
                ));
            }
            return self
                .order_by_values(&goal, &first, &second, how, negated, scope, facts);
        };
        let (na, nb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        let (na, nb) = (&na, &nb);
        if negated {
            return Ok(match how {
                "=" if a != b => Built(self.numerals_differ(scope, &a, &b)),
                // not a ≤ b is b < a, and not a < b is b ≤ a, each turned by
                // the law that says so (`ltnled`, `lenltd`).
                "<=" if b < a => {
                    let below = self.numeral_below(scope, &b, &a);
                    let below = self.numerals_ordered(scope, nb, na, below);
                    Built(self.denied(scope, nb, na, &below, true))
                }
                "<" if b <= a => {
                    let held = take!(self.prove_numeral(
                        &t!(nb, na, "cle", "wbr"),
                        scope,
                        facts
                    )?);
                    let held = self.numerals_ordered(scope, nb, na, held);
                    Built(self.denied(scope, nb, na, &held, false))
                }
                _ => Route::no("a denial of what holds"),
            });
        }
        if how == "=" && a == b {
            let same = self.b.ap("eqid", &binds! {"A" => na}, &[]);
            return Ok(Built(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(na, nb, "wceq"), "ps" => scope},
                &[&same],
            )));
        }
        if how == "<" && a < b {
            return Ok(Built(self.numeral_below(scope, &a, &b)));
        }
        if how == "<=" && a <= b {
            if a == b {
                let real = self.real_numeral(scope, &Q::from_integer(a.clone().into()));
                let law = self.b.ap("leid", &binds! {"A" => na}, &[]);
                return Ok(Built(self.b.ap(
                    "syl",
                    &binds! {"ph" => scope, "ps" => t!(na, "cr", "wcel"), "ch" => t!(na, na, "cle", "wbr")},
                    &[&real, &law],
                )));
            }
            let below = self.numeral_below(scope, &a, &b);
            let ra = self.real_numeral(scope, &Q::from_integer(a.clone().into()));
            let rb = self.real_numeral(scope, &Q::from_integer(b.clone().into()));
            let law = self.b.ap("ltle", &binds! {"A" => na, "B" => nb}, &[]);
            let weaken = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(na, "cr", "wcel"), "ch" => t!(nb, "cr", "wcel"),
                "th" => t!(t!(na, nb, "clt", "wbr"), t!(na, nb, "cle", "wbr"), "wi")},
                &[&ra, &rb, &law],
            );
            return Ok(Built(self.b.ap(
                "mpd",
                &binds! {"ph" => scope, "ps" => t!(na, nb, "clt", "wbr"), "ch" => t!(na, nb, "cle", "wbr")},
                &[&below, &weaken],
            )));
        }
        Ok(Route::no(format!(
            "{a} {how} {b} is not what the numbers do"
        )))
    }

    /// Whether the word `claim` says, or for a denial the word it denies, is
    /// one whose record names `method` in its `decided` field
    /// (`DATABASE.md`). Each such record's `then` line is read in its own
    /// sorts, and the kernel form of what it defines, its letters standing
    /// for any term, is fitted to the claim.
    pub fn decided_by(&mut self, method: &str, claim: &Term) -> Checked<bool> {
        if !self.decided.contains_key(method) {
            let records = self.records;
            let mut words = Vec::new();
            for r in records {
                if r.kind != RecordKind::Definition || !field::decides(r, method) {
                    continue;
                }
                // Each letter the word is said of stands for a set variable's
                // class, which `fits_word` lets any term fill.
                let hole = t!(self.spare[0], "cv");
                let said =
                    self.in_its_names(Item::Record(r), |me| -> Checked<Rpn> {
                        me.names_kept(|me| {
                            let node = me.read_one(&r.stated()[0])?;
                            let left = node.children[0].clone();
                            for name in left.names() {
                                me.names.insert(name, hole.clone());
                            }
                            me.term(&left)
                        })
                    })?;
                words.push(self.to_term(&said));
            }
            self.decided.insert(method.to_string(), words);
        }
        let mut forms = vec![claim.clone()];
        if claim.label() == Some("wn") && claim.children().len() == 1 {
            forms.push(claim.children()[0].clone());
        }
        Ok(self.decided[method]
            .iter()
            .any(|word| forms.iter().any(|f| fits_word(word, f))))
    }

    /// ( scope -> d ∥ n ), or its denial where `negated`, for closed d and n
    /// that work out to whole numbers, d at least 1 (`METHODS.md`,
    /// arithmetic): at their values by `dvdsmul1` at the quotient, or by
    /// `ndvdsi` from the quotient and the remainder, and carried back to the
    /// terms as written by `breq12i`. A decline where the sides do not work
    /// out so, or where what is asked is not what the numbers do.
    pub fn numeral_divides(
        &self,
        core: &Term,
        negated: bool,
        scope: &Rpn,
    ) -> Route<Proof> {
        let labels = self.b.flabel.clone();
        let kids = core.children();
        let (Some((d, d_is)), Some((num, n_is))) = (
            numerals::worked(&self.b, &kids[0], &labels),
            numerals::worked(&self.b, &kids[1], &labels),
        ) else {
            return Route::no(
                "a side of the divisibility is not a whole number worked out",
            );
        };
        if d.is_zero() {
            return Route::no("a divisor of 0");
        }
        if (&num % &d).is_zero() == negated {
            return Route::no("a divisibility that is not what the numbers do");
        }
        let (sd, sn) = (numerals::spell(d.clone()), numerals::spell(num.clone()));
        let at_values = t!(sd, sn, "cdvds", "wbr");
        let shown = self.divides_at_values(&d, &num);
        let said = |t: Rpn| if negated { t!(t, "wn") } else { t };
        let (written, at) = (said(self.rpn(core)), said(at_values.clone()));
        let closed = if written == at {
            shown
        } else {
            let (rd, rn) = (self.rpn(&kids[0]), self.rpn(&kids[1]));
            let mut same = self.b.ap(
                "breq12i",
                &binds! {"A" => &rd, "B" => &sd, "C" => &rn, "D" => &sn, "R" => "cdvds"},
                &[&d_is, &n_is],
            );
            if negated {
                same = self.b.ap(
                    "notbii",
                    &binds! {"ph" => self.rpn(core), "ps" => &at_values},
                    &[&same],
                );
            }
            self.b.ap(
                "mpbir",
                &binds! {"ph" => &written, "ps" => &at},
                &[&shown, &same],
            )
        };
        Built(
            self.b
                .ap("a1i", &binds! {"ph" => &written, "ps" => scope}, &[&closed]),
        )
    }

    /// |- d ∥ n where d divides n, and |- -. d ∥ n where it does not, d at
    /// least 1, each spelt as `numerals::spell` spells them: by `dvdsmul1`
    /// at the quotient, or by `ndvdsi` from the quotient and the remainder.
    pub fn divides_at_values(&self, d: &BigUint, num: &BigUint) -> Proof {
        let (quotient, rest) = (num / d, num % d);
        let negated = !rest.is_zero();
        let (sd, sn, sq) = (
            numerals::spell(d.clone()),
            numerals::spell(num.clone()),
            numerals::spell(quotient.clone()),
        );
        let times = t!(sd, sq, "cmul", "co");
        let product = numerals::product(&self.b, d.clone(), quotient.clone());
        if negated {
            // n = d·q + r with 0 < r < d.
            let sr = numerals::spell(rest.clone());
            let sp = numerals::spell(d * &quotient);
            let moved = self.b.ap(
                "oveq1i",
                &binds! {"A" => &times, "B" => &sp, "C" => &sr, "F" => "caddc"},
                &[&product],
            );
            let total = self.b.ap(
                "eqtri",
                &binds! {"A" => t!(times, sr, "caddc", "co"), "B" => t!(sp, sr, "caddc", "co"), "C" => &sn},
                &[&moved, &numerals::sum(&self.b, d * &quotient, rest.clone())],
            );
            self.b.ap(
                "ndvdsi",
                &binds! {"A" => &sd, "B" => &sn, "Q" => &sq, "R" => &sr},
                &[
                    &numerals::nn(&self.b, d.clone()),
                    &numerals::nn0(&self.b, quotient.clone()),
                    &numerals::nn(&self.b, rest.clone()),
                    &total,
                    &numerals::below(&self.b, rest.clone(), d.clone()),
                ],
            )
        } else {
            let whole_d = self.b.ap(
                "nnzi",
                &binds! {"N" => &sd},
                &[&numerals::nn(&self.b, d.clone())],
            );
            let whole_q = self.b.ap(
                "nn0zi",
                &binds! {"N" => &sq},
                &[&numerals::nn0(&self.b, quotient.clone())],
            );
            let law = self.b.ap("dvdsmul1", &binds! {"M" => &sd, "N" => &sq}, &[]);
            let held = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sd, "cz", "wcel"), "ps" => t!(sq, "cz", "wcel"),
                "ch" => t!(sd, times, "cdvds", "wbr")},
                &[&whole_d, &whole_q, &law],
            );
            self.b.ap(
                "breqtri",
                &binds! {"A" => &sd, "R" => "cdvds", "B" => &times, "C" => &sn},
                &[&held, &product],
            )
        }
    }

    /// ( scope -> d ∥ n ), or its denial where `negated`, for closed d and n
    /// that work out to integers, d not 0. Where both work out to whole
    /// numbers it is `numeral_divides`. Otherwise it is that at their sizes,
    /// the signs turned by `dvdsnegb` and `negdvdsb`, each of which says a
    /// divisibility holds exactly where it does with a side negated, and
    /// carried back to the terms as written by `breq12d`.
    pub fn divides_proved(
        &mut self,
        core: &Term,
        negated: bool,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let kids = core.children().to_vec();
        let whole = kids[..2]
            .iter()
            .all(|side| numerals::worked(&self.b, side, &labels).is_some());
        if whole {
            return Ok(self.numeral_divides(core, negated, scope));
        }
        let (d, vd, d_is) = take!(self.closed_valued(&kids[0], scope, facts)?);
        let (n, vn, n_is) = take!(self.closed_valued(&kids[1], scope, facts)?);
        if !d.is_integer() || !n.is_integer() || d.is_zero() {
            return Ok(Route::no("a side of the divisibility is not an integer"));
        }
        let (a, b) = (
            d.to_integer().magnitude().clone(),
            n.to_integer().magnitude().clone(),
        );
        let (sa, sb) = (numerals::spell(a.clone()), numerals::spell(b.clone()));
        let sizes = t!(sa, sb, "cdvds", "wbr");
        let at_sizes =
            take!(self.numeral_divides(&self.to_term(&sizes), negated, scope));
        // |- ( a ∥ b <-> vd ∥ vn ), a sign turned at a time.
        let za = self.b.ap(
            "nnzi",
            &binds! {"N" => &sa},
            &[&numerals::nn(&self.b, a.clone())],
        );
        let zb = self.b.ap(
            "nn0zi",
            &binds! {"N" => &sb},
            &[&numerals::nn0(&self.b, b.clone())],
        );
        let mut number = sb.clone();
        let mut number_z = zb;
        // Where the turns have reached, and |- ( a ∥ b <-> that ), each turn
        // chained onto the last by `bitri`.
        let mut turned: Option<(Rpn, Proof)> = None;
        let chain = |me: &Self, turned: Option<(Rpn, Proof)>, to: Rpn, iff: Proof| {
            Some(match turned {
                None => (to, iff),
                Some((was, before)) => {
                    let chained = me.b.ap(
                        "bitri",
                        &binds! {"ph" => &sizes, "ps" => &was, "ch" => &to},
                        &[&before, &iff],
                    );
                    (to, chained)
                }
            })
        };
        if n.is_negative() {
            let to = t!(sa, t!(sb, "cneg"), "cdvds", "wbr");
            let law = self.b.ap("dvdsnegb", &binds! {"M" => &sa, "N" => &sb}, &[]);
            let iff = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sa, "cz", "wcel"), "ps" => t!(sb, "cz", "wcel"),
                "ch" => t!(&sizes, &to, "wb")},
                &[&za, &number_z, &law],
            );
            turned = chain(self, turned, to, iff);
            let negz = self.b.ap("znegcl", &binds! {"N" => &sb}, &[]);
            number_z = self.b.ap(
                "ax-mp",
                &binds! {"ph" => t!(sb, "cz", "wcel"), "ps" => t!(t!(sb, "cneg"), "cz", "wcel")},
                &[&number_z, &negz],
            );
            number = t!(sb, "cneg");
        }
        if d.is_negative() {
            let from = t!(sa, &number, "cdvds", "wbr");
            let to = t!(t!(sa, "cneg"), &number, "cdvds", "wbr");
            let law = self
                .b
                .ap("negdvdsb", &binds! {"M" => &sa, "N" => &number}, &[]);
            let iff = self.b.ap(
                "mp2an",
                &binds! {"ph" => t!(sa, "cz", "wcel"), "ps" => t!(&number, "cz", "wcel"),
                "ch" => t!(&from, &to, "wb")},
                &[&za, &number_z, &law],
            );
            turned = chain(self, turned, to, iff);
        }
        let Some((at_values, mut iff)) = turned else {
            return Ok(Route::no(
                "a divisibility of whole numbers is `numeral_divides`",
            ));
        };
        if at_values != t!(vd, vn, "cdvds", "wbr") {
            return Ok(Route::no("the values are not spelt as their sizes turned"));
        }
        let (mut before, mut after) = (sizes.clone(), at_values.clone());
        if negated {
            iff =
                self.b
                    .ap("notbii", &binds! {"ph" => &before, "ps" => &after}, &[&iff]);
            before = t!(before, "wn");
            after = t!(after, "wn");
        }
        let at_signs = self.b.ap(
            "sylib",
            &binds! {"ph" => scope, "ps" => &before, "ch" => &after},
            &[&at_sizes, &iff],
        );
        let written = self.rpn(core);
        let mut same = self.b.ap(
            "breq12d",
            &binds! {"ph" => scope, "A" => self.rpn(&kids[0]), "B" => &vd,
            "C" => self.rpn(&kids[1]), "D" => &vn, "R" => "cdvds"},
            &[&d_is, &n_is],
        );
        let claim = if negated {
            same = self.b.ap(
                "notbid",
                &binds! {"ph" => scope, "ps" => &written, "ch" => &at_values},
                &[&same],
            );
            t!(written, "wn")
        } else {
            written
        };
        Ok(Built(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &claim, "ch" => &after},
            &[&at_signs, &same],
        )))
    }
}
