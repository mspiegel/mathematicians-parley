//! Surds, powers, logarithms, exponentials and trigonometry.

use super::*;
use reals::Trig::{Cosine, Sine};

impl<'a> Elaborator<'a> {
    /// ( scope -> claim ) for a membership, said of the term's canon and
    /// carried back to the term as written (`eleq1d`), as `arithmetic` says
    /// one of its value. The canon is rational, which `arithmetic` decides
    /// of, except in a membership of ℝ or ℂ, which the canon has by the
    /// roots and atoms it is built from.
    pub(super) fn by_surd_values(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let negated = goal.label() == Some("wn") && goal.children().len() == 1;
        let inner = if negated { &goal.children()[0] } else { goal };
        let kids = inner.children().to_vec();
        let (Some("wcel"), [x, set]) = (inner.label(), kids.as_slice()) else {
            return Ok(Route::no("not a relation real arithmetic proves"));
        };
        let side = take!(self.valued(x, scope, facts)?);
        // A membership of a value that is not rational is ℝ's or ℂ's, which
        // the canon has by the atoms it is built from.
        let atoms_in = side.value.as_surd().and_then(|s| s.as_rational()).is_none();
        let (sx, ss) = (self.rpn(x), self.rpn(set));
        let iff = self.b.ap(
            "eleq1d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &side.canon, "C" => &ss},
            &[&side.proof],
        );
        let valued = t!(&side.canon, &ss, "wcel");
        let said = self.rpn(inner);
        let at = self.denied_if(Revalued { said, valued, iff }, negated, scope);
        let held = if atoms_in {
            let goal = self.to_term(&at.valued);
            let Some(system) = goal.children()[1].label().map(str::to_string) else {
                return Ok(Route::no("the set the value is in is a letter"));
            };
            let canon = self.rpn(&goal.children()[0]);
            self.membership(&canon, &system, scope, facts)?
        } else {
            self.numeral_fact(&at.valued, scope, facts)?
        };
        Ok(Built(self.carried_back(&at, &held, scope)))
    }

    /// ( scope -> t = canon ) for a closed term t.
    pub(super) fn valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Built(reals::Value::Exact(value)) = reals::closed_value(t) else {
            return Ok(Route::no("a term with no value"));
        };
        let said = self.rpn(t);
        if !reals::beyond_arithmetic(t) {
            let canon = canon(&value);
            if said == canon {
                let same =
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &said}, &[]);
                return Ok(Built(Valued {
                    value,
                    canon,
                    proof: same,
                }));
            }
            let (_, worked, proof) = take!(self.closed_valued(t, scope, facts)?);
            debug_assert_eq!(worked, canon, "a rational has one canon");
            return Ok(Built(Valued {
                value,
                canon,
                proof,
            }));
        }
        if surds::is_root(t) {
            return self.root_piece(t, value, scope, facts);
        }
        if reals::applies(t, "clog") {
            return self.ln_piece(t, value, scope, facts);
        }
        if reals::applies(t, "ce") {
            return self.exp_piece(t, value, scope, facts);
        }
        if let Some(f) = reals::Trig::of(t) {
            return self.trig_piece(t, f, value, scope, facts);
        }
        let kids = t.children().to_vec();
        if matches!(t.label(), Some("cpi" | "ceu")) && kids.is_empty() {
            return self.made_canon(&said, &value, scope, facts);
        }
        let (written, moved) = match (t.label(), kids.as_slice()) {
            (Some("cneg"), [x]) => {
                let inner = take!(self.valued(x, scope, facts)?);
                let moved = self.b.ap(
                    "negeqd",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &inner.canon},
                    &[&inner.proof],
                );
                (t!(&inner.canon, "cneg"), moved)
            }
            (Some("co"), [x, y, op]) => {
                let left = take!(self.valued(x, scope, facts)?);
                let right = take!(self.valued(y, scope, facts)?);
                let Some(how) = op.label().map(str::to_string) else {
                    return Ok(Route::no("its operation is a letter"));
                };
                let op = self.rpn(op);
                let moved = self.b.ap(
                    "oveq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &left.canon,
                    "C" => self.rpn(y), "D" => &right.canon, "F" => &op},
                    &[&left.proof, &right.proof],
                );
                let written = t!(&left.canon, &right.canon, &op, "co");
                // A quotient and a power are worked from their parts'
                // canons; anything else is an identity of the canons.
                let worked = match how.as_str() {
                    field::DIV => take!(self.quotient(&left, &right, scope, facts)?),
                    field::EXP => take!(self.power(&left, &right, scope, facts)?),
                    _ => take!(self.made_canon(&written, &value, scope, facts)?),
                };
                let joined = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &said, "B" => &written, "C" => &worked.canon},
                    &[&moved, &worked.proof],
                );
                return Ok(Built(Valued {
                    value,
                    canon: worked.canon,
                    proof: joined,
                }));
            }
            _ => {
                return Ok(Route::no(
                    "an operation real arithmetic does not carry through",
                ))
            }
        };
        let worked = take!(self.made_canon(&written, &value, scope, facts)?);
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &said, "B" => &written, "C" => &worked.canon},
            &[&moved, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof: joined,
        }))
    }

    /// ( scope -> written = canon ) for an expression in roots of primes, π,
    /// e and logarithms of primes whose value is `value`.
    pub(super) fn made_canon(
        &mut self,
        written: &Rpn,
        value: &Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let canon = canon(value);
        let proof = if *written == canon {
            self.b
                .ap("eqidd", &binds! {"ph" => scope, "A" => written}, &[])
        } else {
            take!(self.identity(written, &canon, scope, facts)?)
        };
        Ok(Built(Valued {
            value: value.clone(),
            canon,
            proof,
        }))
    }

    /// ( scope -> canon =/= 0 ) for the canon of a value not zero. A
    /// rational one is `arithmetic`'s; any other times its cofactor is its
    /// norm, a rational not zero, so it is not zero itself (`mulne0bad`).
    pub(super) fn surd_apart(
        &mut self,
        canon_of: &Rpn,
        value: &Surd,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        if value.as_rational().is_some() {
            return self
                .numeral_fact(&t!(canon_of, "cc0", "wne"), scope, facts)
                .map(Built);
        }
        let surds::Cofactor { times, norm } = surds::cofactor(value);
        let cofactor = canon(&Real::surd(times));
        let norm = field::spell_rational(&norm);
        let product = t!(canon_of, &cofactor, "cmul", "co");
        let is_norm = take!(self.identity(&product, &norm, scope, facts)?);
        let norm_apart = self.numeral_fact(&t!(&norm, "cc0", "wne"), scope, facts)?;
        let product_apart = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &norm, "C" => "cc0"},
            &[&is_norm, &norm_apart],
        );
        let value_cc = take!(self.in_cc(canon_of, scope, facts)?);
        let cofactor_cc = take!(self.in_cc(&cofactor, scope, facts)?);
        Ok(Built(self.b.ap(
            "mulne0bad",
            &binds! {"ph" => scope, "A" => canon_of, "B" => &cofactor},
            &[&value_cc, &cofactor_cc, &product_apart],
        )))
    }

    /// ( scope -> A / B = canon ) for canons A and B, B not zero: B times
    /// the canon of the quotient is A, which is an identity, and `divmuld`
    /// turns that into the quotient.
    pub(super) fn quotient(
        &mut self,
        top: &Valued,
        below: &Valued,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Some(divisor) = below.value.as_surd().filter(|s| !s.is_zero()) else {
            return Ok(Route::no("a division by zero or by an atom"));
        };
        let value = top.value.times(&Real::surd(divisor.recip()));
        let canon = canon(&value);
        let (a, b) = (&top.canon, &below.canon);
        let back =
            take!(self.identity(&t!(b, &canon, "cmul", "co"), a, scope, facts)?);
        let a_cc = take!(self.in_cc(a, scope, facts)?);
        let b_cc = take!(self.in_cc(b, scope, facts)?);
        let canon_cc = take!(self.in_cc(&canon, scope, facts)?);
        let b_apart = take!(self.surd_apart(b, &divisor, scope, facts)?);
        let iff = self.b.ap(
            "divmuld",
            &binds! {"ph" => scope, "A" => a, "B" => b, "C" => &canon},
            &[&a_cc, &b_cc, &canon_cc, &b_apart],
        );
        let proof = self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => t!(t!(a, b, "cdiv", "co"), &canon, "wceq"),
            "ch" => t!(t!(b, &canon, "cmul", "co"), a, "wceq")},
            &[&back, &iff],
        );
        Ok(Built(Valued {
            value,
            canon,
            proof,
        }))
    }

    /// ( scope -> C ^ K = canon ) for a canon C and a whole exponent K:
    /// C¹ is C (`exp1d`) and each power after it is the one before times C
    /// (`expp1d`), brought to its canon before the next, so a power is never
    /// expanded whole. C⁰ is 1 (`exp0d`), and a negative exponent is one
    /// over the power (`expnegd`).
    pub(super) fn power(
        &mut self,
        base: &Valued,
        exponent: &Valued,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Some(k) = exponent
            .value
            .as_surd()
            .and_then(|s| s.as_rational())
            .filter(|k| k.is_integer())
            .and_then(|k| k.to_integer().to_i64())
        else {
            return Ok(Route::no("a power whose exponent is not whole"));
        };
        let c = &base.canon;
        let c_cc = take!(self.in_cc(c, scope, facts)?);
        if k < 0 {
            let Some(base_surd) = base.value.as_surd() else {
                return Ok(Route::no("a power of an atom to an exponent below 0"));
            };
            let m = numerals::spell(k.unsigned_abs());
            let whole = Valued {
                value: Real::rational(Q::from_integer(k.unsigned_abs().into())),
                canon: m.clone(),
                proof: self.b.ap("eqidd", &binds! {"ph" => scope, "A" => &m}, &[]),
            };
            let raised = take!(self.power(base, &whole, scope, facts)?);
            let c_apart = take!(self.surd_apart(c, &base_surd, scope, facts)?);
            let m_z = self.numeral_fact(&t!(&m, "cz", "wcel"), scope, facts)?;
            let turned = self.b.ap(
                "expnegd",
                &binds! {"ph" => scope, "A" => c, "N" => &m},
                &[&c_cc, &c_apart, &m_z],
            );
            let one = Valued {
                value: Real::rational(field::q(1)),
                canon: numeral(1),
                proof: self.b.ap(
                    "eqidd",
                    &binds! {"ph" => scope, "A" => numeral(1)},
                    &[],
                ),
            };
            let over = t!(c, &m, "cexp", "co");
            let carried = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &over, "B" => &raised.canon, "C" => numeral(1), "F" => "cdiv"},
                &[&raised.proof],
            );
            let worked = take!(self.quotient(&one, &raised, scope, facts)?);
            let first = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(c, &exponent.canon, "cexp", "co"),
                "B" => t!(numeral(1), &over, "cdiv", "co"), "C" => t!(numeral(1), &raised.canon, "cdiv", "co")},
                &[&turned, &carried],
            );
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => t!(c, &exponent.canon, "cexp", "co"),
                "B" => t!(numeral(1), &raised.canon, "cdiv", "co"), "C" => &worked.canon},
                &[&first, &worked.proof],
            );
            return Ok(Built(Valued {
                value: worked.value,
                canon: worked.canon,
                proof,
            }));
        }
        if k == 0 {
            let proof = self
                .b
                .ap("exp0d", &binds! {"ph" => scope, "A" => c}, &[&c_cc]);
            return Ok(Built(Valued {
                value: Real::rational(field::q(1)),
                canon: numeral(1),
                proof,
            }));
        }
        let mut proof = self
            .b
            .ap("exp1d", &binds! {"ph" => scope, "A" => c}, &[&c_cc]);
        let mut at = base.value.clone();
        let mut written = c.clone();
        for j in 1..k as u32 {
            let (here, next) = (numeral(j), numeral(j + 1));
            let sum = t!(&here, numeral(1), "caddc", "co");
            let counted = self.numeral_fact(&t!(&next, &sum, "wceq"), scope, facts)?;
            let respelt = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &next, "B" => &sum, "C" => c, "F" => "cexp"},
                &[&counted],
            );
            let here_n0 = self.numeral_fact(&t!(&here, "cn0", "wcel"), scope, facts)?;
            let stepped = self.b.ap(
                "expp1d",
                &binds! {"ph" => scope, "A" => c, "N" => &here},
                &[&c_cc, &here_n0],
            );
            let before = t!(c, &here, "cexp", "co");
            let carried = self.b.ap(
                "oveq1d",
                &binds! {"ph" => scope, "A" => &before, "B" => &written, "C" => c, "F" => "cmul"},
                &[&proof],
            );
            at = at.times(&base.value);
            let product = t!(&written, c, "cmul", "co");
            let worked = take!(self.made_canon(&product, &at, scope, facts)?);
            let raised = t!(c, &next, "cexp", "co");
            let mut chain = respelt;
            for (from, to, link) in [
                (
                    t!(c, &sum, "cexp", "co"),
                    t!(&before, c, "cmul", "co"),
                    stepped,
                ),
                (t!(&before, c, "cmul", "co"), product.clone(), carried),
                (product.clone(), worked.canon.clone(), worked.proof),
            ] {
                chain = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &raised, "B" => &from, "C" => &to},
                    &[&chain, &link],
                );
            }
            proof = chain;
            written = worked.canon;
        }
        Ok(Built(Valued {
            value: at,
            canon: written,
            proof,
        }))
    }

    /// ( scope -> √x = c·(√p₁·(√p₂·…)) ) for a closed x whose value r is a
    /// rational of at least 0, where r = c²·(p₁·(p₂·…)): x is that product
    /// by arithmetic, the root of a product is the product of the roots
    /// (`sqrtmuld`), and the root of c² is c (`sqrtsqd`). That is the canon
    /// of the root.
    pub(super) fn root_piece(
        &mut self,
        t: &Term,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let Built(surds::Value::Exact(v)) = surds::closed_value(x) else {
            return Ok(Route::no("a root of a number with no value"));
        };
        let Some(r) = v.as_rational() else {
            return Ok(Route::no("a root of a number that is not rational"));
        };
        let Ok(root) = surds::root_of(&r) else {
            return Ok(Route::no("a root real arithmetic does not take"));
        };
        let c = field::spell_rational(&root.coefficient);
        let square = t!(&c, numeral(2), "cexp", "co");
        let primes = product_of_primes(&root.primes);
        let radicand = match &primes {
            None => square.clone(),
            Some(m) => t!(&square, m, "cmul", "co"),
        };
        // The radicand may hold roots of its own, √(√4), so it is valued as
        // any closed term is, and its canon, a numeral, is the product.
        let sx = self.rpn(x);
        let inner = take!(self.valued(x, scope, facts)?);
        let product =
            self.numeral_fact(&t!(&inner.canon, &radicand, "wceq"), scope, facts)?;
        let is = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &radicand},
            &[&inner.proof, &product],
        );
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &radicand, "F" => "csqrt"},
            &[&is],
        );
        let root_of = |r: &Rpn| t!(r, "csqrt", "cfv");
        let c_real = self.numeral_fact(&t!(&c, "cr", "wcel"), scope, facts)?;
        let c_above = self.numeral_fact(&t!("cc0", &c, "cle", "wbr"), scope, facts)?;
        let unsquared = self.b.ap(
            "sqrtsqd",
            &binds! {"ph" => scope, "A" => &c},
            &[&c_real, &c_above],
        );
        let (expression, valued) = match &primes {
            None => (c.clone(), unsquared),
            Some(m) => {
                let square_real =
                    self.numeral_fact(&t!(&square, "cr", "wcel"), scope, facts)?;
                let square_above =
                    self.numeral_fact(&t!("cc0", &square, "cle", "wbr"), scope, facts)?;
                let m_real = self.numeral_fact(&t!(m, "cr", "wcel"), scope, facts)?;
                let m_above =
                    self.numeral_fact(&t!("cc0", m, "cle", "wbr"), scope, facts)?;
                let apart = self.b.ap(
                    "sqrtmuld",
                    &binds! {"ph" => scope, "A" => &square, "B" => m},
                    &[&square_real, &square_above, &m_real, &m_above],
                );
                let first = self.b.ap(
                    "oveq1d",
                    &binds! {"ph" => scope, "A" => root_of(&square), "B" => &c, "C" => root_of(m), "F" => "cmul"},
                    &[&unsquared],
                );
                let (roots, split) = self.split_root(&root.primes, scope, facts)?;
                let second = self.b.ap(
                    "oveq2d",
                    &binds! {"ph" => scope, "A" => root_of(m), "B" => &roots, "C" => &c, "F" => "cmul"},
                    &[&split],
                );
                let both = t!(root_of(&square), root_of(m), "cmul", "co");
                let halfway = t!(&c, root_of(m), "cmul", "co");
                let expression = t!(&c, &roots, "cmul", "co");
                let one = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => root_of(&radicand), "B" => &both, "C" => &halfway},
                    &[&apart, &first],
                );
                let two = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => root_of(&radicand), "B" => &halfway, "C" => &expression},
                    &[&one, &second],
                );
                (expression, two)
            }
        };
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&sx), "B" => root_of(&radicand), "C" => &expression},
            &[&carried, &valued],
        );
        // A root with a whole coefficient is written as its canon; one over a
        // denominator, √(1/2) = 1/2·√2, is brought to (1·√2)/2.
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&sx), "B" => &expression, "C" => &worked.canon},
            &[&proof, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof: joined,
        }))
    }

    /// The logarithm of a positive rational r = Π p^nₚ: r is that product of
    /// powers by arithmetic, carried under the logarithm (`fveq2d`), and the
    /// logarithm of the product is Σ nₚ·ln p (`ln_product`); ln 1 is 0
    /// (`log1`).
    pub(super) fn ln_rational(
        &mut self,
        ratio: &Q,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Logarithm>> {
        let spelt = field::spell_rational(ratio);
        let Ok(factors) = reals::factored(ratio) else {
            return Ok(Route::no("a ratio too large to factor"));
        };
        let powers: Vec<Rpn> = factors
            .iter()
            .filter(|(_, n)| **n != 0)
            .map(|(p, n)| {
                let exponent = numerals::spell_integer(&BigInt::from(*n));
                t!(numerals::spell(*p), exponent, "cexp", "co")
            })
            .collect();
        if powers.is_empty() {
            let proof = self.closed_law(
                &t!(t!("c1", "clog", "cfv"), "cc0", "wceq"),
                "log1",
                scope,
            );
            return Ok(Built(Logarithm {
                ratio: spelt,
                expression: numeral(0),
                proof,
            }));
        }
        let product = take!(self.ln_product(&factors, scope, facts)?);
        let is =
            self.numeral_fact(&t!(&spelt, &product.product, "wceq"), scope, facts)?;
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &spelt, "B" => &product.product, "F" => "clog"},
            &[&is],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => t!(&spelt, "clog", "cfv"),
            "B" => t!(&product.product, "clog", "cfv"), "C" => &product.expression},
            &[&carried, &product.logged],
        );
        Ok(Built(Logarithm {
            ratio: spelt,
            expression: product.expression,
            proof,
        }))
    }

    /// p₁^n₁·p₂^n₂·…, multiplied from the left, with its logarithm
    /// n₁·ln p₁ + n₂·ln p₂ + …: the logarithm of a product of positive reals
    /// is the sum of theirs (`relogmuld`), and of a power to a whole
    /// exponent the exponent times it (`relogexp`).
    pub(super) fn ln_product(
        &mut self,
        factors: &std::collections::BTreeMap<u64, i64>,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<LoggedProduct>> {
        let mut out: Option<LoggedProduct> = None;
        for (p, n) in factors.iter().filter(|(_, n)| **n != 0) {
            let prime = numerals::spell(*p);
            let exponent = numerals::spell_integer(&BigInt::from(*n));
            let power = t!(&prime, &exponent, "cexp", "co");
            let prime_rp = self.positive(&prime, scope, facts)?;
            let exponent_z =
                self.numeral_fact(&t!(&exponent, "cz", "wcel"), scope, facts)?;
            let positive = self.b.ap(
                "rpexpcld",
                &binds! {"ph" => scope, "A" => &prime, "N" => &exponent},
                &[&prime_rp, &exponent_z],
            );
            let ln_p = t!(&prime, "clog", "cfv");
            let expression = t!(&exponent, &ln_p, "cmul", "co");
            let law =
                self.b
                    .ap("relogexp", &binds! {"A" => &prime, "N" => &exponent}, &[]);
            let logged = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(&prime, "crp", "wcel"), "ch" => t!(&exponent, "cz", "wcel"),
                "th" => t!(t!(&power, "clog", "cfv"), &expression, "wceq")},
                &[&prime_rp, &exponent_z, &law],
            );
            let this = LoggedProduct {
                product: power,
                expression,
                logged,
                positive,
            };
            out = Some(match out {
                None => this,
                Some(before) => {
                    let product = t!(&before.product, &this.product, "cmul", "co");
                    let split = self.b.ap(
                        "relogmuld",
                        &binds! {"ph" => scope, "A" => &before.product, "B" => &this.product},
                        &[&before.positive, &this.positive],
                    );
                    let carried = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => t!(&before.product, "clog", "cfv"), "B" => &before.expression,
                        "C" => t!(&this.product, "clog", "cfv"), "D" => &this.expression, "F" => "caddc"},
                        &[&before.logged, &this.logged],
                    );
                    let expression =
                        t!(&before.expression, &this.expression, "caddc", "co");
                    let logged = self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => t!(&product, "clog", "cfv"),
                        "B" => t!(t!(&before.product, "clog", "cfv"), t!(&this.product, "clog", "cfv"), "caddc", "co"),
                        "C" => &expression},
                        &[&split, &carried],
                    );
                    let positive = self.b.ap(
                        "rpmulcld",
                        &binds! {"ph" => scope, "A" => &before.product, "B" => &this.product},
                        &[&before.positive, &this.positive],
                    );
                    LoggedProduct {
                        product,
                        expression,
                        logged,
                        positive,
                    }
                }
            });
        }
        Ok(match out {
            Some(done) => Built(done),
            None => Route::no("a product of no primes"),
        })
    }

    /// ( scope -> ( log ` x ) = canon ) for x of value q·eᵏ: x is q·eᵏ
    /// written so, ln(q·eᵏ) = ln q + ln(eᵏ) (`relogmuld`), ln q is worked out
    /// (`ln_rational`), and ln(eᵏ) = k·ln e = k·1 (`relogexp`, `loge`).
    pub(super) fn ln_piece(
        &mut self,
        t: &Term,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some((ratio, k)) = inner.value.rational_times_e() else {
            return Ok(Route::no("a logarithm of a number not q·eᵏ"));
        };
        let sx = self.rpn(x);
        let log = |r: &Rpn| t!(r, "clog", "cfv");
        let rational = take!(self.ln_rational(&ratio, scope, facts)?);
        // x is the ratio times eᵏ, as the logarithm takes it apart.
        let (written, is) = if k == 0 {
            (rational.ratio.clone(), inner.proof)
        } else {
            let power = match k {
                1 => t!("ceu"),
                _ => t!("ceu", numeral(k), "cexp", "co"),
            };
            let written = t!(&rational.ratio, &power, "cmul", "co");
            let same = take!(self.identity(&inner.canon, &written, scope, facts)?);
            let is = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &written},
                &[&inner.proof, &same],
            );
            (written, is)
        };
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => "clog"},
            &[&is],
        );
        let (expression, logged) = if k == 0 {
            (rational.expression, rational.proof)
        } else {
            let power = match k {
                1 => t!("ceu"),
                _ => t!("ceu", numeral(k), "cexp", "co"),
            };
            let e_rp = self.closed_law(&t!("ceu", "crp", "wcel"), "epr", scope);
            let k_spelt = numeral(k);
            let k_z = self.numeral_fact(&t!(&k_spelt, "cz", "wcel"), scope, facts)?;
            let power_rp = if k == 1 {
                e_rp.clone()
            } else {
                self.b.ap(
                    "rpexpcld",
                    &binds! {"ph" => scope, "A" => "ceu", "N" => &k_spelt},
                    &[&e_rp, &k_z],
                )
            };
            let ratio_rp = self.positive(&rational.ratio, scope, facts)?;
            let split = self.b.ap(
                "relogmuld",
                &binds! {"ph" => scope, "A" => &rational.ratio, "B" => &power},
                &[&ratio_rp, &power_rp],
            );
            let one = t!("c1");
            let log_e =
                self.closed_law(&t!(log(&t!("ceu")), &one, "wceq"), "loge", scope);
            let (e_part, e_logged) = if k == 1 {
                (one.clone(), log_e)
            } else {
                let law =
                    self.b
                        .ap("relogexp", &binds! {"A" => "ceu", "N" => &k_spelt}, &[]);
                let times_log = t!(&k_spelt, log(&t!("ceu")), "cmul", "co");
                let down = self.b.ap(
                    "syl2anc",
                    &binds! {"ph" => scope, "ps" => t!("ceu", "crp", "wcel"), "ch" => t!(&k_spelt, "cz", "wcel"),
                    "th" => t!(log(&power), &times_log, "wceq")},
                    &[&e_rp, &k_z, &law],
                );
                let times_one = t!(&k_spelt, &one, "cmul", "co");
                let to_one = self.b.ap(
                    "oveq2d",
                    &binds! {"ph" => scope, "A" => log(&t!("ceu")), "B" => &one, "C" => &k_spelt, "F" => "cmul"},
                    &[&log_e],
                );
                let joined = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => log(&power), "B" => &times_log, "C" => &times_one},
                    &[&down, &to_one],
                );
                (times_one, joined)
            };
            let expression = t!(&rational.expression, &e_part, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => log(&rational.ratio), "B" => &rational.expression,
                "C" => log(&power), "D" => &e_part, "F" => "caddc"},
                &[&rational.proof, &e_logged],
            );
            let logged = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => log(&written),
                "B" => t!(log(&rational.ratio), log(&power), "caddc", "co"), "C" => &expression},
                &[&split, &both],
            );
            (expression, logged)
        };
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => log(&sx), "B" => log(&written), "C" => &expression},
            &[&carried, &logged],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => log(&sx), "B" => &expression, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( exp ` x ) = canon ) for x of value k + Σ nₚ·ln p: with r
    /// = Π p^nₚ, x is k + ln r, exp(k + ln r) = exp k · exp(ln r) (`efadd`),
    /// exp(ln r) = r (`reeflogd`), and exp k = (exp 1)ᵏ = eᵏ (`efexp`,
    /// `df-e`); exp 0 is 1 (`ef0`).
    pub(super) fn exp_piece(
        &mut self,
        t: &Term,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some(reals::Logarithmic { constant, logs }) = inner.value.logarithmic()
        else {
            return Ok(Route::no("an exponential of a number not k + Σ nₚ·ln p"));
        };
        let Some(k) = constant
            .to_integer()
            .to_u32()
            .filter(|_| constant.is_integer())
        else {
            return Ok(Route::no(
                "an exponential of a number whose rational part is not whole",
            ));
        };
        let mut ratio = field::q(1);
        for (p, n) in &logs {
            let n = n.to_integer().to_i32().unwrap_or(0);
            ratio *= Q::from_integer(BigInt::from(*p)).pow(n);
        }
        let sx = self.rpn(x);
        let exp = |r: &Rpn| t!(r, "ce", "cfv");
        let k_spelt = numeral(k);
        // x as k + ln r, or the one of them it holds.
        let rational = if logs.is_empty() {
            None
        } else {
            Some(take!(self.ln_rational(&ratio, scope, facts)?))
        };
        let (written, is) = match &rational {
            None => (k_spelt.clone(), inner.proof.clone()),
            Some(l) => {
                let as_logs = if k == 0 {
                    l.expression.clone()
                } else {
                    t!(&k_spelt, &l.expression, "caddc", "co")
                };
                let written = if k == 0 {
                    t!(&l.ratio, "clog", "cfv")
                } else {
                    t!(&k_spelt, t!(&l.ratio, "clog", "cfv"), "caddc", "co")
                };
                let same =
                    take!(self.identity(&inner.canon, &as_logs, scope, facts)?);
                let back = self.b.ap(
                    "eqcomd",
                    &binds! {"ph" => scope, "A" => t!(&l.ratio, "clog", "cfv"), "B" => &l.expression},
                    &[&l.proof],
                );
                let folded = if k == 0 {
                    back
                } else {
                    self.b.ap(
                        "oveq2d",
                        &binds! {"ph" => scope, "A" => &l.expression, "B" => t!(&l.ratio, "clog", "cfv"),
                        "C" => &k_spelt, "F" => "caddc"},
                        &[&back],
                    )
                };
                let first = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &as_logs},
                    &[&inner.proof, &same],
                );
                let is = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &sx, "B" => &as_logs, "C" => &written},
                    &[&first, &folded],
                );
                (written, is)
            }
        };
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => "ce"},
            &[&is],
        );
        // exp k = eᵏ, and exp 0 = 1.
        let power = match k {
            0 => t!("c1"),
            1 => t!("ceu"),
            _ => t!("ceu", &k_spelt, "cexp", "co"),
        };
        let exp_k = if k == 0 {
            self.closed_law(&t!(exp(&t!("cc0")), "c1", "wceq"), "ef0", scope)
        } else {
            self.exp_whole(&k_spelt, &power, scope, facts)?
        };
        let (expression, valued) = match &rational {
            None => (power.clone(), exp_k),
            Some(l) => {
                let r_rp = self.positive(&l.ratio, scope, facts)?;
                let back = self.b.ap(
                    "reeflogd",
                    &binds! {"ph" => scope, "A" => &l.ratio},
                    &[&r_rp],
                );
                if k == 0 {
                    (l.ratio.clone(), back)
                } else {
                    let log_r = t!(&l.ratio, "clog", "cfv");
                    let k_cc =
                        self.numeral_fact(&t!(&k_spelt, "cc", "wcel"), scope, facts)?;
                    let log_real = self.b.ap(
                        "relogcld",
                        &binds! {"ph" => scope, "A" => &l.ratio},
                        &[&r_rp],
                    );
                    let log_cc = self.b.ap(
                        "recnd",
                        &binds! {"ph" => scope, "A" => &log_r},
                        &[&log_real],
                    );
                    let law = self.b.ap(
                        "efadd",
                        &binds! {"A" => &k_spelt, "B" => &log_r},
                        &[],
                    );
                    let split = self.b.ap(
                        "syl2anc",
                        &binds! {"ph" => scope, "ps" => t!(&k_spelt, "cc", "wcel"), "ch" => t!(&log_r, "cc", "wcel"),
                        "th" => t!(exp(&written), t!(exp(&k_spelt), exp(&log_r), "cmul", "co"), "wceq")},
                        &[&k_cc, &log_cc, &law],
                    );
                    let both = self.b.ap(
                        "oveq12d",
                        &binds! {"ph" => scope, "A" => exp(&k_spelt), "B" => &power,
                        "C" => exp(&log_r), "D" => &l.ratio, "F" => "cmul"},
                        &[&exp_k, &back],
                    );
                    let expression = t!(&power, &l.ratio, "cmul", "co");
                    let joined = self.b.ap(
                        "eqtrd",
                        &binds! {"ph" => scope, "A" => exp(&written),
                        "B" => t!(exp(&k_spelt), exp(&log_r), "cmul", "co"), "C" => &expression},
                        &[&split, &both],
                    );
                    (expression, joined)
                }
            }
        };
        let worked = take!(self.made_canon(&expression, &value, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(&sx), "B" => exp(&written), "C" => &expression},
            &[&carried, &valued],
        );
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(&sx), "B" => &expression, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( exp ` k ) = e^k ) for a whole k of at least 1: k is k·1,
    /// exp(k·1) = (exp 1)ᵏ (`efexp`), and exp 1 is e (`df-e`).
    pub(super) fn exp_whole(
        &mut self,
        k: &Rpn,
        power: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let exp = |r: &Rpn| t!(r, "ce", "cfv");
        let one = t!("c1");
        let times_one = t!(k, &one, "cmul", "co");
        let counted = self.numeral_fact(&t!(k, &times_one, "wceq"), scope, facts)?;
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => k, "B" => &times_one, "F" => "ce"},
            &[&counted],
        );
        let one_cc = self.numeral_fact(&t!(&one, "cc", "wcel"), scope, facts)?;
        let k_z = self.numeral_fact(&t!(k, "cz", "wcel"), scope, facts)?;
        let law = self.b.ap("efexp", &binds! {"A" => &one, "N" => k}, &[]);
        let raised = t!(exp(&one), k, "cexp", "co");
        let grown = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(&one, "cc", "wcel"), "ch" => t!(k, "cz", "wcel"),
            "th" => t!(exp(&times_one), &raised, "wceq")},
            &[&one_cc, &k_z, &law],
        );
        // e is exp 1, by its definition, turned.
        let defined = self.b.ap(
            "eqcomi",
            &binds! {"A" => "ceu", "B" => exp(&one)},
            &[&self.step("df-e")],
        );
        let named = self.b.ap(
            "a1i",
            &binds! {"ph" => t!(exp(&one), "ceu", "wceq"), "ps" => scope},
            &[&defined],
        );
        let e_power = t!("ceu", k, "cexp", "co");
        let to_e = self.b.ap(
            "oveq1d",
            &binds! {"ph" => scope, "A" => exp(&one), "B" => "ceu", "C" => k, "F" => "cexp"},
            &[&named],
        );
        let first = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => exp(&times_one), "C" => &raised},
            &[&carried, &grown],
        );
        let to_power = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => &raised, "C" => &e_power},
            &[&first, &to_e],
        );
        if *power == e_power {
            return Ok(to_power);
        }
        // e¹ is written e.
        let e_cc = self.closed_law(&t!("ceu", "cr", "wcel"), "ere", scope);
        let e_cc = self
            .b
            .ap("recnd", &binds! {"ph" => scope, "A" => "ceu"}, &[&e_cc]);
        let unit = self
            .b
            .ap("exp1d", &binds! {"ph" => scope, "A" => "ceu"}, &[&e_cc]);
        Ok(self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => exp(k), "B" => &e_power, "C" => power},
            &[&to_power, &unit],
        ))
    }

    /// ( scope -> canon =/= 0 ) for the canon of D = Σ qₚ·ln p, rational
    /// multiples of logarithms of primes and not all 0. With N the least
    /// whole number making each N·qₚ whole and r = Π p^(N·qₚ), D·N is ln r
    /// (an identity, and `ln_rational`), ln r ≠ 0 as r ≠ 1 (`logne0`), and
    /// so D ≠ 0 (`mulne0bad`).
    pub(super) fn ln_apart(
        &mut self,
        canon_of: &Rpn,
        value: &Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let Some(reals::Logarithmic { logs, .. }) = value.logarithmic() else {
            return Ok(Route::no("a difference that is not logarithms of primes"));
        };
        let Ok(reals::LogarithmRatio { scale, ratio }) = reals::logarithm_ratio(&logs)
        else {
            return Ok(Route::no("a multiple of a logarithm too large"));
        };
        let logged = take!(self.ln_rational(&ratio, scope, facts)?);
        let n = numerals::spell(scale.magnitude().clone());
        let product = t!(canon_of, &n, "cmul", "co");
        let is = take!(self.identity(&product, &logged.expression, scope, facts)?);
        let log_r = t!(&logged.ratio, "clog", "cfv");
        let back = self.b.ap(
            "eqcomd",
            &binds! {"ph" => scope, "A" => &log_r, "B" => &logged.expression},
            &[&logged.proof],
        );
        let is_log = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &logged.expression, "C" => &log_r},
            &[&is, &back],
        );
        let r_rp = self.positive(&logged.ratio, scope, facts)?;
        let r_apart =
            self.numeral_fact(&t!(&logged.ratio, "c1", "wne"), scope, facts)?;
        let law = self.b.ap("logne0", &binds! {"A" => &logged.ratio}, &[]);
        let log_apart = self.b.ap(
            "syl2anc",
            &binds! {"ph" => scope, "ps" => t!(&logged.ratio, "crp", "wcel"), "ch" => t!(&logged.ratio, "c1", "wne"),
            "th" => t!(&log_r, "cc0", "wne")},
            &[&r_rp, &r_apart, &law],
        );
        let product_apart = self.b.ap(
            "eqnetrd",
            &binds! {"ph" => scope, "A" => &product, "B" => &log_r, "C" => "cc0"},
            &[&is_log, &log_apart],
        );
        let value_cc = take!(self.in_cc(canon_of, scope, facts)?);
        let n_cc = self.numeral_fact(&t!(&n, "cc", "wcel"), scope, facts)?;
        Ok(Built(self.b.ap(
            "mulne0bad",
            &binds! {"ph" => scope, "A" => canon_of, "B" => &n},
            &[&value_cc, &n_cc, &product_apart],
        )))
    }

    /// ( scope -> ( f ` x ) = canon ) for f sine or cosine and x of value
    /// q·π: with q = 2k + r, 0 ≤ r < 2, x is a(r) + k·(2·π), or a(r) where k
    /// is 0 (`angle_form`), by an identity; a turn is taken off (`sinper`,
    /// `cosper`), the rest reduced to set.mm's values (`trig_reduced`), and
    /// what a value lemma says brought to the canon.
    pub(super) fn trig_piece(
        &mut self,
        t: &Term,
        f: reals::Trig,
        value: Real,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let inner = take!(self.valued(x, scope, facts)?);
        let Some(multiple) = reals::multiple_of_pi(&inner.value) else {
            return Ok(Route::no("an angle that is not a multiple of π"));
        };
        let r = reals::turned(&multiple);
        let turns = ((&multiple - &r) / field::q(2)).to_integer();
        let Some(turns) = turns.to_i64() else {
            return Ok(Route::no("an angle of too many turns"));
        };
        let label = trig_label(f);
        let apply = |a: &Rpn| t!(a, label, "cfv");
        let base = angle_form(&r);
        let written = if turns == 0 {
            base.clone()
        } else {
            t!(
                &base,
                t!(
                    numerals::spell_integer(&BigInt::from(turns)),
                    t!("c2", "cpi", "cmul", "co"),
                    "cmul",
                    "co"
                ),
                "caddc",
                "co"
            )
        };
        let sx = self.rpn(x);
        let same = if inner.canon == written {
            self.b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &written}, &[])
        } else {
            take!(self.identity(&inner.canon, &written, scope, facts)?)
        };
        let is = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => &sx, "B" => &inner.canon, "C" => &written},
            &[&inner.proof, &same],
        );
        let carried = self.b.ap(
            "fveq2d",
            &binds! {"ph" => scope, "A" => &sx, "B" => &written, "F" => label},
            &[&is],
        );
        // A turn taken off.
        let at_base = if turns == 0 {
            carried
        } else {
            let base_cc = take!(self.in_cc(&base, scope, facts)?);
            let k = numerals::spell_integer(&BigInt::from(turns));
            let k_z = self.numeral_fact(&t!(&k, "cz", "wcel"), scope, facts)?;
            let periodic = match f {
                reals::Trig::Sine => "sinper",
                reals::Trig::Cosine => "cosper",
            };
            let law = self.b.ap(periodic, &binds! {"A" => &base, "K" => &k}, &[]);
            let turned = self.b.ap(
                "syl2anc",
                &binds! {"ph" => scope, "ps" => t!(&base, "cc", "wcel"), "ch" => t!(&k, "cz", "wcel"),
                "th" => t!(apply(&written), apply(&base), "wceq")},
                &[&base_cc, &k_z, &law],
            );
            self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => apply(&sx), "B" => apply(&written), "C" => apply(&base)},
                &[&carried, &turned],
            )
        };
        let (said, reduced) = take!(self.trig_reduced(f, &r, scope, facts)?);
        let reached = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(&sx), "B" => apply(&base), "C" => &said},
            &[&at_base, &reduced],
        );
        let worked = take!(self.valued(&self.to_term(&said), scope, facts)?);
        let proof = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(&sx), "B" => &said, "C" => &worked.canon},
            &[&reached, &worked.proof],
        );
        debug_assert_eq!(
            worked.value, value,
            "the reduction comes to the decider's value"
        );
        Ok(Built(Valued {
            value,
            canon: worked.canon,
            proof,
        }))
    }

    /// ( scope -> ( f ` a(r) ) = v ) for 0 ≤ r < 2 and v what set.mm's lemmas
    /// say: a π taken off (`sinppi`, `cosppi`), then π/2 (`sinhalfpip`,
    /// `coshalfpip`), and the value at 0, π/6, π/4 or π/3 (`sin0`, `cos0`,
    /// `sincos6thpi`, `sincos4thpi`, `sincos3rdpi`).
    pub(super) fn trig_reduced(
        &mut self,
        f: reals::Trig,
        r: &Q,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<(Rpn, Proof)>> {
        let half = Q::new(BigInt::from(1), BigInt::from(2));
        let apply = |g: reals::Trig, a: &Rpn| t!(a, trig_label(g), "cfv");
        let angle = angle_form(r);
        // A π or a π/2 off: the lemma, the function and angle it leaves, and
        // whether it negates.
        let step = if *r >= field::q(1) {
            let rest = r - field::q(1);
            let lemma = match f {
                Sine => "sinppi",
                Cosine => "cosppi",
            };
            Some((lemma, f, rest, true))
        } else if *r >= half {
            let rest = r - &half;
            match f {
                Sine => Some(("sinhalfpip", Cosine, rest, false)),
                Cosine => Some(("coshalfpip", Sine, rest, true)),
            }
        } else {
            None
        };
        let Some((lemma, then, rest, negates)) = step else {
            return Ok(Built(self.trig_base(f, r, scope)));
        };
        let left = angle_form(&rest);
        let left_cc = take!(self.in_cc(&left, scope, facts)?);
        let shifted = if negates {
            t!(apply(then, &left), "cneg")
        } else {
            apply(then, &left)
        };
        let law = self.b.ap(lemma, &binds! {"A" => &left}, &[]);
        let moved = self.b.ap(
            "syl",
            &binds! {"ph" => scope, "ps" => t!(&left, "cc", "wcel"), "ch" => t!(apply(f, &angle), &shifted, "wceq")},
            &[&left_cc, &law],
        );
        let (below, proof) = take!(self.trig_reduced(then, &rest, scope, facts)?);
        let (said, carried) = if negates {
            let carried = self.b.ap(
                "negeqd",
                &binds! {"ph" => scope, "A" => apply(then, &left), "B" => &below},
                &[&proof],
            );
            (t!(&below, "cneg"), carried)
        } else {
            (below, proof)
        };
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => apply(f, &angle), "B" => &shifted, "C" => &said},
            &[&moved, &carried],
        );
        Ok(Built((said, joined)))
    }

    /// ( scope -> ( f ` a ) = v ) for a = 0, π/6, π/4 or π/3, from set.mm's
    /// statement of the value, the one of its two halves that names f.
    pub(super) fn trig_base(
        &mut self,
        f: reals::Trig,
        r: &Q,
        scope: &Rpn,
    ) -> (Rpn, Proof) {
        let apply = |g: reals::Trig, a: &Rpn| t!(a, trig_label(g), "cfv");
        let over = |top: Rpn, d: &str| t!(top, d, "cdiv", "co");
        let root = |p: &str| t!(p, "csqrt", "cfv");
        let twelfths = (r * field::q(12)).to_integer().to_i64().unwrap_or(-1);
        let angle = angle_form(r);
        if twelfths == 0 {
            let (value, label) = match f {
                Sine => (t!("cc0"), "sin0"),
                Cosine => (t!("c1"), "cos0"),
            };
            let proof =
                self.closed_law(&t!(apply(f, &angle), &value, "wceq"), label, scope);
            return (value, proof);
        }
        let (label, sine, cosine) = match twelfths {
            2 => ("sincos6thpi", over(t!("c1"), "c2"), over(root("c3"), "c2")),
            // set.mm writes both values at π/4 as 1/√2.
            3 => (
                "sincos4thpi",
                t!("c1", root("c2"), "cdiv", "co"),
                t!("c1", root("c2"), "cdiv", "co"),
            ),
            _ => ("sincos3rdpi", over(root("c3"), "c2"), over(t!("c1"), "c2")),
        };
        let first = t!(apply(Sine, &angle), &sine, "wceq");
        let second = t!(apply(Cosine, &angle), &cosine, "wceq");
        let value = match f {
            Sine => sine,
            Cosine => cosine,
        };
        let proof = self.closed_half([first, second], label, f == Cosine, scope);
        (value, proof)
    }

    /// ( scope -> √(p₁·(p₂·…)) = √p₁·(√p₂·…) ), and the right side.
    pub(super) fn split_root(
        &mut self,
        primes: &[u64],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<(Rpn, Proof)> {
        let product = product_of_primes(primes).expect("a root of at least one prime");
        let root_of = |r: &Rpn| t!(r, "csqrt", "cfv");
        let [first, rest @ ..] = primes else {
            unreachable!("a root of at least one prime");
        };
        if rest.is_empty() {
            let same = self.b.ap(
                "eqidd",
                &binds! {"ph" => scope, "A" => root_of(&product)},
                &[],
            );
            return Ok((root_of(&product), same));
        }
        let head = numerals::spell(*first);
        let tail = product_of_primes(rest).expect("at least one prime is left");
        let mut held = Vec::new();
        for claim in [
            t!(&head, "cr", "wcel"),
            t!("cc0", &head, "cle", "wbr"),
            t!(&tail, "cr", "wcel"),
            t!("cc0", &tail, "cle", "wbr"),
        ] {
            held.push(self.numeral_fact(&claim, scope, facts)?);
        }
        let apart = self.b.ap(
            "sqrtmuld",
            &binds! {"ph" => scope, "A" => &head, "B" => &tail},
            &[&held[0], &held[1], &held[2], &held[3]],
        );
        let (roots, split) = self.split_root(rest, scope, facts)?;
        let carried = self.b.ap(
            "oveq2d",
            &binds! {"ph" => scope, "A" => root_of(&tail), "B" => &roots, "C" => root_of(&head), "F" => "cmul"},
            &[&split],
        );
        let whole = t!(root_of(&head), &roots, "cmul", "co");
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => root_of(&product), "B" => t!(root_of(&head), root_of(&tail), "cmul", "co"), "C" => &whole},
            &[&apart, &carried],
        );
        Ok((whole, joined))
    }

    /// ( scope -> left = right ) for two expressions whose only atoms are
    /// square roots of primes and which are equal: d·left − d·right, for d
    /// the least whole number that makes its coefficients whole, is a sum
    /// of whole multiples of (√p)² − p, each zero, and the normaliser shows
    /// the sum is the difference; d is cancelled (`mulcanad`). The
    /// multiples are whole so that the normaliser adds no fractions.
    pub(super) fn identity(
        &mut self,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let read = |me: &Self, r: &Rpn| field::read(&me.to_term(r), &labels);
        let difference = read(self, left).minus(&read(self, right));
        let Some(under) = difference.under.constant_value().filter(|u| !u.is_zero())
        else {
            return Ok(Route::no("a divisor that is not a number"));
        };
        let exact = difference.over.scaled(&under.recip());
        let scale = field::common_denominator(exact.terms.values());
        let mut rest = exact.scaled(&Q::from_integer(scale.clone()));
        let mut by: IndexMap<Rpn, Multiplier> = IndexMap::new();
        while let Some(found) = reducible(&rest, self) {
            rest.terms.shift_remove(&found.monomial);
            let lowered = lowered(&found.monomial, &found.root);
            let one = Poly::new(IndexMap::from([(lowered, found.weight)]));
            let entry = by.entry(found.root.clone()).or_insert_with(|| Multiplier {
                root: found.root.clone(),
                prime: found.prime,
                times: Poly::default(),
            });
            entry.times = entry.times.plus(&one);
            rest = rest.plus(&one.scaled(&field::q(found.prime as i64)));
        }
        if !rest.zero() {
            return Ok(Route::no("the two sides are not one value"));
        }
        let mut w = Work::plain(scope, facts);
        if by.is_empty() {
            return self.same_polynomial(&mut w, left, right);
        }
        let mut pieces: Vec<Vanishing> = Vec::new();
        for m in by.values() {
            let prime = numerals::spell(m.prime);
            let squared = t!(&m.root, numeral(2), "cexp", "co");
            let gap = t!(&squared, &prime, "cmin", "co");
            let prime_cc =
                self.numeral_fact(&t!(&prime, "cc", "wcel"), scope, facts)?;
            let squares = self.b.ap(
                "sqsqrtd",
                &binds! {"ph" => scope, "A" => &prime},
                &[&prime_cc],
            );
            let squared_cc = take!(self.in_cc(&squared, scope, facts)?);
            let turn = self.b.ap(
                "subeq0ad",
                &binds! {"ph" => scope, "A" => &squared, "B" => &prime},
                &[&squared_cc, &prime_cc],
            );
            let vanishes = self.b.ap(
                "mpbird",
                &binds! {"ph" => scope, "ps" => t!(&gap, "cc0", "wceq"), "ch" => t!(&squared, &prime, "wceq")},
                &[&squares, &turn],
            );
            let times = spelt_poly(&m.times);
            let times_cc = self.membership(&times, "cc", scope, facts)?;
            pieces.push(
                self.multiple_vanishing(&gap, &vanishes, &times, &times_cc, scope),
            );
        }
        let Vanishing {
            term: total,
            proof: sums,
        } = self.vanishing_sum(&pieces, scope);
        let scaled =
            (!scale.is_one()).then(|| numerals::spell(scale.magnitude().clone()));
        let (l, r) = match &scaled {
            None => (left.clone(), right.clone()),
            Some(d) => (t!(d, left, "cmul", "co"), t!(d, right, "cmul", "co")),
        };
        let whole = t!(&l, &r, "cmin", "co");
        let alike = take!(self.same_polynomial(&mut w, &total, &whole)?);
        let l_cc = take!(self.in_cc(&l, scope, facts)?);
        let r_cc = take!(self.in_cc(&r, scope, facts)?);
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => &l, "B" => &r},
            &[&l_cc, &r_cc],
        );
        let equal = self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(&whole, "cc0", "wceq"), "ch" => t!(&l, &r, "wceq")},
            &[&reached, &turn],
        );
        let Some(d) = scaled else {
            return Ok(Built(equal));
        };
        let left_cc = take!(self.in_cc(left, scope, facts)?);
        let right_cc = take!(self.in_cc(right, scope, facts)?);
        let d_cc = self.numeral_fact(&t!(&d, "cc", "wcel"), scope, facts)?;
        let d_apart = self.numeral_fact(&t!(&d, "cc0", "wne"), scope, facts)?;
        Ok(Built(self.b.ap(
            "mulcanad",
            &binds! {"ph" => scope, "A" => left, "B" => right, "C" => &d},
            &[&left_cc, &right_cc, &d_cc, &d_apart, &equal],
        )))
    }
}
