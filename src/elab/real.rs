//! `real arithmetic`: closed facts about square roots of rationals, proved.
//!
//! The deciding is `crate::methods::surds`, and a claim is worked out
//! before anything is proved, so what cannot be proved is reported as what
//! it is. A proof takes each side to an expression whose only atoms are
//! square roots of primes (`valued`): the root of a rational is its square
//! part times a product of roots of primes (`root_piece`), and an operation
//! is carried through to what its operands came to. Two such expressions
//! are equal when their difference is a sum of multiples of (√p)² − p, one
//! for each prime (`identity`); the decider works out the multiples, and the
//! normaliser checks that the sum is the difference.

use indexmap::IndexMap;
use num_traits::{Signed, ToPrimitive, Zero};

use super::calculators::Work;
use super::field::{self, numeral, Monomial, Poly, Q};
use super::numerals;
use super::state::Elaborator;
use super::Facts;
use crate::binds;
use crate::corpus::{fmt, Step};
use crate::methods::surds::{self, Value, Verdict};
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked, Declined, Problem, Route};
use crate::{t, take};

/// A term proved equal to an expression whose only atoms are square roots
/// of primes: ( scope -> term = expression ).
struct Valued {
    expression: Rpn,
    proof: Proof,
}

/// The multiple of (√p)² − p that a difference holds, for one prime.
struct Multiplier {
    /// √p, as set.mm spells it.
    root: Rpn,
    prime: u64,
    times: Poly,
}

impl<'a> Elaborator<'a> {
    /// A step citing `real arithmetic`.
    pub fn real_arithmetic(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let what = format!("step {} claims {}", fmt(&step.number), step.claim.text());
        self.real_fact(term, scope, facts, &what).map(Built)
    }

    /// A closed fact about square roots of rationals, worked out and then
    /// proved; `what` says where it was asked, as the page writes it.
    pub fn real_fact(
        &mut self,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        what: &str,
    ) -> Checked<Proof> {
        let goal = self.to_term(term);
        match surds::decide_closed(&goal) {
            Built(Verdict::Holds(true)) => {}
            other => return Err(self.real_unshown(other, what)),
        }
        let known = self.roots_known(&goal, scope, facts)?;
        match self.real_proved(&goal, scope, &known)? {
            Built(p) => Ok(p),
            Declined(d) => Err(self.defect(
                self.at,
                format!(
                    "{what}, which is true, and real arithmetic cannot show it yet: {}",
                    d.reason()
                ),
            )),
        }
    }

    /// The defect for a claim real arithmetic did not find true.
    fn real_unshown(&self, verdict: Route<Verdict>, what: &str) -> Problem {
        let message = match verdict {
            Declined(_) => format!(
                "{what}, which is not a fact about numerals and square roots alone, and real arithmetic decides nothing else"
            ),
            Built(Verdict::Holds(false)) => format!("{what}, which is false"),
            Built(Verdict::Unworked(why)) => format!("{what}, which {why}"),
            Built(Verdict::Undecided(why)) => {
                format!("{what}, which {why}; real arithmetic does not decide it")
            }
            Built(Verdict::Holds(true)) => unreachable!("a true claim is proved"),
        };
        self.defect(self.at, message)
    }

    /// The facts, with √p ∈ ℂ for each prime p under a root of the claim:
    /// what the normaliser asks of each atom it meets.
    fn roots_known(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Facts> {
        let known = facts.copy();
        for p in primes_under(goal) {
            let prime = numerals::spell(p);
            let complex = self.numeral_fact(&t!(&prime, "cc", "wcel"), scope, facts)?;
            let root = root_of_prime(p);
            let held = self.b.ap(
                "sqrtcld",
                &binds! {"ph" => scope, "A" => &prime},
                &[&complex],
            );
            self.know(&known, t!(&root, "cc", "wcel"), held);
        }
        Ok(known)
    }

    /// A fact about numerals alone, which arithmetic proves.
    fn numeral_fact(
        &mut self,
        claim: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Proof> {
        let what = format!("real arithmetic asks {}", self.render(claim));
        self.closed_fact(claim, scope, facts, &what, None)
    }

    /// ( scope -> goal ) for a closed claim real arithmetic found true.
    fn real_proved(
        &mut self,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let kids = goal.children().to_vec();
        match (goal.label(), kids.as_slice()) {
            (Some("wceq"), [a, b]) => {
                let left = take!(self.valued(a, scope, facts)?);
                let right = take!(self.valued(b, scope, facts)?);
                let same = take!(self.identity(
                    &left.expression,
                    &right.expression,
                    scope,
                    facts
                )?);
                let (sa, sb) = (self.rpn(a), self.rpn(b));
                let reached = self.b.ap(
                    "eqtrd",
                    &binds! {"ph" => scope, "A" => &sa, "B" => &left.expression, "C" => &right.expression},
                    &[&left.proof, &same],
                );
                Ok(Built(self.b.ap(
                    "eqtr4d",
                    &binds! {"ph" => scope, "A" => &sa, "B" => &right.expression, "C" => &sb},
                    &[&reached, &right.proof],
                )))
            }
            _ => Ok(Route::no("a relation other than an equation")),
        }
    }

    /// ( scope -> t = e ) for a closed term t and an expression e whose
    /// only atoms are square roots of primes.
    fn valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let said = self.rpn(t);
        if !surds::takes_root(t) {
            // What the normaliser holds as an atom is worked to its value
            // first; anything else it reads as it stands.
            if self.normaliser_opaque(t) {
                let (_, canon, proof) = take!(self.closed_valued(t, scope, facts)?);
                return Ok(Built(Valued {
                    expression: canon,
                    proof,
                }));
            }
            let same = self
                .b
                .ap("eqidd", &binds! {"ph" => scope, "A" => &said}, &[]);
            return Ok(Built(Valued {
                expression: said,
                proof: same,
            }));
        }
        if surds::is_root(t) {
            return self.root_piece(t, scope, facts);
        }
        let kids = t.children().to_vec();
        match (t.label(), kids.as_slice()) {
            (Some("cneg"), [x]) => {
                let inner = take!(self.valued(x, scope, facts)?);
                let moved = self.b.ap(
                    "negeqd",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &inner.expression},
                    &[&inner.proof],
                );
                Ok(Built(Valued {
                    expression: t!(&inner.expression, "cneg"),
                    proof: moved,
                }))
            }
            (Some("co"), [x, y, op]) => {
                let how = op.label().unwrap_or("");
                let left = take!(self.valued(x, scope, facts)?);
                let right = match how {
                    field::EXP | field::DIV => {
                        take!(self.rational_valued(y, scope, facts)?)
                    }
                    _ => take!(self.valued(y, scope, facts)?),
                };
                if how == field::EXP && !whole_at_least_zero(&right.expression) {
                    return Ok(Route::no(
                        "a power whose exponent is not a whole number of at least 0",
                    ));
                }
                let op = self.rpn(op);
                let moved = self.b.ap(
                    "oveq12d",
                    &binds! {"ph" => scope, "A" => self.rpn(x), "B" => &left.expression,
                    "C" => self.rpn(y), "D" => &right.expression, "F" => &op},
                    &[&left.proof, &right.proof],
                );
                Ok(Built(Valued {
                    expression: t!(&left.expression, &right.expression, &op, "co"),
                    proof: moved,
                }))
            }
            _ => Ok(Route::no(
                "an operation real arithmetic does not carry through",
            )),
        }
    }

    /// ( scope -> t = q ) for a closed term t whose value is the rational
    /// q, written plainly: an exponent, or a divisor.
    fn rational_valued(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let Built(Value::Exact(v)) = surds::closed_value(t) else {
            return Ok(Route::no("it has no value"));
        };
        let Some(v) = v.as_rational() else {
            return Ok(Route::no("a divisor or an exponent that is not rational"));
        };
        let canon = spelt_rational(&v);
        let inner = take!(self.valued(t, scope, facts)?);
        if inner.expression == canon {
            return Ok(Built(inner));
        }
        let same = take!(self.identity(&inner.expression, &canon, scope, facts)?);
        let joined = self.b.ap(
            "eqtrd",
            &binds! {"ph" => scope, "A" => self.rpn(t), "B" => &inner.expression, "C" => &canon},
            &[&inner.proof, &same],
        );
        Ok(Built(Valued {
            expression: canon,
            proof: joined,
        }))
    }

    /// ( scope -> √x = c·(√p₁·(√p₂·…)) ) for a closed x whose value r is a
    /// rational of at least 0, where r = c²·(p₁·(p₂·…)): x is that product
    /// by arithmetic, the root of a product is the product of the roots
    /// (`sqrtmuld`), and the root of c² is c (`sqrtsqd`).
    fn root_piece(
        &mut self,
        t: &Term,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Valued>> {
        let x = &t.children()[0];
        let Built(Value::Exact(v)) = surds::closed_value(x) else {
            return Ok(Route::no("a root of a number with no value"));
        };
        let Some(r) = v.as_rational() else {
            return Ok(Route::no("a root of a number that is not rational"));
        };
        let Ok(root) = surds::root_of(&r) else {
            return Ok(Route::no("a root real arithmetic does not take"));
        };
        let c = spelt_rational(&root.coefficient);
        let square = t!(&c, numeral(2), "cexp", "co");
        let primes = product_of_primes(&root.primes);
        let radicand = match &primes {
            None => square.clone(),
            Some(m) => t!(&square, m, "cmul", "co"),
        };
        let sx = self.rpn(x);
        let is = self.numeral_fact(&t!(&sx, &radicand, "wceq"), scope, facts)?;
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
        Ok(Built(Valued { expression, proof }))
    }

    /// ( scope -> √(p₁·(p₂·…)) = √p₁·(√p₂·…) ), and the right side.
    fn split_root(
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
    /// square roots of primes and which are equal: left − right is a sum
    /// of multiples of (√p)² − p, each zero, and the normaliser shows the
    /// sum is the difference.
    fn identity(
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
        let mut rest = difference.over.scaled(&under.recip());
        let mut by: IndexMap<Rpn, Multiplier> = IndexMap::new();
        while let Some((monomial, weight, at)) = reducible(&rest, self) {
            let (root, prime) = at;
            rest.terms.shift_remove(&monomial);
            let lowered = lowered(&monomial, &root);
            let one = Poly::new(IndexMap::from([(lowered.clone(), weight.clone())]));
            let entry = by.entry(root.clone()).or_insert_with(|| Multiplier {
                root: root.clone(),
                prime,
                times: Poly::default(),
            });
            entry.times = entry.times.plus(&one);
            rest = rest.plus(&one.scaled(&field::q(prime as i64)));
        }
        if !rest.zero() {
            return Ok(Route::no("the two sides are not one value"));
        }
        let mut w = Work::plain(scope, facts);
        if by.is_empty() {
            return self.same_polynomial(&mut w, left, right);
        }
        let mut pieces: Vec<(Rpn, Proof)> = Vec::new();
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
            let moved = self.b.ap(
                "oveq2d",
                &binds! {"ph" => scope, "A" => &gap, "B" => "cc0", "C" => &times, "F" => "cmul"},
                &[&vanishes],
            );
            let times_cc = self.membership(&times, "cc", scope, facts)?;
            let zero = self.b.ap(
                "mul01d",
                &binds! {"ph" => scope, "A" => &times},
                &[&times_cc],
            );
            let piece = t!(&times, &gap, "cmul", "co");
            let proof = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &piece, "B" => t!(&times, "cc0", "cmul", "co"), "C" => "cc0"},
                &[&moved, &zero],
            );
            pieces.push((piece, proof));
        }
        let (mut total, mut sums) = pieces[0].clone();
        let naught = t!("cc0", "cc0", "caddc", "co");
        for (piece, proof) in &pieces[1..] {
            let joined = t!(&total, piece, "caddc", "co");
            let both = self.b.ap(
                "oveq12d",
                &binds! {"ph" => scope, "A" => &total, "B" => "cc0", "C" => piece, "D" => "cc0", "F" => "caddc"},
                &[&sums, proof],
            );
            let zero = self.b.ap(
                "a1i",
                &binds! {"ph" => t!(&naught, "cc0", "wceq"), "ps" => scope},
                &[&self.step("00id")],
            );
            sums = self.b.ap(
                "eqtrd",
                &binds! {"ph" => scope, "A" => &joined, "B" => &naught, "C" => "cc0"},
                &[&both, &zero],
            );
            total = joined;
        }
        let whole = t!(left, right, "cmin", "co");
        let alike = take!(self.same_polynomial(&mut w, &total, &whole)?);
        let left_cc = take!(self.in_cc(left, scope, facts)?);
        let right_cc = take!(self.in_cc(right, scope, facts)?);
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => scope, "A" => &total, "B" => &whole, "C" => "cc0"},
            &[&alike, &sums],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => scope, "A" => left, "B" => right},
            &[&left_cc, &right_cc],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => scope, "ps" => t!(&whole, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
            &[&reached, &turn],
        )))
    }
}

/// A monomial of `p` holding a root of a prime to the power 2 or more, its
/// weight, and that root with its prime: the first, in the order the
/// polynomial holds them.
fn reducible(p: &Poly, el: &Elaborator) -> Option<(Monomial, Q, (Rpn, u64))> {
    for (monomial, weight) in &p.terms {
        for (atom, power) in monomial {
            if *power < 2 {
                continue;
            }
            if let Some(prime) = prime_under(&el.to_term(atom)) {
                return Some((monomial.clone(), weight.clone(), (atom.clone(), prime)));
            }
        }
    }
    None
}

/// The monomial with the power of `atom` two less.
fn lowered(monomial: &Monomial, atom: &Rpn) -> Monomial {
    monomial
        .iter()
        .filter_map(|(a, power)| match (a == atom, power) {
            (true, 2) => None,
            (true, p) => Some((a.clone(), p - 2)),
            (false, p) => Some((a.clone(), *p)),
        })
        .collect()
}

/// The prime p where the term is √p.
fn prime_under(term: &Term) -> Option<u64> {
    if !surds::is_root(term) {
        return None;
    }
    let n = crate::methods::numerals::value(&term.children()[0])?.to_u64()?;
    surds::root_of(&field::q(n as i64))
        .ok()
        .filter(|r| r.primes == [n] && r.coefficient == field::q(1))
        .map(|_| n)
}

/// Every prime under a root of the term, as its value finds them.
fn primes_under(term: &Term) -> Vec<u64> {
    let mut out = Vec::new();
    collect_primes(term, &mut out);
    out.sort_unstable();
    out.dedup();
    out
}

fn collect_primes(term: &Term, out: &mut Vec<u64>) {
    if term.variable().is_some() {
        return;
    }
    if surds::is_root(term) {
        if let Built(Value::Exact(v)) = surds::closed_value(term) {
            out.extend(v.primes());
        }
    }
    for kid in term.children() {
        collect_primes(kid, out);
    }
}

/// √p, as set.mm spells it.
fn root_of_prime(p: u64) -> Rpn {
    t!(numerals::spell(p), "csqrt", "cfv")
}

/// p₁·(p₂·…), or None for no primes.
fn product_of_primes(primes: &[u64]) -> Option<Rpn> {
    let (last, before) = primes.split_last()?;
    let mut out = numerals::spell(*last);
    for p in before.iter().rev() {
        out = t!(numerals::spell(*p), out, "cmul", "co");
    }
    Some(out)
}

/// Whether an expression is a numeral, a whole number of at least 0.
fn whole_at_least_zero(expression: &Rpn) -> bool {
    !expression.has("cneg") && !expression.has("cdiv")
}

/// A rational number as a term: a whole number as a numeral, and any other
/// as the quotient of two, each negated where it is negative.
fn spelt_rational(value: &Q) -> Rpn {
    if let Some(whole) = field::spell_coefficient(value) {
        return whole;
    }
    let top = numerals::spell(value.numer().magnitude().clone());
    let below = numerals::spell(value.denom().magnitude().clone());
    let quotient = t!(top, below, "cdiv", "co");
    if value.is_negative() {
        t!(quotient, "cneg")
    } else {
        quotient
    }
}

/// A polynomial as a sum of its terms, each a rational times a product of
/// powers of its atoms.
fn spelt_poly(p: &Poly) -> Rpn {
    let mut out: Option<Rpn> = None;
    let mut terms: Vec<(&Monomial, &Q)> = p.terms.iter().collect();
    terms.sort_by_key(|(m, _)| field::order(m));
    for (monomial, weight) in terms {
        let factors = monomial
            .iter()
            .map(|(atom, power)| match power {
                1 => atom.clone(),
                _ => t!(atom, numeral(*power), "cexp", "co"),
            })
            .reduce(|acc, f| t!(acc, f, "cmul", "co"));
        let coefficient = spelt_rational(weight);
        let term = match factors {
            None => coefficient,
            Some(f) => t!(coefficient, f, "cmul", "co"),
        };
        out = Some(match out {
            None => term,
            Some(sum) => t!(sum, term, "caddc", "co"),
        });
    }
    out.unwrap_or_else(|| t!("cc0"))
}
