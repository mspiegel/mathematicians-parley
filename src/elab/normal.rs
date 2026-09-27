//! Metamath proofs of ring identities over ℂ.
//!
//! [`super::field`] decides whether an `algebra` step holds; this builds the
//! proof of one that does. The two are separate because deciding needs no
//! kernel and emitting is most of the work.
//!
//! A step claims `L = R` where both sides are the same polynomial. The proof
//! is that each side equals one canonical term — `field::spell` of that
//! polynomial — so what is needed is a procedure taking a term to its
//! canonical form and saying why. That is done by recursion on the term
//! rather than by searching for a chain of rewrites: at `a + b` both sides
//! are already canonical, and what remains is to add two canonical forms,
//! which is a merge.
//!
//! Every step carries its membership alongside its equality. A ring lemma
//! wants its arguments in ℂ, and a canonical form's membership is built as the
//! form is built rather than asked for again at each use: `m ∈ ℂ` is proved
//! once, and everything above it follows by `mulcld`, `addcld` and `expcld`.
//!
//! The elaborator drives this; nothing here reads the database or the corpus.
//! What it cannot do for itself — say that an atom is a complex number, or
//! that a term is not zero — it asks of an [`Oracle`].

use std::rc::Rc;

use indexmap::IndexMap;
use num_traits::{ToPrimitive, Zero};

use super::field::{
    self, numeral as n, order, q, spell_coefficient, spell_monomial, Monomial, Q,
};
use crate::binds;
use crate::mm::kernel::{FloatLabels, Term};
use crate::mm::spell::{Builder, Proof};
use crate::outcome::{Built, Checked, Declined, Route};
use crate::{t, take};

const ADD: &str = "caddc";
const MUL: &str = "cmul";
const EXP: &str = "cexp";
const DIV: &str = "cdiv";
const SUB: &str = "cmin";

/// A canonical form: its terms, each a monomial and a coefficient, in the
/// order the form writes them.
pub type Run = Vec<(Monomial, Q)>;

/// A term's canonical form as a numerator, a denominator where it divides,
/// and the proof that the term is the one over the other.
pub type Quotiented = (Run, Option<Run>, Proof);

/// What the emitter asks of the elaborator driving it.
pub trait Oracle {
    /// The builder every step is assembled on.
    fn b(&self) -> &Builder;
    /// ( under -> said e. CC ), for a term the recursion bottoms out at.
    fn atom(&mut self, said: &str) -> Checked<Proof>;
    /// ( under -> said =/= 0 ), asked only of an emitter given a way to.
    fn apart(&mut self, said: &str) -> Checked<Proof>;
    /// What the page says makes `said` not zero, asked only of an emitter
    /// given a way to.
    fn written(&mut self, said: &str) -> Checked<Option<Proof>>;
}

/// `( left what right )`, which reverse Polish writes the other way.
fn op(left: &str, right: &str, what: &str) -> String {
    t!(left, right, what, "co")
}

/// A left-associated run, which is the shape every canonical form has.
fn join(terms: &[String], what: &str) -> String {
    let mut out = terms[0].clone();
    for one in &terms[1..] {
        out = op(&out, one, what);
    }
    out
}

fn whole(weight: &Q) -> i64 {
    weight.to_integer().to_i64().unwrap_or(0)
}

fn coeff(weight: &Q) -> String {
    spell_coefficient(weight).unwrap_or_default()
}

/// What an emitter has built and remembers, because it will be asked for it
/// again: these build from their arguments and from `under`, which does not
/// change while one emitter is alive.
#[derive(Clone, PartialEq, Eq, Hash)]
enum Made {
    Number(i64),
    Index(i64),
    Coefficient(Q),
    MonomialCc(Monomial),
    TermCc(Monomial, Q),
    FactorCc(Rc<str>, u32),
}

/// Proofs over one scope.
///
/// `under` is the antecedent every statement carries, in reverse Polish.
/// Everything here is built by applying a label to what it is applied to,
/// and nothing is parsed.
pub struct Emitter {
    pub under: String,
    /// Whether the oracle can say a term is not zero, by search.
    apart: bool,
    /// Whether the oracle can say what the page wrote a term is not.
    written: bool,
    held: IndexMap<String, Proof>,
    made: IndexMap<Made, Proof>,
    nonzero: IndexMap<String, Proof>,
}

impl Emitter {
    pub fn new(under: &str, apart: bool, written: bool) -> Emitter {
        Emitter {
            under: under.to_string(),
            apart,
            written,
            held: IndexMap::new(),
            made: IndexMap::new(),
            nonzero: IndexMap::new(),
        }
    }

    /// ( under -> what = what ).
    pub fn same(&self, o: &dyn Oracle, what: &str) -> Proof {
        o.b()
            .ap("eqidd", &binds! {"ph" => &self.under, "A" => what}, &[])
    }

    /// ( under -> a = c ) from ( under -> a = b ) and ( under -> b = c ).
    pub fn chain(
        &self,
        o: &dyn Oracle,
        first: &Proof,
        second: &Proof,
        a: &str,
        b: &str,
        c: &str,
    ) -> Proof {
        o.b().ap(
            "eqtrd",
            &binds! {"ph" => &self.under, "A" => a, "B" => b, "C" => c},
            &[first, second],
        )
    }

    // --- membership -----------------------------------------------------

    /// What says a numeral is a complex number. set.mm proves one for each
    /// digit but takes the one for 1 as an axiom.
    pub fn complex_label(value: i64) -> String {
        if value == 1 {
            "ax-1cn".to_string()
        } else {
            format!("{value}cn")
        }
    }

    /// What says a numeral is not zero, named the same way.
    pub fn apart_label(value: i64) -> String {
        if value == 1 {
            "ax-1ne0".to_string()
        } else {
            format!("{value}ne0")
        }
    }

    /// ( under -> n e. CC ) for a whole number the kernel spells.
    pub fn number(&mut self, o: &dyn Oracle, value: i64) -> Proof {
        let key = Made::Number(value);
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let b = o.b();
        let made = b.ap(
            "a1i",
            &binds! {"ph" => t!(n(value as u32), "cc", "wcel"), "ps" => &self.under},
            &[&b.step(&Self::complex_label(value))],
        );
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> k e. NN0 ), which an exponent has to be.
    pub fn index(&mut self, o: &dyn Oracle, value: i64) -> Proof {
        let key = Made::Index(value);
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let b = o.b();
        let made = b.ap(
            "a1i",
            &binds! {"ph" => t!(n(value as u32), "cn0", "wcel"), "ps" => &self.under},
            &[&b.step(&format!("{value}nn0"))],
        );
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> c e. CC ) for a coefficient, negated where negative.
    pub fn coefficient(&mut self, o: &dyn Oracle, weight: &Q) -> Proof {
        let key = Made::Coefficient(weight.clone());
        if let Some(p) = self.made.get(&key) {
            return p.clone();
        }
        let numerator = whole(&Q::from_integer(weight.numer().clone()));
        let magnitude = numerator.abs();
        let held = self.number(o, magnitude);
        let made = if numerator < 0 {
            o.b().ap(
                "negcld",
                &binds! {"ph" => &self.under, "A" => n(magnitude as u32)},
                &[&held],
            )
        } else {
            held
        };
        self.made.insert(key, made.clone());
        made
    }

    /// ( under -> M e. CC ) for a monomial's canonical form.
    pub fn monomial_cc(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
    ) -> Checked<Proof> {
        let key = Made::MonomialCc(monomial.clone());
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let made = if monomial.is_empty() {
            self.number(o, 1)
        } else {
            let mut said: Option<String> = None;
            let mut out: Option<Proof> = None;
            for (name, power) in monomial {
                let atom = o.atom(name)?;
                let index = self.index(o, *power as i64);
                let one = o.b().ap(
                    "expcld",
                    &binds! {"ph" => &self.under, "A" => &**name, "N" => n(*power)},
                    &[&atom, &index],
                );
                let spelt = op(name, n(*power), EXP);
                match (&said, &out) {
                    (Some(s), Some(p)) => {
                        out = Some(o.b().ap(
                            "mulcld",
                            &binds! {"ph" => &self.under, "A" => s, "B" => &spelt},
                            &[p, &one],
                        ));
                        said = Some(op(s, &spelt, MUL));
                    }
                    _ => {
                        said = Some(spelt);
                        out = Some(one);
                    }
                }
            }
            out.expect("a monomial of one factor at least")
        };
        self.made.insert(key, made.clone());
        Ok(made)
    }

    /// ( under -> ( c x. M ) e. CC ).
    pub fn term_cc(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Proof> {
        let key = Made::TermCc(monomial.clone(), weight.clone());
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let c = self.coefficient(o, weight);
        let m = self.monomial_cc(o, monomial)?;
        let made = o.b().ap(
            "mulcld",
            &binds! {"ph" => &self.under, "A" => coeff(weight), "B" => spell_monomial(monomial)},
            &[&c, &m],
        );
        self.made.insert(key, made.clone());
        Ok(made)
    }

    pub fn spell_term(item: &(Monomial, Q)) -> String {
        op(&coeff(&item.1), &spell_monomial(&item.0), MUL)
    }

    /// A run of terms as one term; the empty run is zero.
    pub fn spell_run(items: &[(Monomial, Q)]) -> String {
        if items.is_empty() {
            return n(0).to_string();
        }
        join(&items.iter().map(Self::spell_term).collect::<Vec<_>>(), ADD)
    }

    /// ( under -> spell_run(items) e. CC ), remembered once per run.
    pub fn run_cc(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
    ) -> Checked<Proof> {
        let said = Self::spell_run(items);
        if let Some(p) = self.held.get(&said) {
            return Ok(p.clone());
        }
        let out = if items.is_empty() {
            self.number(o, 0)
        } else {
            let mut out = self.term_cc(o, &items[0].0, &items[0].1)?;
            let mut running = Self::spell_term(&items[0]);
            for item in &items[1..] {
                let one = Self::spell_term(item);
                let cc = self.term_cc(o, &item.0, &item.1)?;
                out = o.b().ap(
                    "addcld",
                    &binds! {"ph" => &self.under, "A" => &running, "B" => &one},
                    &[&out, &cc],
                );
                running = op(&running, &one, ADD);
            }
            out
        };
        self.held.insert(said, out.clone());
        Ok(out)
    }

    // --- moving a term along a sum -------------------------------------

    /// Carry an equality of a prefix out to the whole run.
    ///
    /// A canonical form associates to the left, so a rewrite of the first k
    /// parts sits under one `oveq1d` for each part after them. Sums and
    /// products are the same shape, which is why this takes the operation.
    fn lift(
        &self,
        o: &dyn Oracle,
        proof: Proof,
        left: &str,
        right: &str,
        tail: &[String],
        what: &str,
    ) -> Proof {
        let (mut proof, mut left, mut right) =
            (proof, left.to_string(), right.to_string());
        for one in tail {
            proof = o.b().ap(
                "oveq1d",
                &binds! {"ph" => &self.under, "A" => &left, "B" => &right, "C" => one, "F" => what},
                &[&proof],
            );
            left = op(&left, one, what);
            right = op(&right, one, what);
        }
        proof
    }

    /// Two neighbours exchanged, as an equality of the whole run: `add32`
    /// where they sit at the end of a run, `addcom` where they are the whole
    /// of it, and the terms after them come along under `lift`.
    fn swap(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<Proof> {
        let head = &items[..at];
        let a = Self::spell_term(&items[at]);
        let b = Self::spell_term(&items[at + 1]);
        let tail: Vec<String> = items[at + 2..].iter().map(Self::spell_term).collect();
        let (before, after, step);
        if !head.is_empty() {
            let prefix = Self::spell_run(head);
            before = op(&op(&prefix, &a, ADD), &b, ADD);
            after = op(&op(&prefix, &b, ADD), &a, ADD);
            let p0 = self.run_cc(o, head)?;
            let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
            let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
            let bb = o.b();
            let law =
                bb.ap("add32", &binds! {"A" => &prefix, "B" => &a, "C" => &b}, &[]);
            step = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(before, after, "wceq")},
                &[&p0, &p1, &p2, &law],
            );
        } else {
            before = op(&a, &b, ADD);
            after = op(&b, &a, ADD);
            let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
            let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
            let bb = o.b();
            let law = bb.ap("addcom", &binds! {"A" => &a, "B" => &b}, &[]);
            step = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(b, "cc", "wcel"), "th" => t!(before, after, "wceq")},
                &[&p1, &p2, &law],
            );
        }
        Ok(self.lift(o, step, &before, &after, &tail, ADD))
    }

    // --- coefficients ---------------------------------------------------

    /// ( under -> claim ) from a claim that holds outright.
    pub fn a1i(&self, o: &dyn Oracle, claim: &str, proof: &Proof) -> Proof {
        o.b().ap(
            "a1i",
            &binds! {"ph" => claim, "ps" => &self.under},
            &[proof],
        )
    }

    /// `a1i` of a closed lemma named by its label.
    pub fn a1i_label(&self, o: &dyn Oracle, claim: &str, label: &str) -> Proof {
        let step = o.b().step(label);
        self.a1i(o, claim, &step)
    }

    /// ( under -> ( c + d ) = e ), the coefficients as `spell` writes them.
    ///
    /// set.mm names a lemma for every pair of single digits, and the pairs
    /// it leaves out are exactly those with a zero, which `addlid` and
    /// `addrid` cover. A pair that cancels is `negidd`. Anything else is
    /// refused rather than guessed at.
    pub fn coefficient_sum(
        &mut self,
        o: &dyn Oracle,
        first: &Q,
        second: &Q,
    ) -> Route<Proof> {
        let total = first + second;
        let said = spell_coefficient(&total);
        let (c, d) = (spell_coefficient(first), spell_coefficient(second));
        let (Some(said), Some(c), Some(d)) = (said, c, d) else {
            return Route::no(format!(
                "{} + {} is past one digit",
                show(first),
                show(second)
            ));
        };
        let claim = t!(op(&c, &d, ADD), said, "wceq");
        let (a, bn) = (whole(first), whole(second));
        if a == -bn && a != 0 {
            let whole_n = n(a.unsigned_abs() as u32);
            let num = self.number(o, a.abs());
            let cancels = o.b().ap(
                "negidd",
                &binds! {"ph" => &self.under, "A" => whole_n},
                &[&num],
            );
            if a > 0 {
                return Built(cancels);
            }
            // The negative one first, so the two are commuted before they
            // cancel: `negid` states the sum only one way round.
            let pc = self.coefficient(o, first);
            let pd = self.coefficient(o, second);
            let bb = o.b();
            let law = bb.ap("addcom", &binds! {"A" => &c, "B" => &d}, &[]);
            let turned = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                "ch" => t!(d, "cc", "wcel"),
                "th" => t!(op(&c, &d, ADD), op(&d, &c, ADD), "wceq")},
                &[&pc, &pd, &law],
            );
            return Built(self.chain(
                o,
                &turned,
                &cancels,
                &op(&c, &d, ADD),
                &op(&d, &c, ADD),
                n(0),
            ));
        }
        if a < 0 && bn < 0 {
            // -u i + -u j is -u ( i + j ), which `negdi` says read
            // backwards, and the two are then both positive.
            let w = [n((-a) as u32).to_string(), n((-bn) as u32).to_string()];
            let both = match self.coefficient_sum(o, &-first, &-second) {
                Built(p) => p,
                Declined(d) => return Declined(d),
            };
            let pa = self.number(o, -a);
            let pb = self.number(o, -bn);
            let bb = o.b();
            let sum = op(&w[0], &w[1], ADD);
            let law = bb.ap("negdi", &binds! {"A" => &w[0], "B" => &w[1]}, &[]);
            let inner = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(w[0], "cc", "wcel"),
                "ch" => t!(w[1], "cc", "wcel"),
                "th" => t!(t!(sum, "cneg"), op(&c, &d, ADD), "wceq")},
                &[&pa, &pb, &law],
            );
            let back = bb.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => t!(sum, "cneg"), "B" => op(&c, &d, ADD)},
                &[&inner],
            );
            let negated = bb.ap(
                "negeqd",
                &binds! {"ph" => &self.under, "A" => &sum, "B" => n((-a - bn) as u32)},
                &[&both],
            );
            return Built(self.chain(
                o,
                &back,
                &negated,
                &op(&c, &d, ADD),
                &t!(sum, "cneg"),
                &said,
            ));
        }
        if a < 0 || bn < 0 {
            if a < 0 {
                // The negative one second, so one case covers both.
                let swapped = match self.coefficient_sum(o, second, first) {
                    Built(p) => p,
                    Declined(d) => return Declined(d),
                };
                let pc = self.coefficient(o, first);
                let pd = self.coefficient(o, second);
                let bb = o.b();
                let law = bb.ap("addcom", &binds! {"A" => &c, "B" => &d}, &[]);
                let turned = bb.ap(
                    "syl2anc",
                    &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                    "ch" => t!(d, "cc", "wcel"),
                    "th" => t!(op(&c, &d, ADD), op(&d, &c, ADD), "wceq")},
                    &[&pc, &pd, &law],
                );
                return Built(self.chain(
                    o,
                    &turned,
                    &swapped,
                    &op(&c, &d, ADD),
                    &op(&d, &c, ADD),
                    &said,
                ));
            }
            return self.minus_numeral(o, a, -bn, &c, &d, &said);
        }
        let bb = o.b();
        if a == 0 {
            let law = bb.ap("addlid", &binds! {"A" => &d}, &[]);
            let held = self.mp(
                o,
                &t!(d, "cc", "wcel"),
                &claim,
                &Self::complex_label(bn),
                &law,
            );
            return Built(self.a1i(o, &claim, &held));
        }
        if bn == 0 {
            let law = bb.ap("addrid", &binds! {"A" => &c}, &[]);
            let held = self.mp(
                o,
                &t!(c, "cc", "wcel"),
                &claim,
                &Self::complex_label(a),
                &law,
            );
            return Built(self.a1i(o, &claim, &held));
        }
        Built(self.a1i_label(o, &claim, &format!("{a}p{bn}e{}", a + bn)))
    }

    fn mp(
        &self,
        o: &dyn Oracle,
        given: &str,
        claim: &str,
        hypothesis: &str,
        implication: &Proof,
    ) -> Proof {
        let b = o.b();
        b.ap(
            "ax-mp",
            &binds! {"ph" => given, "ps" => claim},
            &[&b.step(hypothesis), implication],
        )
    }

    /// ( under -> ( i - j ) = k ) for whole numbers with i at least j.
    ///
    /// `subadd` says a difference is a number exactly when adding that
    /// number back gives the first, so the subtraction is answered out of
    /// the addition table and set.mm needs no second one.
    fn gap_numeral(
        &mut self,
        o: &dyn Oracle,
        bigger: i64,
        smaller: i64,
    ) -> Route<Proof> {
        let (left, right) = (n(bigger as u32), n(smaller as u32));
        let out = n((bigger - smaller) as u32);
        let back = match self.coefficient_sum(o, &q(smaller), &q(bigger - smaller)) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, bigger);
        let p1 = self.number(o, smaller);
        let p2 = self.number(o, bigger - smaller);
        let b = o.b();
        let law = b.ap(
            "subadd",
            &binds! {"A" => left, "B" => right, "C" => out},
            &[],
        );
        let turn = b.ap(
            "syl3anc",
            &binds! {"ph" => &self.under, "ps" => t!(left, "cc", "wcel"),
            "ch" => t!(right, "cc", "wcel"), "th" => t!(out, "cc", "wcel"),
            "ta" => t!(t!(op(left, right, "cmin"), out, "wceq"),
                       t!(op(right, out, ADD), left, "wceq"), "wb")},
            &[&p0, &p1, &p2, &law],
        );
        Built(b.ap(
            "mpbird",
            &binds! {"ph" => &self.under,
            "ps" => t!(op(left, right, "cmin"), out, "wceq"),
            "ch" => t!(op(right, out, ADD), left, "wceq")},
            &[&back, &turn],
        ))
    }

    /// ( under -> ( i + -u j ) = k ), the two of opposite sign: `negsub`
    /// turns the sum into a difference, and which way round the difference
    /// goes decides whether the answer carries a minus.
    fn minus_numeral(
        &mut self,
        o: &dyn Oracle,
        first: i64,
        second: i64,
        c: &str,
        d: &str,
        said: &str,
    ) -> Route<Proof> {
        let gap = op(n(first as u32), n(second as u32), "cmin");
        let apart = match self.same_gap(o, first, second) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, first);
        let p1 = self.number(o, second);
        let b = o.b();
        let law = b.ap(
            "negsub",
            &binds! {"A" => n(first as u32), "B" => n(second as u32)},
            &[],
        );
        let turned = b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(n(first as u32), "cc", "wcel"),
            "ch" => t!(n(second as u32), "cc", "wcel"),
            "th" => t!(op(c, d, ADD), gap, "wceq")},
            &[&p0, &p1, &law],
        );
        Built(self.chain(o, &turned, &apart, &op(c, d, ADD), &gap, said))
    }

    /// ( under -> ( i - j ) = k ), whichever way round the two are.
    fn same_gap(&mut self, o: &dyn Oracle, first: i64, second: i64) -> Route<Proof> {
        if first >= second {
            return self.gap_numeral(o, first, second);
        }
        let (f, s) = (n(first as u32), n(second as u32));
        let other = op(s, f, "cmin");
        let back = match self.gap_numeral(o, second, first) {
            Built(p) => p,
            Declined(d) => return Declined(d),
        };
        let p0 = self.number(o, second);
        let p1 = self.number(o, first);
        let b = o.b();
        let law = b.ap("negsubdi2", &binds! {"A" => s, "B" => f}, &[]);
        let inner = b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(s, "cc", "wcel"),
            "ch" => t!(f, "cc", "wcel"),
            "th" => t!(t!(other, "cneg"), op(f, s, "cmin"), "wceq")},
            &[&p0, &p1, &law],
        );
        let turned = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => t!(other, "cneg"), "B" => op(f, s, "cmin")},
            &[&inner],
        );
        let negated = b.ap(
            "negeqd",
            &binds! {"ph" => &self.under, "A" => &other, "B" => n((second - first) as u32)},
            &[&back],
        );
        Built(self.chain(
            o,
            &turned,
            &negated,
            &op(f, s, "cmin"),
            &t!(other, "cneg"),
            &t!(n((second - first) as u32), "cneg"),
        ))
    }

    // --- putting one term into a run ------------------------------------

    /// ( under -> ( ( c x. M ) + ( d x. M ) ) = ( e x. M ) ): `adddir` read
    /// the other way collects two terms that share a monomial, which is the
    /// only place the coefficients meet.
    fn combine(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        first: &Q,
        second: &Q,
    ) -> Checked<Route<Proof>> {
        let spelt = spell_monomial(monomial);
        let (c, d) = (coeff(first), coeff(second));
        let total = coeff(&(first + second));
        let pc = self.coefficient(o, first);
        let pd = self.coefficient(o, second);
        let pm = self.monomial_cc(o, monomial)?;
        let apart = op(&op(&c, &spelt, MUL), &op(&d, &spelt, MUL), ADD);
        let together = op(&op(&c, &d, ADD), &spelt, MUL);
        let gathered = {
            let b = o.b();
            let law =
                b.ap("adddir", &binds! {"A" => &c, "B" => &d, "C" => &spelt}, &[]);
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"),
                "ch" => t!(d, "cc", "wcel"), "th" => t!(spelt, "cc", "wcel"),
                "ta" => t!(together, apart, "wceq")},
                &[&pc, &pd, &pm, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &together, "B" => &apart},
                &[&inner],
            )
        };
        let added = take!(self.coefficient_sum(o, first, second));
        let moved = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&c, &d, ADD), "B" => &total,
            "C" => &spelt, "F" => MUL},
            &[&added],
        );
        Ok(Built(self.chain(
            o,
            &gathered,
            &moved,
            &apart,
            &together,
            &op(&total, &spelt, MUL),
        )))
    }

    /// ( under -> spell_run(items) = spell_run(moved) ), one term moved.
    ///
    /// Leftward is the direction an appended term travels to reach the
    /// place its degree puts it; rightward is how a term whose coefficient
    /// has cancelled reaches the end, where it comes off. Each step is one
    /// `swap`.
    fn shift(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        frm: usize,
        to: usize,
    ) -> Checked<(Run, Proof)> {
        let start = Self::spell_run(items);
        let mut said = start.clone();
        let mut items: Run = items.to_vec();
        let mut proof: Option<Proof> = None;
        let steps: Vec<usize> = if to > frm {
            (frm..to).collect()
        } else {
            (to..frm).rev().collect()
        };
        for at in steps {
            let step = self.swap(o, &items, at)?;
            items.swap(at, at + 1);
            let after = Self::spell_run(&items);
            proof = Some(match proof {
                None => step,
                Some(p) => self.chain(o, &p, &step, &start, &said, &after),
            });
            said = after;
        }
        let proof = match proof {
            Some(p) => p,
            None => self.same(o, &start),
        };
        Ok((items, proof))
    }

    /// ( under -> spell_run(items) = spell_run(rest) ), a zero term gone.
    ///
    /// A coefficient that has cancelled leaves `( 0 x. M )`, which is zero
    /// by `mul02` and comes off the end by `addrid`. The term is walked to
    /// the end first, because that is where it can come off.
    fn drop(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<(Run, Proof)> {
        let start = Self::spell_run(items);
        let (items, walked) = self.shift(o, items, at, items.len() - 1)?;
        let run = Self::spell_run(&items);
        let rest: Run = items[..items.len() - 1].to_vec();
        let last = &items[items.len() - 1];
        let zero = Self::spell_term(last);
        let spelt = spell_monomial(&last.0);
        let pm = self.monomial_cc(o, &last.0)?;
        let vanishes = {
            let b = o.b();
            let law = b.ap("mul02", &binds! {"A" => &spelt}, &[]);
            b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(spelt, "cc", "wcel"),
                "ch" => t!(zero, n(0), "wceq")},
                &[&pm, &law],
            )
        };
        if rest.is_empty() {
            let p = self.chain(o, &walked, &vanishes, &start, &run, n(0));
            return Ok((rest, p));
        }
        let keep = Self::spell_run(&rest);
        let rc = self.run_cc(o, &rest)?;
        let comes_off = {
            let b = o.b();
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => &zero, "B" => n(0), "C" => &keep, "F" => ADD},
                &[&vanishes],
            );
            let law = b.ap("addrid", &binds! {"A" => &keep}, &[]);
            let second = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, n(0), ADD), keep, "wceq")},
                &[&rc, &law],
            );
            self.chain(o, &first, &second, &run, &op(&keep, n(0), ADD), &keep)
        };
        let p = self.chain(o, &walked, &comes_off, &start, &run, &keep);
        Ok((rest, p))
    }

    /// ( under -> ( spell_run(items) + ( c x. M ) ) = spell_run(out) ).
    ///
    /// One term put where its degree says it goes. If the monomial is
    /// already there the two coefficients meet and may cancel; otherwise the
    /// term simply travels left to its place.
    fn insert(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Route<(Run, Proof)>> {
        let term = Self::spell_term(&(monomial.clone(), weight.clone()));
        if items.is_empty() {
            let cc = self.term_cc(o, monomial, weight)?;
            let b = o.b();
            let law = b.ap("addlid", &binds! {"A" => &term}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(op(n(0), &term, ADD), term, "wceq")},
                &[&cc, &law],
            );
            return Ok(Built((vec![(monomial.clone(), weight.clone())], p)));
        }
        let mut appended: Run = items.to_vec();
        appended.push((monomial.clone(), weight.clone()));
        let start = Self::spell_run(&appended);
        if let Some(at) = items.iter().position(|(m, _)| m == monomial) {
            let (moved, walked) = self.shift(o, &appended, items.len(), at + 1)?;
            let total = &moved[at].1 + &moved[at + 1].1;
            let joined = take!(self.gather(o, &moved, at)?);
            let mut out: Run = moved[..at].to_vec();
            out.push((monomial.clone(), total.clone()));
            out.extend(moved[at + 2..].iter().cloned());
            let mut proof = self.chain(
                o,
                &walked,
                &joined,
                &start,
                &Self::spell_run(&moved),
                &Self::spell_run(&out),
            );
            if total.is_zero() {
                let before = Self::spell_run(&out);
                let (rest, gone) = self.drop(o, &out, at)?;
                proof = self.chain(
                    o,
                    &proof,
                    &gone,
                    &start,
                    &before,
                    &Self::spell_run(&rest),
                );
                out = rest;
            }
            return Ok(Built((out, proof)));
        }
        let mine = order(monomial);
        let goes = items.iter().filter(|(m, _)| order(m) < mine).count();
        let (out, walked) = self.shift(o, &appended, items.len(), goes)?;
        Ok(Built((out, walked)))
    }

    /// Two neighbours that share a monomial, collected into one term:
    /// `addass` exposes them as a pair where they sit at the end of a run;
    /// where they are the whole of it they are already exposed.
    fn gather(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        at: usize,
    ) -> Checked<Route<Proof>> {
        let head = &items[..at];
        let rest = &items[at + 2..];
        let monomial = &items[at].0;
        let a = Self::spell_term(&items[at]);
        let b = Self::spell_term(&items[at + 1]);
        let total =
            Self::spell_term(&(monomial.clone(), &items[at].1 + &items[at + 1].1));
        let collect =
            take!(self.combine(o, monomial, &items[at].1, &items[at + 1].1)?);
        let tail: Vec<String> = rest.iter().map(Self::spell_term).collect();
        if head.is_empty() {
            return Ok(Built(self.lift(
                o,
                collect,
                &op(&a, &b, ADD),
                &total,
                &tail,
                ADD,
            )));
        }
        let prefix = Self::spell_run(head);
        let p0 = self.run_cc(o, head)?;
        let p1 = self.term_cc(o, &items[at].0, &items[at].1)?;
        let p2 = self.term_cc(o, &items[at + 1].0, &items[at + 1].1)?;
        let outer = op(&op(&prefix, &a, ADD), &b, ADD);
        let inner_pair = op(&prefix, &op(&a, &b, ADD), ADD);
        let exposed = {
            let bb = o.b();
            let law = bb.ap(
                "addass",
                &binds! {"A" => &prefix, "B" => &a, "C" => &b},
                &[],
            );
            bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(outer, inner_pair, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let moved = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => op(&a, &b, ADD), "B" => &total,
            "C" => &prefix, "F" => ADD},
            &[&collect],
        );
        let step = self.chain(
            o,
            &exposed,
            &moved,
            &outer,
            &inner_pair,
            &op(&prefix, &total, ADD),
        );
        Ok(Built(self.lift(
            o,
            step,
            &outer,
            &op(&prefix, &total, ADD),
            &tail,
            ADD,
        )))
    }

    /// ( under -> ( spell_run(left) + spell_run(right) ) = spell_run(sum) ).
    ///
    /// The right-hand run is taken apart from its end, one term at a time,
    /// and each is put into the left by `insert`. `addass` is what peels a
    /// term off: the run associates to the left, so its last term is
    /// already where the law can reach it.
    pub fn add(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Monomial, Q)],
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let start = op(&Self::spell_run(left), &Self::spell_run(right), ADD);
        if right.is_empty() {
            let keep = Self::spell_run(left);
            let rc = self.run_cc(o, left)?;
            let b = o.b();
            let law = b.ap("addrid", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, n(0), ADD), keep, "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((left.to_vec(), p)));
        }
        if right.len() == 1 {
            return self.insert(o, left, &right[0].0, &right[0].1);
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let whole_run = Self::spell_run(right);
        let prefix = Self::spell_run(rest);
        let held = Self::spell_run(left);
        let term = Self::spell_term(last);
        let p0 = self.run_cc(o, left)?;
        let p1 = self.run_cc(o, rest)?;
        let p2 = self.term_cc(o, &last.0, &last.1)?;
        let grouped = op(&op(&held, &prefix, ADD), &term, ADD);
        let peeled = {
            let b = o.b();
            let law = b.ap(
                "addass",
                &binds! {"A" => &held, "B" => &prefix, "C" => &term},
                &[],
            );
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(held, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(term, "cc", "wcel"),
                "ta" => t!(grouped, op(&held, &whole_run, ADD), "wceq")},
                &[&p0, &p1, &p2, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &grouped, "B" => op(&held, &whole_run, ADD)},
                &[&inner],
            )
        };
        let (merged, inner) = take!(self.add(o, left, rest)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&held, &prefix, ADD),
            "B" => Self::spell_run(&merged), "C" => &term, "F" => ADD},
            &[&inner],
        );
        let (out, placed) = take!(self.insert(o, &merged, &last.0, &last.1)?);
        let middle = op(&Self::spell_run(&merged), &term, ADD);
        let first = self.chain(o, &peeled, &carried, &start, &grouped, &middle);
        let p = self.chain(o, &first, &placed, &start, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    // --- monomials --------------------------------------------------------
    //
    // The same shape as the sum side, over products, and shorter for one
    // reason: a monomial holds only positive powers, so multiplying two of
    // them adds positive numbers and nothing can cancel.

    fn factor_cc(
        &mut self,
        o: &mut dyn Oracle,
        name: &Rc<str>,
        power: u32,
    ) -> Checked<Proof> {
        let key = Made::FactorCc(name.clone(), power);
        if let Some(p) = self.made.get(&key) {
            return Ok(p.clone());
        }
        let atom = o.atom(name)?;
        let index = self.index(o, power as i64);
        let made = o.b().ap(
            "expcld",
            &binds! {"ph" => &self.under, "A" => &**name, "N" => n(power)},
            &[&atom, &index],
        );
        self.made.insert(key, made.clone());
        Ok(made)
    }

    fn factors_cc(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rc<str>, u32)],
    ) -> Checked<Proof> {
        if factors.is_empty() {
            return Ok(self.number(o, 1));
        }
        let mut out = self.factor_cc(o, &factors[0].0, factors[0].1)?;
        let mut running = spell_factor(&factors[0]);
        for one in &factors[1..] {
            let f = self.factor_cc(o, &one.0, one.1)?;
            out = o.b().ap(
                "mulcld",
                &binds! {"ph" => &self.under, "A" => &running, "B" => spell_factor(one)},
                &[&out, &f],
            );
            running = op(&running, &spell_factor(one), MUL);
        }
        Ok(out)
    }

    /// `mul32` for `add32`, and `mulcom` where the two are the whole.
    fn swap_factors(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rc<str>, u32)],
        at: usize,
    ) -> Checked<Proof> {
        let head = &factors[..at];
        let a = spell_factor(&factors[at]);
        let b = spell_factor(&factors[at + 1]);
        let (before, after, step);
        if !head.is_empty() {
            let prefix = spell_monomial(&head.to_vec());
            before = op(&op(&prefix, &a, MUL), &b, MUL);
            after = op(&op(&prefix, &b, MUL), &a, MUL);
            let p0 = self.factors_cc(o, head)?;
            let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
            let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
            let bb = o.b();
            let law =
                bb.ap("mul32", &binds! {"A" => &prefix, "B" => &a, "C" => &b}, &[]);
            step = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(before, after, "wceq")},
                &[&p0, &p1, &p2, &law],
            );
        } else {
            before = op(&a, &b, MUL);
            after = op(&b, &a, MUL);
            let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
            let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
            let bb = o.b();
            let law = bb.ap("mulcom", &binds! {"A" => &a, "B" => &b}, &[]);
            step = bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(b, "cc", "wcel"), "th" => t!(before, after, "wceq")},
                &[&p1, &p2, &law],
            );
        }
        let tail: Vec<String> = factors[at + 2..].iter().map(spell_factor).collect();
        Ok(self.lift(o, step, &before, &after, &tail, MUL))
    }

    fn shift_factors(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rc<str>, u32)],
        frm: usize,
        to: usize,
    ) -> Checked<(Monomial, Proof)> {
        let start = spell_monomial(&factors.to_vec());
        let mut said = start.clone();
        let mut factors = factors.to_vec();
        let mut proof: Option<Proof> = None;
        for at in (to..frm).rev() {
            let step = self.swap_factors(o, &factors, at)?;
            factors.swap(at, at + 1);
            let after = spell_monomial(&factors);
            proof = Some(match proof {
                None => step,
                Some(p) => self.chain(o, &p, &step, &start, &said, &after),
            });
            said = after;
        }
        let proof = match proof {
            Some(p) => p,
            None => self.same(o, &start),
        };
        Ok((factors, proof))
    }

    /// ( under -> ( ( x ^ j ) x. ( x ^ k ) ) = ( x ^ ( j + k ) ) ): `expadd`
    /// read backwards, which is where two powers of one atom meet, and the
    /// only place the exponents are added.
    fn gather_factors(
        &mut self,
        o: &mut dyn Oracle,
        name: &Rc<str>,
        first: u32,
        second: u32,
    ) -> Checked<Route<Proof>> {
        let a = op(name, n(first), EXP);
        let b = op(name, n(second), EXP);
        let total = first + second;
        if total > 9 {
            return Ok(Route::no(format!(
                "{name} to the {total} is past one digit"
            )));
        }
        let exponent = op(n(first), n(second), ADD);
        let atom = o.atom(name)?;
        let i1 = self.index(o, first as i64);
        let i2 = self.index(o, second as i64);
        let joined = {
            let bb = o.b();
            let law = bb.ap(
                "expadd",
                &binds! {"A" => &**name, "M" => n(first), "N" => n(second)},
                &[],
            );
            let inner = bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(name, "cc", "wcel"),
                "ch" => t!(n(first), "cn0", "wcel"), "th" => t!(n(second), "cn0", "wcel"),
                "ta" => t!(op(name, &exponent, EXP), op(&a, &b, MUL), "wceq")},
                &[&atom, &i1, &i2, &law],
            );
            bb.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => op(name, &exponent, EXP), "B" => op(&a, &b, MUL)},
                &[&inner],
            )
        };
        let exponents =
            match self.coefficient_sum(o, &q(first as i64), &q(second as i64)) {
                Built(p) => p,
                Declined(d) => return Ok(Declined(d)),
            };
        let moved = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => &exponent, "B" => n(total),
            "C" => &**name, "F" => EXP},
            &[&exponents],
        );
        Ok(Built(self.chain(
            o,
            &joined,
            &moved,
            &op(&a, &b, MUL),
            &op(name, &exponent, EXP),
            &op(name, n(total), EXP),
        )))
    }

    /// One factor put where its atom's name says it goes.
    fn insert_factor(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rc<str>, u32)],
        name: &Rc<str>,
        power: u32,
    ) -> Checked<Route<(Monomial, Proof)>> {
        let one = op(name, n(power), EXP);
        if factors.is_empty() {
            let f = self.factor_cc(o, name, power)?;
            let b = o.b();
            let law = b.ap("mullid", &binds! {"A" => &one}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(one, "cc", "wcel"),
                "ch" => t!(op(n(1), &one, MUL), one, "wceq")},
                &[&f, &law],
            );
            return Ok(Built((vec![(name.clone(), power)], p)));
        }
        let mut appended = factors.to_vec();
        appended.push((name.clone(), power));
        let start = spell_monomial(&appended);
        if let Some(at) = factors.iter().position(|(m, _)| m == name) {
            let (moved, walked) =
                self.shift_factors(o, &appended, factors.len(), at + 1)?;
            let total = moved[at].1 + moved[at + 1].1;
            let mut out = moved[..at].to_vec();
            out.push((name.clone(), total));
            out.extend(moved[at + 2..].iter().cloned());
            let gathered =
                take!(self.gather_factors(o, name, moved[at].1, moved[at + 1].1)?);
            let spread = self.spread(o, &moved, at, gathered)?;
            let p = self.chain(
                o,
                &walked,
                &spread,
                &start,
                &spell_monomial(&moved),
                &spell_monomial(&out),
            );
            return Ok(Built((out, p)));
        }
        let goes = factors.iter().filter(|(m, _)| m < name).count();
        let (out, p) = self.shift_factors(o, &appended, factors.len(), goes)?;
        Ok(Built((out, p)))
    }

    /// A rewrite of two neighbouring factors, carried to the whole.
    fn spread(
        &mut self,
        o: &mut dyn Oracle,
        factors: &[(Rc<str>, u32)],
        at: usize,
        collect: Proof,
    ) -> Checked<Proof> {
        let head = &factors[..at];
        let rest = &factors[at + 2..];
        let a = spell_factor(&factors[at]);
        let b = spell_factor(&factors[at + 1]);
        let total =
            spell_factor(&(factors[at].0.clone(), factors[at].1 + factors[at + 1].1));
        let tail: Vec<String> = rest.iter().map(spell_factor).collect();
        if head.is_empty() {
            return Ok(self.lift(o, collect, &op(&a, &b, MUL), &total, &tail, MUL));
        }
        let prefix = spell_monomial(&head.to_vec());
        let p0 = self.factors_cc(o, head)?;
        let p1 = self.factor_cc(o, &factors[at].0, factors[at].1)?;
        let p2 = self.factor_cc(o, &factors[at + 1].0, factors[at + 1].1)?;
        let outer = op(&op(&prefix, &a, MUL), &b, MUL);
        let inner_pair = op(&prefix, &op(&a, &b, MUL), MUL);
        let exposed = {
            let bb = o.b();
            let law = bb.ap(
                "mulass",
                &binds! {"A" => &prefix, "B" => &a, "C" => &b},
                &[],
            );
            bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(a, "cc", "wcel"), "th" => t!(b, "cc", "wcel"),
                "ta" => t!(outer, inner_pair, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let moved = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => op(&a, &b, MUL), "B" => &total,
            "C" => &prefix, "F" => MUL},
            &[&collect],
        );
        let step = self.chain(
            o,
            &exposed,
            &moved,
            &outer,
            &inner_pair,
            &op(&prefix, &total, MUL),
        );
        Ok(self.lift(o, step, &outer, &op(&prefix, &total, MUL), &tail, MUL))
    }

    /// ( under -> ( M x. N ) = P ), two monomials merged.
    fn multiply_monomials(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Rc<str>, u32)],
        right: &[(Rc<str>, u32)],
    ) -> Checked<Route<(Monomial, Proof)>> {
        let start = op(
            &spell_monomial(&left.to_vec()),
            &spell_monomial(&right.to_vec()),
            MUL,
        );
        if right.is_empty() {
            let keep = spell_monomial(&left.to_vec());
            let fc = self.factors_cc(o, left)?;
            let b = o.b();
            let law = b.ap("mulrid", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(&keep, n(1), MUL), keep, "wceq")},
                &[&fc, &law],
            );
            return Ok(Built((left.to_vec(), p)));
        }
        if right.len() == 1 {
            return self.insert_factor(o, left, &right[0].0, right[0].1);
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let whole_m = spell_monomial(&right.to_vec());
        let prefix = spell_monomial(&rest.to_vec());
        let held = spell_monomial(&left.to_vec());
        let one = spell_factor(last);
        let p0 = self.factors_cc(o, left)?;
        let p1 = self.factors_cc(o, rest)?;
        let p2 = self.factor_cc(o, &last.0, last.1)?;
        let grouped = op(&op(&held, &prefix, MUL), &one, MUL);
        let peeled = {
            let b = o.b();
            let law = b.ap(
                "mulass",
                &binds! {"A" => &held, "B" => &prefix, "C" => &one},
                &[],
            );
            let inner = b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(held, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(one, "cc", "wcel"),
                "ta" => t!(grouped, op(&held, &whole_m, MUL), "wceq")},
                &[&p0, &p1, &p2, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &grouped, "B" => op(&held, &whole_m, MUL)},
                &[&inner],
            )
        };
        let (merged, inner) = take!(self.multiply_monomials(o, left, rest)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&held, &prefix, MUL),
            "B" => spell_monomial(&merged), "C" => &one, "F" => MUL},
            &[&inner],
        );
        let (out, placed) = take!(self.insert_factor(o, &merged, &last.0, last.1)?);
        let middle = op(&spell_monomial(&merged), &one, MUL);
        let first = self.chain(o, &peeled, &carried, &start, &grouped, &middle);
        let p = self.chain(o, &first, &placed, &start, &middle, &spell_monomial(&out));
        Ok(Built((out, p)))
    }

    // --- multiplying ----------------------------------------------------

    /// ( under -> ( a x. b ) = c ) for two whole numbers.
    fn positive_product(&mut self, o: &dyn Oracle, first: i64, second: i64) -> Proof {
        let (a, b) = (n(first as u32), n(second as u32));
        let claim = t!(op(a, b, MUL), n((first * second) as u32), "wceq");
        let bb = o.b();
        let held = if first == 0 {
            let law = bb.ap("mul02", &binds! {"A" => b}, &[]);
            self.mp(
                o,
                &t!(b, "cc", "wcel"),
                &claim,
                &Self::complex_label(second),
                &law,
            )
        } else if second == 0 {
            let law = bb.ap("mul01", &binds! {"A" => a}, &[]);
            self.mp(
                o,
                &t!(a, "cc", "wcel"),
                &claim,
                &Self::complex_label(first),
                &law,
            )
        } else if first == 1 {
            let law = bb.ap("mullid", &binds! {"A" => b}, &[]);
            self.mp(
                o,
                &t!(b, "cc", "wcel"),
                &claim,
                &Self::complex_label(second),
                &law,
            )
        } else if second == 1 {
            let law = bb.ap("mulrid", &binds! {"A" => a}, &[]);
            self.mp(
                o,
                &t!(a, "cc", "wcel"),
                &claim,
                &Self::complex_label(first),
                &law,
            )
        } else {
            return self.a1i_label(
                o,
                &claim,
                &format!("{first}t{second}e{}", first * second),
            );
        };
        self.a1i(o, &claim, &held)
    }

    /// ( under -> ( c x. d ) = e ), the coefficients as `spell` has them.
    ///
    /// Signs come off first — `mulneg1`, `mulneg2` and `mul2neg` say where
    /// the minus goes — and what is left is two whole numbers, which set.mm
    /// names a lemma for.
    fn coefficient_product(
        &mut self,
        o: &dyn Oracle,
        first: &Q,
        second: &Q,
    ) -> Route<Proof> {
        let total = first * second;
        let said = spell_coefficient(&total);
        let c = spell_coefficient(first);
        let d = spell_coefficient(second);
        let (Some(said), Some(c), Some(d)) = (said, c, d) else {
            return Route::no(format!(
                "{} x. {} is past one digit",
                show(first),
                show(second)
            ));
        };
        let (a, b) = (whole(first), whole(second));
        if a >= 0 && b >= 0 {
            return Built(self.positive_product(o, a, b));
        }
        let size = self.positive_product(o, a.abs(), b.abs());
        let whole_p = op(n(a.unsigned_abs() as u32), n(b.unsigned_abs() as u32), MUL);
        if a < 0 && b < 0 {
            let paired = self.pair(
                o,
                "mul2neg",
                n(a.unsigned_abs() as u32),
                n(b.unsigned_abs() as u32),
                &op(&c, &d, MUL),
                &whole_p,
            );
            return Built(self.chain(
                o,
                &paired,
                &size,
                &op(&c, &d, MUL),
                &whole_p,
                &said,
            ));
        }
        let label = if a < 0 { "mulneg1" } else { "mulneg2" };
        let paired = self.pair(
            o,
            label,
            n(a.unsigned_abs() as u32),
            n(b.unsigned_abs() as u32),
            &op(&c, &d, MUL),
            &t!(whole_p, "cneg"),
        );
        let negated = o.b().ap(
            "negeqd",
            &binds! {"ph" => &self.under, "A" => &whole_p, "B" => n((a * b).unsigned_abs() as u32)},
            &[&size],
        );
        Built(self.chain(
            o,
            &paired,
            &negated,
            &op(&c, &d, MUL),
            &t!(whole_p, "cneg"),
            &said,
        ))
    }

    /// A two-argument law of ℂ, applied to two numerals.
    fn pair(
        &mut self,
        o: &dyn Oracle,
        label: &str,
        left: &str,
        right: &str,
        before: &str,
        after: &str,
    ) -> Proof {
        let pl = self.number(o, crate::rules::digit_of(left).unwrap_or(0) as i64);
        let pr = self.number(o, crate::rules::digit_of(right).unwrap_or(0) as i64);
        let b = o.b();
        let law = b.ap(label, &binds! {"A" => left, "B" => right}, &[]);
        b.ap(
            "syl2anc",
            &binds! {"ph" => &self.under, "ps" => t!(left, "cc", "wcel"),
            "ch" => t!(right, "cc", "wcel"), "th" => t!(before, after, "wceq")},
            &[&pl, &pr, &law],
        )
    }

    /// ( under -> ( ( c x. M ) x. ( d x. N ) ) = ( e x. P ) ): `mul4` puts
    /// the two coefficients together and the two monomials together, and
    /// then each side is its own problem.
    fn term_times_term(
        &mut self,
        o: &mut dyn Oracle,
        one: &(Monomial, Q),
        two: &(Monomial, Q),
    ) -> Checked<Route<((Monomial, Q), Proof)>> {
        let ((first, weight), (second, other)) = (one, two);
        let c = coeff(weight);
        let d = coeff(other);
        let (m, nn) = (spell_monomial(first), spell_monomial(second));
        let (a, b) = (Self::spell_term(one), Self::spell_term(two));
        let pc = self.coefficient(o, weight);
        let pm = self.monomial_cc(o, first)?;
        let pd = self.coefficient(o, other);
        let pn = self.monomial_cc(o, second)?;
        let regrouped = {
            let bb = o.b();
            let left_pair = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(c, "cc", "wcel"), "ch" => t!(m, "cc", "wcel")},
                &[&pc, &pm],
            );
            let right_pair = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(d, "cc", "wcel"), "ch" => t!(nn, "cc", "wcel")},
                &[&pd, &pn],
            );
            let both = bb.ap(
                "jca",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(c, "cc", "wcel"), t!(m, "cc", "wcel"), "wa"),
                "ch" => t!(t!(d, "cc", "wcel"), t!(nn, "cc", "wcel"), "wa")},
                &[&left_pair, &right_pair],
            );
            let law = bb.ap(
                "mul4",
                &binds! {"A" => &c, "B" => &m, "C" => &d, "D" => &nn},
                &[],
            );
            bb.ap(
                "syl",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(t!(c, "cc", "wcel"), t!(m, "cc", "wcel"), "wa"),
                           t!(t!(d, "cc", "wcel"), t!(nn, "cc", "wcel"), "wa"), "wa"),
                "ch" => t!(op(&a, &b, MUL), op(&op(&c, &d, MUL), &op(&m, &nn, MUL), MUL), "wceq")},
                &[&both, &law],
            )
        };
        let fl: Monomial = first.clone();
        let sl: Monomial = second.clone();
        let (merged, monomial) = take!(self.multiply_monomials(o, &fl, &sl)?);
        let total = weight * other;
        let out = (merged.clone(), total.clone());
        let times = match self.coefficient_product(o, weight, other) {
            Built(p) => p,
            Declined(d) => return Ok(Declined(d)),
        };
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&c, &d, MUL), "B" => coeff(&total),
            "C" => op(&m, &nn, MUL), "D" => spell_monomial(&merged), "F" => MUL},
            &[&times, &monomial],
        );
        let p = self.chain(
            o,
            &regrouped,
            &lifted,
            &op(&a, &b, MUL),
            &op(&op(&c, &d, MUL), &op(&m, &nn, MUL), MUL),
            &Self::spell_term(&out),
        );
        Ok(Built((out, p)))
    }

    /// ( under -> ( t x. spell_run(right) ) = spell_run(product) ): `adddi`
    /// takes the right-hand run apart from its end, one term at a time, and
    /// each product of two terms is `term_times_term`.
    fn term_times_run(
        &mut self,
        o: &mut dyn Oracle,
        one: &(Monomial, Q),
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let term = Self::spell_term(one);
        let start = op(&term, &Self::spell_run(right), MUL);
        if right.is_empty() {
            let cc = self.term_cc(o, &one.0, &one.1)?;
            let b = o.b();
            let law = b.ap("mul01", &binds! {"A" => &term}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(op(&term, n(0), MUL), n(0), "wceq")},
                &[&cc, &law],
            );
            return Ok(Built((Vec::new(), p)));
        }
        if right.len() == 1 {
            let (out, proof) = take!(self.term_times_term(o, one, &right[0])?);
            return Ok(Built((vec![out], proof)));
        }
        let (rest, last) = (&right[..right.len() - 1], &right[right.len() - 1]);
        let prefix = Self::spell_run(rest);
        let tail = Self::spell_term(last);
        let p0 = self.term_cc(o, &one.0, &one.1)?;
        let p1 = self.run_cc(o, rest)?;
        let p2 = self.term_cc(o, &last.0, &last.1)?;
        let apart = op(&op(&term, &prefix, MUL), &op(&term, &tail, MUL), ADD);
        let spread = {
            let b = o.b();
            let law = b.ap(
                "adddi",
                &binds! {"A" => &term, "B" => &prefix, "C" => &tail},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(term, "cc", "wcel"),
                "ch" => t!(prefix, "cc", "wcel"), "th" => t!(tail, "cc", "wcel"),
                "ta" => t!(start, apart, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let (inner, first) = take!(self.term_times_run(o, one, rest)?);
        let (single, second) = take!(self.term_times_term(o, one, last)?);
        let both = op(&Self::spell_run(&inner), &Self::spell_term(&single), ADD);
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&term, &prefix, MUL),
            "B" => Self::spell_run(&inner), "C" => op(&term, &tail, MUL),
            "D" => Self::spell_term(&single), "F" => ADD},
            &[&first, &second],
        );
        let lined = self.chain(o, &spread, &lifted, &start, &apart, &both);
        let (out, placed) = take!(self.insert(o, &inner, &single.0, &single.1)?);
        let p = self.chain(o, &lined, &placed, &start, &both, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> ( spell_run(left) x. spell_run(right) ) = the product ):
    /// `adddir` takes the left-hand run apart, and what each of its terms
    /// does to the whole right-hand run is `term_times_run`. The pieces are
    /// then added, which is what `add` is for.
    pub fn multiply(
        &mut self,
        o: &mut dyn Oracle,
        left: &[(Monomial, Q)],
        right: &[(Monomial, Q)],
    ) -> Checked<Route<(Run, Proof)>> {
        let start = op(&Self::spell_run(left), &Self::spell_run(right), MUL);
        if left.is_empty() {
            let keep = Self::spell_run(right);
            let rc = self.run_cc(o, right)?;
            let b = o.b();
            let law = b.ap("mul02", &binds! {"A" => &keep}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(keep, "cc", "wcel"),
                "ch" => t!(op(n(0), &keep, MUL), n(0), "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((Vec::new(), p)));
        }
        if left.len() == 1 {
            return self.term_times_run(o, &left[0], right);
        }
        let (rest, last) = (&left[..left.len() - 1], &left[left.len() - 1]);
        let prefix = Self::spell_run(rest);
        let tail = Self::spell_term(last);
        let whole_run = Self::spell_run(right);
        let p0 = self.run_cc(o, rest)?;
        let p1 = self.term_cc(o, &last.0, &last.1)?;
        let p2 = self.run_cc(o, right)?;
        let apart = op(
            &op(&prefix, &whole_run, MUL),
            &op(&tail, &whole_run, MUL),
            ADD,
        );
        let spread = {
            let b = o.b();
            let law = b.ap(
                "adddir",
                &binds! {"A" => &prefix, "B" => &tail, "C" => &whole_run},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(prefix, "cc", "wcel"),
                "ch" => t!(tail, "cc", "wcel"), "th" => t!(whole_run, "cc", "wcel"),
                "ta" => t!(start, apart, "wceq")},
                &[&p0, &p1, &p2, &law],
            )
        };
        let (inner, first) = take!(self.multiply(o, rest, right)?);
        let (outer, second) = take!(self.term_times_run(o, last, right)?);
        let both = op(&Self::spell_run(&inner), &Self::spell_run(&outer), ADD);
        let lifted = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&prefix, &whole_run, MUL),
            "B" => Self::spell_run(&inner), "C" => op(&tail, &whole_run, MUL),
            "D" => Self::spell_run(&outer), "F" => ADD},
            &[&first, &second],
        );
        let lined = self.chain(o, &spread, &lifted, &start, &apart, &both);
        let (out, joined) = take!(self.add(o, &inner, &outer)?);
        let p = self.chain(o, &lined, &joined, &start, &both, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> ( spell_run(items) ^ k ) = spell_run(the power) ).
    ///
    /// `expp1` peels one factor off, and it states the exponent as `N + 1`,
    /// so the numeral is rewritten that way round first.
    fn power(
        &mut self,
        o: &mut dyn Oracle,
        items: &[(Monomial, Q)],
        times: u32,
    ) -> Checked<Route<(Run, Proof)>> {
        let run = Self::spell_run(items);
        let start = op(&run, n(times), EXP);
        let unit: Run = vec![(Vec::new(), q(1))];
        if times == 0 {
            let rc = self.run_cc(o, items)?;
            let first = {
                let b = o.b();
                let law = b.ap("exp0", &binds! {"A" => &run}, &[]);
                b.ap(
                    "syl",
                    &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                    "ch" => t!(start, n(1), "wceq")},
                    &[&rc, &law],
                )
            };
            let one = self.one_as_term(o);
            let p =
                self.chain(o, &first, &one, &start, n(1), &Self::spell_term(&unit[0]));
            return Ok(Built((unit, p)));
        }
        if times == 1 {
            let rc = self.run_cc(o, items)?;
            let b = o.b();
            let law = b.ap("exp1", &binds! {"A" => &run}, &[]);
            let p = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(start, run, "wceq")},
                &[&rc, &law],
            );
            return Ok(Built((items.to_vec(), p)));
        }
        let below = n(times - 1);
        let stepped_from = match self.coefficient_sum(o, &q(times as i64 - 1), &q(1)) {
            Built(p) => p,
            Declined(d) => return Ok(Declined(d)),
        };
        let rc = self.run_cc(o, items)?;
        let ix = self.index(o, times as i64 - 1);
        let peeled_exponent = op(below, n(1), ADD);
        let stepped = {
            let b = o.b();
            let turned = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &peeled_exponent, "B" => n(times)},
                &[&stepped_from],
            );
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => n(times), "B" => &peeled_exponent,
                "C" => &run, "F" => EXP},
                &[&turned],
            );
            let law = b.ap("expp1", &binds! {"A" => &run, "N" => below}, &[]);
            let second = b.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(below, "cn0", "wcel"),
                "th" => t!(op(&run, &peeled_exponent, EXP), op(&op(&run, below, EXP), &run, MUL), "wceq")},
                &[&rc, &ix, &law],
            );
            self.chain(
                o,
                &first,
                &second,
                &start,
                &op(&run, &peeled_exponent, EXP),
                &op(&op(&run, below, EXP), &run, MUL),
            )
        };
        let (inner, smaller) = take!(self.power(o, items, times - 1)?);
        let carried = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => op(&run, below, EXP),
            "B" => Self::spell_run(&inner), "C" => &run, "F" => MUL},
            &[&smaller],
        );
        let (out, product) = take!(self.multiply(o, &inner, items)?);
        let middle = op(&Self::spell_run(&inner), &run, MUL);
        let first = self.chain(
            o,
            &stepped,
            &carried,
            &start,
            &op(&op(&run, below, EXP), &run, MUL),
            &middle,
        );
        let p =
            self.chain(o, &first, &product, &start, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// ( under -> 1 = ( 1 x. 1 ) ), the canonical form of one.
    fn one_as_term(&mut self, o: &dyn Oracle) -> Proof {
        let product = self.positive_product(o, 1, 1);
        o.b().ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(n(1), n(1), MUL), "B" => n(1)},
            &[&product],
        )
    }

    // --- the driver -----------------------------------------------------

    /// (items, ( under -> term = spell_run(items) )).
    ///
    /// Recursion on the term, not a search: at each node the children are
    /// already canonical and what remains is one of the operations above. A
    /// subterm this does not recognise is an atom, and the oracle is asked
    /// once for its membership.
    pub fn normalize(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<(Run, Proof)>> {
        let said = term.rpn(labels).to_string();
        if term.variable().is_none() {
            if let Some(value) = term.label().and_then(crate::rules::digit_of) {
                let value = value as i64;
                if value == 0 {
                    // The empty run, not a term of weight zero: a canonical
                    // form holds no such term, and one left in it would be
                    // carried through every sum it took part in.
                    return Ok(Built((Vec::new(), self.same(o, n(0)))));
                }
                if value == 1 {
                    return Ok(Built((vec![(Vec::new(), q(1))], self.one_as_term(o))));
                }
                let product = self.positive_product(o, value, 1);
                let p = o.b().ap(
                    "eqcomd",
                    &binds! {"ph" => &self.under, "A" => op(n(value as u32), n(1), MUL),
                    "B" => n(value as u32)},
                    &[&product],
                );
                return Ok(Built((vec![(Vec::new(), q(value))], p)));
            }
        }
        if term.variable().is_none()
            && term.label() == Some("cneg")
            && term.children().len() == 1
        {
            let (items, proof) =
                take!(self.normalize(o, &term.children()[0], labels)?);
            let inner = term.children()[0].rpn(labels).to_string();
            return self.negated(o, &inner, &items, proof, &said);
        }
        if term.variable().is_none()
            && term.label() == Some("co")
            && term.children().len() == 3
        {
            let how = term.children()[2].rpn(labels).to_string();
            let (left, right) = (&term.children()[0], &term.children()[1]);
            if how == field::ADD || how == field::SUB || how == field::MUL {
                return self.binary(o, &how, left, right, labels, &said);
            }
            if how == field::EXP {
                // The exponent rule, as `field` states it where the same
                // claim is decided: a numeral exponent is expanded, and any
                // other leaves the whole power an atom.
                if let Some(times) = field::whole_number(right) {
                    if (0..=9).contains(&times) {
                        let times = times as u32;
                        let (inner, proof) = take!(self.normalize(o, left, labels)?);
                        let (out, raised) = take!(self.power(o, &inner, times)?);
                        let moved = o.b().ap(
                            "oveq1d",
                            &binds! {"ph" => &self.under, "A" => &*left.rpn(labels),
                            "B" => Self::spell_run(&inner), "C" => n(times), "F" => EXP},
                            &[&proof],
                        );
                        let p = self.chain(
                            o,
                            &moved,
                            &raised,
                            &said,
                            &op(&Self::spell_run(&inner), n(times), EXP),
                            &Self::spell_run(&out),
                        );
                        return Ok(Built((out, p)));
                    }
                }
                return self.as_atom(o, &said).map(Built);
            }
            if how == field::DIV {
                return Ok(Route::no(format!(
                    "{said} divides, which is cross-multiplied"
                )));
            }
        }
        self.as_atom(o, &said).map(Built)
    }

    /// A subterm nothing above recognises, as `( 1 x. ( t ^ 1 ) )`.
    fn as_atom(&mut self, o: &mut dyn Oracle, said: &str) -> Checked<(Run, Proof)> {
        let raised = op(said, n(1), EXP);
        let atom = o.atom(said)?;
        let name: Rc<str> = Rc::from(said);
        let fc = self.factor_cc(o, &name, 1)?;
        let b = o.b();
        let law = b.ap("exp1", &binds! {"A" => said}, &[]);
        let inner = b.ap(
            "syl",
            &binds! {"ph" => &self.under, "ps" => t!(said, "cc", "wcel"),
            "ch" => t!(raised, said, "wceq")},
            &[&atom, &law],
        );
        let first = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => &raised, "B" => said},
            &[&inner],
        );
        let law = b.ap("mullid", &binds! {"A" => &raised}, &[]);
        let inner = b.ap(
            "syl",
            &binds! {"ph" => &self.under, "ps" => t!(raised, "cc", "wcel"),
            "ch" => t!(op(n(1), &raised, MUL), raised, "wceq")},
            &[&fc, &law],
        );
        let second = b.ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(n(1), &raised, MUL), "B" => &raised},
            &[&inner],
        );
        let p = self.chain(o, &first, &second, said, &raised, &op(n(1), &raised, MUL));
        Ok((vec![(vec![(name, 1)], q(1))], p))
    }

    /// -u X, taken as ( -u 1 ) x. X so that `multiply` does the work. The
    /// minus one is written the way a canonical form writes a constant,
    /// `( -u 1 x. 1 )`, before `multiply` will take it, which `mulrid`
    /// supplies.
    fn negated(
        &mut self,
        o: &mut dyn Oracle,
        inner: &str,
        items: &[(Monomial, Q)],
        proof: Proof,
        said: &str,
    ) -> Checked<Route<(Run, Proof)>> {
        let run = Self::spell_run(items);
        let minus: Run = vec![(Vec::new(), q(-1))];
        let bare = t!(n(1), "cneg");
        let unit = Self::spell_run(&minus);
        let rc = self.run_cc(o, items)?;
        let inner_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => inner, "B" => &run, "C" => "cc"},
            &[&proof, &rc],
        );
        let becomes = {
            let b = o.b();
            let law = b.ap("mulm1", &binds! {"A" => inner}, &[]);
            let turned = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(inner, "cc", "wcel"),
                "ch" => t!(op(&bare, inner, MUL), said, "wceq")},
                &[&inner_cc, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => op(&bare, inner, MUL), "B" => said},
                &[&turned],
            )
        };
        let inside = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => inner, "B" => &run, "C" => &bare, "F" => MUL},
            &[&proof],
        );
        let minus_cc = self.coefficient(o, &q(-1));
        let spelt = {
            let b = o.b();
            let law = b.ap("mulrid", &binds! {"A" => &bare}, &[]);
            let turned = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(bare, "cc", "wcel"),
                "ch" => t!(unit, bare, "wceq")},
                &[&minus_cc, &law],
            );
            let back = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &unit, "B" => &bare},
                &[&turned],
            );
            b.ap(
                "oveq1d",
                &binds! {"ph" => &self.under, "A" => &bare, "B" => &unit, "C" => &run, "F" => MUL},
                &[&back],
            )
        };
        let (out, product) = take!(self.multiply(o, &minus, items)?);
        let one = self.chain(
            o,
            &becomes,
            &inside,
            said,
            &op(&bare, inner, MUL),
            &op(&bare, &run, MUL),
        );
        let two = self.chain(
            o,
            &one,
            &spelt,
            said,
            &op(&bare, &run, MUL),
            &op(&unit, &run, MUL),
        );
        let p = self.chain(
            o,
            &two,
            &product,
            said,
            &op(&unit, &run, MUL),
            &Self::spell_run(&out),
        );
        Ok(Built((out, p)))
    }

    /// X - Y, turned into X + -u Y, which the sum side already does:
    /// `negsub` states the two as equal one way round, so it is read
    /// backwards, and the negation is then the case already written.
    #[allow(clippy::too_many_arguments)]
    fn subtracted(
        &mut self,
        o: &mut dyn Oracle,
        la: &str,
        lb: &str,
        first: &[(Monomial, Q)],
        one: Proof,
        second: &[(Monomial, Q)],
        two: Proof,
        said: &str,
    ) -> Checked<Route<(Run, Proof)>> {
        let rc1 = self.run_cc(o, first)?;
        let a_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => la, "B" => Self::spell_run(first), "C" => "cc"},
            &[&one, &rc1],
        );
        let rc2 = self.run_cc(o, second)?;
        let b_cc = o.b().ap(
            "eqeltrd",
            &binds! {"ph" => &self.under, "A" => lb, "B" => Self::spell_run(second), "C" => "cc"},
            &[&two, &rc2],
        );
        let minus = t!(lb, "cneg");
        let plus = op(la, &minus, ADD);
        let turned = {
            let b = o.b();
            let law = b.ap("negsub", &binds! {"A" => la, "B" => lb}, &[]);
            let inner = b.ap(
                "syl2anc",
                &binds! {"ph" => &self.under, "ps" => t!(la, "cc", "wcel"),
                "ch" => t!(lb, "cc", "wcel"), "th" => t!(plus, said, "wceq")},
                &[&a_cc, &b_cc, &law],
            );
            b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => &plus, "B" => said},
                &[&inner],
            )
        };
        let (negated, backwards) = take!(self.negated(o, lb, second, two, &minus)?);
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => la, "B" => Self::spell_run(first),
            "C" => &minus, "D" => Self::spell_run(&negated), "F" => ADD},
            &[&one, &backwards],
        );
        let (out, combined) = take!(self.add(o, first, &negated)?);
        let middle = op(&Self::spell_run(first), &Self::spell_run(&negated), ADD);
        let head = self.chain(o, &turned, &joined, said, &plus, &middle);
        let p = self.chain(o, &head, &combined, said, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    /// `+`, `-` or `x.` with both sides taken to canonical form first.
    fn binary(
        &mut self,
        o: &mut dyn Oracle,
        how: &str,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &str,
    ) -> Checked<Route<(Run, Proof)>> {
        let (first, one) = take!(self.normalize(o, left, labels)?);
        let (second, two) = take!(self.normalize(o, right, labels)?);
        if how == field::SUB {
            return self.subtracted(
                o,
                &left.rpn(labels),
                &right.rpn(labels),
                &first,
                one,
                &second,
                two,
                said,
            );
        }
        let what = if how == field::ADD { ADD } else { MUL };
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => &*left.rpn(labels),
            "B" => Self::spell_run(&first), "C" => &*right.rpn(labels),
            "D" => Self::spell_run(&second), "F" => what},
            &[&one, &two],
        );
        let made = if how == field::ADD {
            self.add(o, &first, &second)?
        } else {
            self.multiply(o, &first, &second)?
        };
        let (out, combined) = take!(made);
        let middle = op(&Self::spell_run(&first), &Self::spell_run(&second), what);
        let p =
            self.chain(o, &joined, &combined, said, &middle, &Self::spell_run(&out));
        Ok(Built((out, p)))
    }

    // --- quotients ------------------------------------------------------
    //
    // A canonical form with a denominator is a pair rather than a polynomial
    // with fractions in it. Everything above keeps working on the numerator,
    // because its coefficients stay whole; what is added here is bookkeeping
    // on a second polynomial, and the four laws that say how the two travel
    // through a sum, a product, a division and a power.

    /// The canonical term for a pair, or for a numerator on its own.
    pub fn spell_quotient(
        over: &[(Monomial, Q)],
        under: Option<&[(Monomial, Q)]>,
    ) -> String {
        match under {
            None => Self::spell_run(over),
            Some(under) => op(&Self::spell_run(over), &Self::spell_run(under), DIV),
        }
    }

    /// ( under -> d e. CC ) and ( under -> d =/= 0 ) for a denominator.
    ///
    /// A denominator that is a number says for itself that it is not zero,
    /// since the canonical form of a constant is `( n x. 1 )` and the scope
    /// knows only about the `n`.
    fn denominator(
        &mut self,
        o: &mut dyn Oracle,
        under: &[(Monomial, Q)],
    ) -> Checked<Route<(Proof, Proof)>> {
        let said = Self::spell_run(under);
        if under.len() == 1 {
            let (monomial, weight) = &under[0];
            if weight.is_integer() && !weight.is_zero() {
                let apart = take!(self.term_apart(o, monomial, weight)?);
                let rc = self.run_cc(o, under)?;
                return Ok(Built((rc, apart)));
            }
        }
        // What the page wrote comes first, then what was kept while the
        // denominator was made (`keep_nonzero`), then the oracle's search.
        let page = if self.written {
            o.written(&said)?
        } else {
            None
        };
        if let Some(page) = page {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, page)));
        }
        if let Some(kept) = self.nonzero.get(&said).cloned() {
            let rc = self.run_cc(o, under)?;
            return Ok(Built((rc, kept)));
        }
        if !self.apart {
            return Ok(Route::no("nothing can say a denominator is not zero"));
        }
        let rc = self.run_cc(o, under)?;
        let apart = o.apart(&said)?;
        Ok(Built((rc, apart)))
    }

    /// Keep that `run` is not zero, from `whole` not being zero and
    /// ( under -> whole = run ).
    ///
    /// A denominator the normaliser makes by multiplying two out is one the
    /// page never wrote: 2/k − 2/(k + 1) lands on k² + k. That it is not
    /// zero is known where it is made, from its factors, and not afterwards,
    /// when it is one polynomial.
    fn keep_nonzero(
        &mut self,
        o: &dyn Oracle,
        whole: &str,
        run: &[(Monomial, Q)],
        apart: &Proof,
        equal: &Proof,
    ) {
        let said = Self::spell_run(run);
        if self.nonzero.contains_key(&said) || run.len() == 1 {
            return;
        }
        let b = o.b();
        let moved = b.ap(
            "neeq1d",
            &binds! {"ph" => &self.under, "A" => whole, "B" => &said, "C" => "cc0"},
            &[equal],
        );
        let kept = b.ap(
            "mpbid",
            &binds! {"ph" => &self.under, "ps" => t!(whole, "cc0", "wne"),
            "ch" => t!(said, "cc0", "wne")},
            &[apart, &moved],
        );
        self.nonzero.insert(said, kept);
    }

    /// `keep_nonzero` for a denominator that is two multiplied out.
    fn keep_product(
        &mut self,
        o: &mut dyn Oracle,
        one: &[(Monomial, Q)],
        other: &[(Monomial, Q)],
        run: &[(Monomial, Q)],
        equal: &Proof,
    ) -> Checked<()> {
        let first = self.denominator(o, one)?;
        let second = self.denominator(o, other)?;
        let (Built((held_a, apart_a)), Built((held_b, apart_b))) = (first, second)
        else {
            return Ok(());
        };
        let (a, b) = (Self::spell_run(one), Self::spell_run(other));
        let apart = o.b().ap(
            "mulne0d",
            &binds! {"ph" => &self.under, "A" => &a, "B" => &b},
            &[&held_a, &held_b, &apart_a, &apart_b],
        );
        self.keep_nonzero(o, &op(&a, &b, MUL), run, &apart, equal);
        Ok(())
    }

    /// ( under -> ( c x. M ) =/= 0 ), for a denominator of one term.
    ///
    /// The scope knows about the atoms; the canonical form it is asked about
    /// is `( c x. ( x ^ k ) )`, which the scope has never heard of. A product
    /// is not zero when neither side is, and a power is not when what it
    /// raises is not, so the whole of it comes off the atoms the scope does
    /// know.
    fn term_apart(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
        weight: &Q,
    ) -> Checked<Route<Proof>> {
        let digit = coeff(weight);
        let numerator = whole(&Q::from_integer(weight.numer().clone()));
        let magnitude = numerator.abs();
        let mut nonzero = self.a1i_label(
            o,
            &t!(n(magnitude as u32), "cc0", "wne"),
            &Self::apart_label(magnitude),
        );
        if numerator < 0 {
            let num = self.number(o, magnitude);
            nonzero = o.b().ap(
                "negne0d",
                &binds! {"ph" => &self.under, "A" => n(magnitude as u32)},
                &[&num, &nonzero],
            );
        }
        let spelt = spell_monomial(monomial);
        let apart = take!(self.monomial_apart(o, monomial)?);
        let c = self.coefficient(o, weight);
        let m = self.monomial_cc(o, monomial)?;
        Ok(Built(o.b().ap(
            "mulne0d",
            &binds! {"ph" => &self.under, "A" => &digit, "B" => &spelt},
            &[&c, &m, &nonzero, &apart],
        )))
    }

    /// ( under -> M =/= 0 ), the empty one being one.
    fn monomial_apart(
        &mut self,
        o: &mut dyn Oracle,
        monomial: &Monomial,
    ) -> Checked<Route<Proof>> {
        if monomial.is_empty() {
            return Ok(Built(self.a1i_label(
                o,
                &t!(n(1), "cc0", "wne"),
                &Self::apart_label(1),
            )));
        }
        let mut out: Option<(Proof, String, Proof)> = None;
        for (name, power) in monomial {
            let spelt = op(name, n(*power), EXP);
            let apart = take!(self.atom_apart(o, name)?);
            let atom = o.atom(name)?;
            let wi = self.whole_index(o, *power);
            let one = o.b().ap(
                "expne0d",
                &binds! {"ph" => &self.under, "A" => &**name, "N" => n(*power)},
                &[&atom, &apart, &wi],
            );
            let mine = self.factor_cc(o, name, *power)?;
            out = Some(match out {
                None => (one, spelt, mine),
                Some((acc, running, held)) => {
                    let b = o.b();
                    let next = b.ap(
                        "mulne0d",
                        &binds! {"ph" => &self.under, "A" => &running, "B" => &spelt},
                        &[&held, &mine, &acc, &one],
                    );
                    let held = b.ap(
                        "mulcld",
                        &binds! {"ph" => &self.under, "A" => &running, "B" => &spelt},
                        &[&held, &mine],
                    );
                    (next, op(&running, &spelt, MUL), held)
                }
            });
        }
        Ok(Built(out.expect("a monomial of one factor at least").0))
    }

    /// ( under -> k e. ZZ ), which `expne0d` asks for.
    fn whole_index(&self, o: &dyn Oracle, power: u32) -> Proof {
        self.a1i_label(o, &t!(n(power), "cz", "wcel"), &format!("{power}z"))
    }

    /// A numerator on its own, given the denominator of one it hides: `div1`
    /// says a term over one is the term, so it is what promotes a polynomial
    /// into the pair the laws below want.
    pub fn as_quotient(
        &mut self,
        o: &mut dyn Oracle,
        over: Run,
        under: Option<Run>,
        proof: Proof,
        said: &str,
    ) -> Checked<(Run, Run, Proof)> {
        if let Some(under) = under {
            return Ok((over, under, proof));
        }
        let one: Run = vec![(Vec::new(), q(1))];
        let run = Self::spell_run(&over);
        let unit = Self::spell_run(&one);
        // One in canonical form is `( 1 x. 1 )`, so the denominator is tidied
        // to that first.
        let unit_proof = self.one_as_term(o);
        let rc = self.run_cc(o, &over)?;
        let back = {
            let b = o.b();
            let turned = b.ap(
                "eqcomd",
                &binds! {"ph" => &self.under, "A" => n(1), "B" => &unit},
                &[&unit_proof],
            );
            let first = b.ap(
                "oveq2d",
                &binds! {"ph" => &self.under, "A" => &unit, "B" => n(1), "C" => &run, "F" => DIV},
                &[&turned],
            );
            let law = b.ap("div1", &binds! {"A" => &run}, &[]);
            let second = b.ap(
                "syl",
                &binds! {"ph" => &self.under, "ps" => t!(run, "cc", "wcel"),
                "ch" => t!(op(&run, n(1), DIV), run, "wceq")},
                &[&rc, &law],
            );
            self.chain(
                o,
                &first,
                &second,
                &op(&run, &unit, DIV),
                &op(&run, n(1), DIV),
                &run,
            )
        };
        let flipped = o.b().ap(
            "eqcomd",
            &binds! {"ph" => &self.under, "A" => op(&run, &unit, DIV), "B" => &run},
            &[&back],
        );
        let p = self.chain(o, &proof, &flipped, said, &run, &op(&run, &unit, DIV));
        Ok((over, one, p))
    }

    /// (over, under, ( under -> term = over / under )).
    ///
    /// `under` is None where the term divides nothing, and the proof is then
    /// of the numerator alone: a term that divides nothing must not be made
    /// to carry a denominator of one, or every caller's output would change.
    pub fn normalize_quotient(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<Quotiented>> {
        let said = term.rpn(labels).to_string();
        if !divides(term, labels) {
            let (items, proof) = take!(self.normalize(o, term, labels)?);
            return Ok(Built((items, None, proof)));
        }
        if term.variable().is_none()
            && term.label() == Some("co")
            && term.children().len() == 3
        {
            let how = term.children()[2].rpn(labels).to_string();
            let (left, right) = (&term.children()[0], &term.children()[1]);
            if how == field::DIV {
                return self.quotient_of(o, left, right, labels, &said);
            }
            if how == field::ADD || how == field::SUB || how == field::MUL {
                return self.quotient_joined(o, &how, left, right, labels, &said);
            }
            if how == field::EXP {
                return self.quotient_raised(o, left, right, labels, &said);
            }
        }
        Ok(Route::no(format!(
            "{said} divides somewhere this does not reach"
        )))
    }

    /// `a / b`, where what is below may divide as well: `divdiv1` is what
    /// folds a division under a division into one.
    fn quotient_of(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &str,
    ) -> Checked<Route<Quotiented>> {
        let (over, under, first) = take!(self.normalize_quotient(o, left, labels)?);
        let (below, beneath, second) =
            take!(self.normalize_quotient(o, right, labels)?);
        if beneath.is_some() {
            return self.divided_by_quotient(o, left, right, labels, said);
        }
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => &*left.rpn(labels),
            "B" => Self::spell_quotient(&over, under.as_deref()),
            "C" => &*right.rpn(labels), "D" => Self::spell_run(&below), "F" => DIV},
            &[&first, &second],
        );
        let Some(under) = under else {
            return Ok(Built((over, Some(below), joined)));
        };
        // ( A / B ) / C is A / ( B x. C ), and the new denominator is then
        // the two of them multiplied out.
        let top = Self::spell_run(&over);
        let bottom = Self::spell_run(&under);
        let outer = Self::spell_run(&below);
        let p1 = self.pair_of(o, &under)?;
        let p2 = self.pair_of(o, &below)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let rc = self.run_cc(o, &over)?;
        let folded = {
            let b = o.b();
            let law = b.ap(
                "divdiv1",
                &binds! {"A" => &top, "B" => &bottom, "C" => &outer},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(top, "cc", "wcel"),
                "ch" => t!(t!(bottom, "cc", "wcel"), t!(bottom, "cc0", "wne"), "wa"),
                "th" => t!(t!(outer, "cc", "wcel"), t!(outer, "cc0", "wne"), "wa"),
                "ta" => t!(op(&op(&top, &bottom, DIV), &outer, DIV),
                           op(&top, &op(&bottom, &outer, MUL), DIV), "wceq")},
                &[&rc, &p1, &p2, &law],
            )
        };
        let (made, product) = take!(self.multiply(o, &under, &below)?);
        self.keep_product(o, &under, &below, &made, &product)?;
        let first_link = self.chain(
            o,
            &joined,
            &folded,
            said,
            &op(&op(&top, &bottom, DIV), &outer, DIV),
            &op(&top, &op(&bottom, &outer, MUL), DIV),
        );
        let second_link = o.b().ap(
            "oveq2d",
            &binds! {"ph" => &self.under, "A" => op(&bottom, &outer, MUL),
            "B" => Self::spell_run(&made), "C" => &top, "F" => DIV},
            &[&product],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &op(&top, &op(&bottom, &outer, MUL), DIV),
            &op(&top, &Self::spell_run(&made), DIV),
        );
        Ok(Built((over, Some(made), p)))
    }

    /// `a / ( c / d )`, normalised as `( a x. d ) / c` (`divdiv2`). What is
    /// asked of c is asked of it as written (`written_pair`). A divisor that
    /// divides only once normalised, a sum of quotients, is not reached.
    fn divided_by_quotient(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &str,
    ) -> Checked<Route<Quotiented>> {
        if right.variable().is_some()
            || right.label() != Some("co")
            || right.children().len() != 3
            || &*right.children()[2].rpn(labels) != DIV
        {
            return Ok(Route::no(format!(
                "{said} divides by something that divides"
            )));
        }
        let (c, d) = (&right.children()[0], &right.children()[1]);
        let (a_s, c_s, d_s) = (
            left.rpn(labels).to_string(),
            c.rpn(labels).to_string(),
            d.rpn(labels).to_string(),
        );
        let p1 = self.written_pair(o, c, labels)?;
        let p2 = self.written_pair(o, d, labels)?;
        let (p1, p2) = (take!(p1), take!(p2));
        // c is the new denominator, and its canonical form is asked later.
        let spread = self.normalize(o, c, labels)?;
        let apart = self.written_apart(o, c, labels)?;
        if let (Built((items, equal)), Built(apart)) = (&spread, &apart) {
            self.keep_nonzero(o, &c_s, items, apart, equal);
        }
        let flipped = op(&op(&a_s, &d_s, MUL), &c_s, DIV);
        let atom = o.atom(&a_s)?;
        let turned = {
            let b = o.b();
            let law = b.ap(
                "divdiv2",
                &binds! {"A" => &a_s, "B" => &c_s, "C" => &d_s},
                &[],
            );
            b.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(a_s, "cc", "wcel"),
                "ch" => t!(t!(c_s, "cc", "wcel"), t!(c_s, "cc0", "wne"), "wa"),
                "th" => t!(t!(d_s, "cc", "wcel"), t!(d_s, "cc0", "wne"), "wa"),
                "ta" => t!(said, flipped, "wceq")},
                &[&atom, &p1, &p2, &law],
            )
        };
        let rebuilt = Term::apply(
            "co",
            vec![
                Term::apply(
                    "co",
                    vec![left.clone(), d.clone(), Term::apply(MUL, vec![])],
                ),
                c.clone(),
                right.children()[2].clone(),
            ],
        );
        let (over, under, proof) = take!(self.normalize_quotient(o, &rebuilt, labels)?);
        let p = self.chain(
            o,
            &turned,
            &proof,
            said,
            &flipped,
            &Self::spell_quotient(&over, under.as_deref()),
        );
        Ok(Built((over, under, p)))
    }

    /// ( under -> ( t e. CC /\ t =/= 0 ) ) for a term as the page wrote it.
    fn written_pair(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<Proof>> {
        let said = term.rpn(labels).to_string();
        let apart = take!(self.written_apart(o, term, labels)?);
        let atom = o.atom(&said)?;
        Ok(Built(o.b().ap(
            "jca",
            &binds! {"ph" => &self.under, "ps" => t!(said, "cc", "wcel"), "ch" => t!(said, "cc0", "wne")},
            &[&atom, &apart],
        )))
    }

    /// ( under -> t =/= 0 ), for `written_pair`: a digit says so itself, and
    /// a product is not zero when its factors are not (`mulne0d`). Anything
    /// else is what the page said of it.
    fn written_apart(
        &mut self,
        o: &mut dyn Oracle,
        term: &Term,
        labels: &FloatLabels,
    ) -> Checked<Route<Proof>> {
        let said = term.rpn(labels).to_string();
        if let Some(value) = crate::rules::digit_of(&said) {
            if value != 0 {
                return Ok(Built(self.a1i_label(
                    o,
                    &t!(said, "cc0", "wne"),
                    &Self::apart_label(value as i64),
                )));
            }
        }
        if term.variable().is_none()
            && term.label() == Some("co")
            && term.children().len() == 3
            && &*term.children()[2].rpn(labels) == MUL
        {
            let (a, b) = (&term.children()[0], &term.children()[1]);
            let pa = self.written_apart(o, a, labels)?;
            let pb = self.written_apart(o, b, labels)?;
            let (pa, pb) = (take!(pa), take!(pb));
            let (a_s, b_s) = (a.rpn(labels).to_string(), b.rpn(labels).to_string());
            let aa = o.atom(&a_s)?;
            let ab = o.atom(&b_s)?;
            return Ok(Built(o.b().ap(
                "mulne0d",
                &binds! {"ph" => &self.under, "A" => &a_s, "B" => &b_s},
                &[&aa, &ab, &pa, &pb],
            )));
        }
        self.atom_apart(o, &said)
    }

    /// ( under -> said =/= 0 ) from the oracle, or from the page where the
    /// oracle gives only that, or a decline.
    fn atom_apart(&mut self, o: &mut dyn Oracle, said: &str) -> Checked<Route<Proof>> {
        if self.apart {
            return o.apart(said).map(Built);
        }
        let found = if self.written { o.written(said)? } else { None };
        Ok(match found {
            Some(p) => Built(p),
            None => Route::no(format!("nothing says {said} is not zero")),
        })
    }

    /// ( under -> ( d e. CC /\ d =/= 0 ) ), which every law wants.
    pub fn pair_of(
        &mut self,
        o: &mut dyn Oracle,
        under: &[(Monomial, Q)],
    ) -> Checked<Route<Proof>> {
        let said = Self::spell_run(under);
        let (held, nonzero) = take!(self.denominator(o, under)?);
        Ok(Built(o.b().ap(
            "jca",
            &binds! {"ph" => &self.under, "ps" => t!(said, "cc", "wcel"), "ch" => t!(said, "cc0", "wne")},
            &[&held, &nonzero],
        )))
    }

    /// `a + b`, `a - b` or `a x. b` where one of them divides: `divadddiv`,
    /// `divsubdiv` and `divmuldiv` say what the pair becomes, and the
    /// numerator and denominator they land on are then multiplied out.
    fn quotient_joined(
        &mut self,
        o: &mut dyn Oracle,
        how: &str,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &str,
    ) -> Checked<Route<Quotiented>> {
        let written_op = if how == field::ADD {
            ADD
        } else if how == field::SUB {
            SUB
        } else {
            MUL
        };
        let mut quotients = Vec::new();
        for side in [left, right] {
            let (over, under, proof) = take!(self.normalize_quotient(o, side, labels)?);
            quotients.push(self.as_quotient(
                o,
                over,
                under,
                proof,
                &side.rpn(labels),
            )?);
        }
        let (below, beneath, second) = quotients.pop().unwrap();
        let (over, under, first) = quotients.pop().unwrap();
        let (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
        let (c, d) = (Self::spell_run(&below), Self::spell_run(&beneath));
        let joined = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => &*left.rpn(labels), "B" => op(&a, &b, DIV),
            "C" => &*right.rpn(labels), "D" => op(&c, &d, DIV), "F" => written_op},
            &[&first, &second],
        );
        let (label, top, made, numerator);
        if how == field::SUB {
            // The numerator a difference lands on is two products, the
            // second taken from the first, which `subtracted` does to runs.
            label = "divsubdiv";
            top = op(&op(&a, &d, MUL), &op(&c, &b, MUL), SUB);
            let (first_items, one) = take!(self.multiply(o, &over, &beneath)?);
            let (second_items, two) = take!(self.multiply(o, &below, &under)?);
            let (m, p) = take!(self.subtracted(
                o,
                &op(&a, &d, MUL),
                &op(&c, &b, MUL),
                &first_items,
                one,
                &second_items,
                two,
                &top
            )?);
            made = m;
            numerator = p;
        } else if how == field::ADD {
            // The numerator a sum lands on is two products added, so each is
            // multiplied out and then the two of them joined.
            label = "divadddiv";
            top = op(&op(&a, &d, MUL), &op(&c, &b, MUL), ADD);
            let (first_items, one) = take!(self.multiply(o, &over, &beneath)?);
            let (second_items, two) = take!(self.multiply(o, &below, &under)?);
            let (m, together) = take!(self.add(o, &first_items, &second_items)?);
            let middle = op(
                &Self::spell_run(&first_items),
                &Self::spell_run(&second_items),
                ADD,
            );
            let lifted = o.b().ap(
                "oveq12d",
                &binds! {"ph" => &self.under, "A" => op(&a, &d, MUL),
                "B" => Self::spell_run(&first_items), "C" => op(&c, &b, MUL),
                "D" => Self::spell_run(&second_items), "F" => ADD},
                &[&one, &two],
            );
            numerator =
                self.chain(o, &lifted, &together, &top, &middle, &Self::spell_run(&m));
            made = m;
        } else {
            label = "divmuldiv";
            top = op(&a, &c, MUL);
            let (m, p) = take!(self.multiply(o, &over, &below)?);
            made = m;
            numerator = p;
        }
        let bottom = op(&b, &d, MUL);
        let p1 = self.pair_of(o, &under)?;
        let p2 = self.pair_of(o, &beneath)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let multiplied = take!(self.multiply(o, &under, &beneath)?);
        let rc1 = self.run_cc(o, &over)?;
        let rc2 = self.run_cc(o, &below)?;
        let spread = {
            let bb = o.b();
            let tops = bb.ap(
                "jca",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"), "ch" => t!(c, "cc", "wcel")},
                &[&rc1, &rc2],
            );
            let bottoms = bb.ap(
                "jca",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                "ch" => t!(t!(d, "cc", "wcel"), t!(d, "cc0", "wne"), "wa")},
                &[&p1, &p2],
            );
            let law = bb.ap(
                label,
                &binds! {"A" => &a, "B" => &c, "C" => &b, "D" => &d},
                &[],
            );
            bb.ap(
                "syl2anc",
                &binds! {"ph" => &self.under,
                "ps" => t!(t!(a, "cc", "wcel"), t!(c, "cc", "wcel"), "wa"),
                "ch" => t!(t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                           t!(t!(d, "cc", "wcel"), t!(d, "cc0", "wne"), "wa"), "wa"),
                "th" => t!(op(&op(&a, &b, DIV), &op(&c, &d, DIV), written_op), op(&top, &bottom, DIV), "wceq")},
                &[&tops, &bottoms, &law],
            )
        };
        let (low, denominator) = multiplied;
        self.keep_product(o, &under, &beneath, &low, &denominator)?;
        let first_link = self.chain(
            o,
            &joined,
            &spread,
            said,
            &op(&op(&a, &b, DIV), &op(&c, &d, DIV), written_op),
            &op(&top, &bottom, DIV),
        );
        let second_link = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => &top, "B" => Self::spell_run(&made),
            "C" => &bottom, "D" => Self::spell_run(&low), "F" => DIV},
            &[&numerator, &denominator],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &op(&top, &bottom, DIV),
            &op(&Self::spell_run(&made), &Self::spell_run(&low), DIV),
        );
        Ok(Built((made, Some(low), p)))
    }

    /// `( a / b ) ^ k`, which `expdiv` takes apart.
    fn quotient_raised(
        &mut self,
        o: &mut dyn Oracle,
        left: &Term,
        right: &Term,
        labels: &FloatLabels,
        said: &str,
    ) -> Checked<Route<Quotiented>> {
        let times = match field::whole_number(right) {
            Some(t) if (0..=9).contains(&t) => t as u32,
            _ => return Ok(Route::no(format!("{said} has no numeral exponent"))),
        };
        let (o1, u1, p1) = take!(self.normalize_quotient(o, left, labels)?);
        let (over, under, first) =
            self.as_quotient(o, o1, u1, p1, &left.rpn(labels))?;
        let (a, b) = (Self::spell_run(&over), Self::spell_run(&under));
        let pair = take!(self.pair_of(o, &under)?);
        let joined = o.b().ap(
            "oveq1d",
            &binds! {"ph" => &self.under, "A" => &*left.rpn(labels), "B" => op(&a, &b, DIV),
            "C" => n(times), "F" => EXP},
            &[&first],
        );
        let rc = self.run_cc(o, &over)?;
        let ix = self.index(o, times as i64);
        let split = op(&op(&a, n(times), EXP), &op(&b, n(times), EXP), DIV);
        let spread = {
            let bb = o.b();
            let law = bb.ap(
                "expdiv",
                &binds! {"A" => &a, "B" => &b, "N" => n(times)},
                &[],
            );
            bb.ap(
                "syl3anc",
                &binds! {"ph" => &self.under, "ps" => t!(a, "cc", "wcel"),
                "ch" => t!(t!(b, "cc", "wcel"), t!(b, "cc0", "wne"), "wa"),
                "th" => t!(n(times), "cn0", "wcel"),
                "ta" => t!(op(&op(&a, &b, DIV), n(times), EXP), split, "wceq")},
                &[&rc, &pair, &ix, &law],
            )
        };
        let (made, numerator) = take!(self.power(o, &over, times)?);
        let (low, denominator) = take!(self.power(o, &under, times)?);
        let first_link = self.chain(
            o,
            &joined,
            &spread,
            said,
            &op(&op(&a, &b, DIV), n(times), EXP),
            &split,
        );
        let second_link = o.b().ap(
            "oveq12d",
            &binds! {"ph" => &self.under, "A" => op(&a, n(times), EXP), "B" => Self::spell_run(&made),
            "C" => op(&b, n(times), EXP), "D" => Self::spell_run(&low), "F" => DIV},
            &[&numerator, &denominator],
        );
        let p = self.chain(
            o,
            &first_link,
            &second_link,
            said,
            &split,
            &op(&Self::spell_run(&made), &Self::spell_run(&low), DIV),
        );
        Ok(Built((made, Some(low), p)))
    }
}

/// A rational as Python writes a `Fraction`: `3`, or `-1/2`.
pub fn show(value: &Q) -> String {
    if value.is_integer() {
        value.to_integer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

/// Whether a division appears in this term outside its atoms.
///
/// Only the arithmetic the normaliser reads is looked through. A sum whose
/// summand divides, Σ(k = 1 to n) 1/T(k), is an atom, and what is inside it
/// is not a denominator of the term it stands in.
pub fn divides(term: &Term, labels: &FloatLabels) -> bool {
    if term.variable().is_some() {
        return false;
    }
    if term.label() == Some("cneg") {
        return term.children().iter().any(|one| divides(one, labels));
    }
    if term.label() != Some("co") || term.children().len() != 3 {
        return false;
    }
    let how = term.children()[2].rpn(labels);
    if &*how == field::DIV {
        return true;
    }
    if ![field::ADD, field::SUB, field::MUL, field::EXP].contains(&&*how) {
        return false;
    }
    term.children()[..2].iter().any(|one| divides(one, labels))
}

/// One factor of a monomial, always `( x ^ k )`.
fn spell_factor(factor: &(Rc<str>, u32)) -> String {
    op(&factor.0, n(factor.1), EXP)
}

/// A polynomial as its terms in canonical order.
pub fn terms_of(poly: &field::Poly) -> Run {
    let mut monomials: Vec<&Monomial> = poly.terms.keys().collect();
    monomials.sort_by_key(|m| order(m));
    monomials
        .into_iter()
        .map(|m| (m.clone(), poly.terms[m].clone()))
        .collect()
}
