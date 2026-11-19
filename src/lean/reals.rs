//! `real arithmetic` in Lean, as the Metamath elaborator proves it
//! (`elab::real`): each special value the claim holds is put as its value,
//! which the checker's own decider works out (`methods::reals`,
//! `methods::surds`), each by the law that gives it, and the two sides are
//! then compared.
//!
//! The values are polynomials in four kinds of atom: √p and ln p for a
//! prime p, π, and e. A piece that is not an atom has a `have` stating its
//! value, proved by its law:
//! - a root of a rational, c·√(p₁·…·pₖ) for its square part c: the
//!   radicand is c²·p₁·…·pₖ, the root of c² is c (`Real.sqrt_sq`), and the
//!   root of a product the product of the roots (`Real.sqrt_mul`);
//! - a quotient by a value holding a root, v where v times the divisor is
//!   what is divided (`div_eq_iff`), the divisor shown not 0 by its
//!   cofactor, which makes it a rational not 0 (`surds::cofactor`);
//! - a logarithm of q·eᵏ, the sum of its primes' logarithms, each times
//!   its exponent (`Real.log_div`, `Real.log_mul`, `Real.log_pow`), and k;
//! - an exponential of k + Σ nₚ·ln p, eᵏ·Π pⁿᵖ (`Real.exp_add`,
//!   `Real.exp_nat_mul`, `Real.exp_log`);
//! - a sine or cosine of q·π, its angle less its whole turns
//!   (`Real.sin_add_int_mul_two_pi`), then less π and π/2 where it reaches
//!   them, and then the value Mathlib names at 0, π/6, π/4 or π/3.
//!
//! The two sides then differ by the pieces less their values, each times
//! what it is multiplied by, and by multiples of (√p)² − p, which
//! `linear_combination` is given (`Real.sq_sqrt`), as `elab::real`'s
//! `identity` finds them.

use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::algebra::coefficient_term;
use super::doc::forms::casts_dropped;
use super::doc::{LeanType, Op, Proof, Source, Tactic, TermKind};
use super::expr::{Printed, Writer};
use super::tactics as t;
use super::templates::Num;
use crate::formula::Node;
use crate::methods::field::{self, Monomial, Poly, Quotient, Q};
use crate::methods::numerals;
use crate::methods::reals::{self, Atom, Real, Trig};
use crate::methods::surds;
use crate::methods::terms::{term_of_node_reading, Targets};
use crate::mm::kernel::{FloatLabels, Term};
use crate::mm::Rpn;
use crate::outcome::Route;

/// The proof of a `real arithmetic` claim of closed terms built from
/// numerals, roots, π, e, logarithms, exponentials, sines and cosines: an
/// equation, a disequality, an order or its denial, a membership of ℕ, ℕ₀
/// or ℤ or its denial, or several of these joined by "and". Any other
/// declines.
pub fn real_arithmetic(
    writer: &Writer,
    targets: &Targets,
    claim: &Node,
) -> Route<Proof> {
    match proved(writer, targets, claim) {
        Route::Built(lines) => Route::Built(Proof::Block(lines)),
        Route::Declined(d) => Route::Declined(d),
    }
}

/// The proof of a calculation link real arithmetic works out, `left =
/// right`, where only closed pieces change, as the checker reads one
/// (`checker::formulas::real_pieces`): what holds a letter, cos(x) in
/// cos(x)·sin(π), is an atom that the two sides share. A link of a
/// calculation worked in a wider type than ℝ, `chain`, is shown in ℝ and
/// taken up by its casts (`exact_mod_cast`).
pub fn real_link(
    writer: &Writer,
    targets: &Targets,
    left: &Node,
    right: &Node,
    chain: Num,
) -> Route<Proof> {
    let mut w = Work::new(writer, targets);
    for side in [left, right] {
        if let Route::Declined(d) = w.pieces_of(side) {
            return Route::Declined(d);
        }
    }
    let (l, r) = match (w.read_node(left), w.read_node(right)) {
        (Route::Built(l), Route::Built(r)) => (l, r),
        (Route::Declined(d), _) | (_, Route::Declined(d)) => return Route::Declined(d),
    };
    let close = match w.compared(l, r) {
        Route::Built(c) => c,
        Route::Declined(d) => return Route::Declined(d),
    };
    if chain <= Num::Real {
        w.lines.push(close);
        return Route::Built(Proof::Block(w.lines));
    }
    let (ls, rs) = match (w.number(left), w.number(right)) {
        (Route::Built(l), Route::Built(r)) => (l, r),
        (Route::Declined(d), _) | (_, Route::Declined(d)) => return Route::Declined(d),
    };
    let hl = w.fact(eq(ls, rs), Proof::By(close));
    w.lines.push(t::exact_mod_cast(t::hyp(&hl)));
    Route::Built(Proof::Block(w.lines))
}

/// The proof that an equation or an order real arithmetic shows false is
/// false: an equation as a disequality of its sides is shown
/// (`apart_proof`), an order as the opposite order (`order_refuted`). Any
/// other claim declines.
pub fn real_refuted(writer: &Writer, targets: &Targets, claim: &Node) -> Route<Proof> {
    let mut w = Work::new(writer, targets);
    let term = w.term(claim);
    if let (Some("wbr"), [a, _, rel]) = (term.label(), term.children()) {
        if let Route::Declined(d) = w.pieces_of(claim) {
            return Route::Declined(d);
        }
        return match w.order_refuted(claim, a, rel) {
            Route::Built(t) => {
                w.lines.push(t);
                Route::Built(Proof::Block(w.lines))
            }
            Route::Declined(d) => Route::Declined(d),
        };
    }
    if term.label() != Some("wceq") {
        return Route::no(
            "a line real arithmetic shows false that is neither equation nor order",
        );
    }
    let [a, b] = claim.children.as_slice() else {
        return Route::no("an equation without two sides");
    };
    if let Route::Declined(d) = w.pieces_of(claim) {
        return Route::Declined(d);
    }
    match w.apart_proof(a, b) {
        Route::Built(lines) => {
            w.lines.extend(lines);
            Route::Built(Proof::Block(w.lines))
        }
        Route::Declined(d) => Route::Declined(d),
    }
}

/// The lines proving one claim: a joined claim part by part, each part
/// its own `have`.
fn proved(writer: &Writer, targets: &Targets, claim: &Node) -> Route<Vec<Tactic>> {
    let mut w = Work::new(writer, targets);
    let term = w.term(claim);
    if term.label() == Some("wa") {
        let [a, b] = claim.children.as_slice() else {
            return Route::no("a joined claim without two parts");
        };
        let mut lines = Vec::new();
        let mut names = Vec::new();
        for (k, part) in [a, b].into_iter().enumerate() {
            let says = match writer.formula(part) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            let proof = match proved(writer, targets, part) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("hc{}", k + 1);
            lines.push(Tactic::Have {
                name: name.clone(),
                says,
                proof: Box::new(Proof::Block(proof)),
            });
            names.push(t::hyp(&name));
        }
        lines.push(Tactic::Exact(Printed {
            kind: TermKind::Listed {
                brackets: super::doc::Brackets::Angle,
                items: names,
            },
            ty: None,
        }));
        return Route::Built(lines);
    }
    if let Route::Declined(d) = w.pieces_of(claim) {
        return Route::Declined(d);
    }
    let close = match w.closed(claim, &term) {
        Route::Built(c) => c,
        Route::Declined(d) => return Route::Declined(d),
    };
    w.lines.extend(close);
    Route::Built(w.lines)
}

/// `linarith only [facts]`.
fn linarith_only(facts: Vec<Printed>) -> Tactic {
    t::call(
        "linarith",
        vec![super::doc::TacticArg::Only, t::rules(facts)],
    )
}

/// `a < b`.
fn less(a: Printed, b: Printed) -> Printed {
    Printed::infix(Op::of("<").expect("< is an operator"), a, b, LeanType::Prop)
}

/// `(iff).mpr arg`.
fn mpr(iff: Printed, arg: Printed) -> Printed {
    Printed::of(
        TermKind::App {
            head: Box::new(Printed {
                kind: TermKind::Field {
                    inner: Box::new(t::bracket(iff)),
                    field: "mpr".into(),
                },
                ty: None,
            }),
            args: vec![super::doc::Arg::Explicit(arg)],
            explicit: false,
        },
        LeanType::Prop,
    )
}

/// `a / b` of a positive rational, its numerator over its denominator.
fn fraction(q: &Q) -> Printed {
    let n = |x: &BigInt| Printed::numeral(x.to_string(), real());
    Printed::cast(
        Printed::infix(Op::DIVIDE, n(q.numer()), n(q.denom()), real()),
        real(),
    )
}

/// `show says by norm_num`.
fn show_by_norm_num(says: Printed) -> Printed {
    show(says, t::call("norm_num", vec![]))
}

/// `Real.log (r : ℝ)`.
fn log_of_rational(r: &Q) -> Printed {
    Printed::applied(
        "Real.log",
        Source::Mathlib,
        vec![typed(rational(r))],
        real(),
    )
}

/// `linear_combination` of the terms, or `ring1` where there are none.
fn closing(terms: Vec<Printed>) -> Tactic {
    match sum_of(terms) {
        Some(e) => t::linear_combination(e),
        None => t::call("ring1", vec![]),
    }
}

/// The terms added.
fn sum_of(terms: Vec<Printed>) -> Option<Printed> {
    terms
        .into_iter()
        .reduce(|s, part| Printed::infix(Op::PLUS, s, part, real()))
}

/// A piece of the claim put as its value by a `have`.
struct Piece {
    said: Printed,
    /// The piece as the decider reads it, an atom of the sides until it is
    /// put as its value.
    atom: Rpn,
    value: Real,
    /// The `have` stating `said = ` the value as its law leaves it.
    name: String,
}

/// An atom of the values: √p or ln p for a prime p, π or e.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Base {
    Root(u64),
    Log(u64),
    Pi,
    E,
}

/// What a proof has stated so far, and the lines stating it.
struct Work<'a> {
    writer: &'a Writer<'a>,
    targets: &'a Targets,
    labels: FloatLabels,
    lines: Vec<Tactic>,
    pieces: Vec<Piece>,
    /// Each atom of the values, as the decider reads it.
    atoms: IndexMap<Rpn, Base>,
    /// The primes whose `(√p)² = p` is stated.
    squares: BTreeSet<u64>,
    /// How many divisors are stated not 0.
    apart: usize,
    /// How many other facts are stated.
    facts: usize,
    /// Each part holding a letter of the proof's, as the decider reads it,
    /// and as Lean writes it: an atom the sides of a link share.
    opaque: IndexMap<Rpn, Printed>,
}

/// A term between two bounds, with the facts stating each.
#[derive(Clone)]
struct Bounded {
    said: Printed,
    below: Printed,
    above: Printed,
    below_fact: String,
    above_fact: String,
}

/// What a closed term holds that a law puts as its value.
enum Kind {
    Root,
    Quotient,
    Log,
    Exp,
    Trig(Trig),
    /// A power to a whole number below 0.
    Power,
}

impl<'a> Work<'a> {
    fn new(writer: &'a Writer<'a>, targets: &'a Targets) -> Work<'a> {
        Work {
            writer,
            targets,
            labels: FloatLabels::new(IndexMap::new()),
            lines: Vec::new(),
            pieces: Vec::new(),
            atoms: IndexMap::new(),
            squares: BTreeSet::new(),
            apart: 0,
            facts: 0,
            opaque: IndexMap::new(),
        }
    }

    /// Whether a node holds a letter of the proof's.
    fn lettered(&self, node: &Node) -> bool {
        node.names()
            .iter()
            .any(|n| self.writer.letters.contains_key(n.as_str()))
    }

    /// The pieces of a node stated, inner ones first so that each is
    /// stated after those inside it; and each part holding a letter that
    /// is no sum, difference, product, quotient, power or negation noted
    /// as an atom.
    fn pieces_of(&mut self, node: &Node) -> Route<()> {
        let mut nodes = Vec::new();
        self.walk_to_opaque(node, &mut nodes);
        nodes.reverse();
        for n in &nodes {
            if self.lettered(n) {
                let term = self.term(n);
                if self.opaque_at(n) {
                    let said = match self.number(n) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.opaque.insert(term.rpn(&self.labels), said);
                }
                continue;
            }
            if let Route::Declined(d) = self.piece(n) {
                return Route::Declined(d);
            }
        }
        Route::Built(())
    }

    /// Whether the node is a term the arithmetic takes as one piece: one
    /// with a letter in it that is no sum, product or negation, |CA| or
    /// x³.
    fn opaque_at(&self, node: &Node) -> bool {
        let term = self.term(node);
        self.lettered(node)
            && !(matches!(term.label(), Some("co" | field::NEG))
                && !term.children().is_empty())
    }

    /// The node and what stands in it, before what stands in each, as
    /// `Node::walk` gives them, but nothing inside an opaque term
    /// (`opaque_at`): the points A and C of |CA| are no numbers of the
    /// arithmetic's.
    fn walk_to_opaque(&self, node: &Node, out: &mut Vec<Node>) {
        out.push(node.clone());
        if self.opaque_at(node) {
            return;
        }
        for c in &node.children {
            self.walk_to_opaque(c, out);
        }
    }

    fn number(&self, node: &Node) -> Route<Printed> {
        self.writer.number(node, Num::Real)
    }

    /// The node as the decider reads it, as the checker does
    /// (`checker::formulas::real_term`): a name that is no letter of the
    /// proof's is the library's function, ln in ln(8).
    fn term(&self, node: &Node) -> Term {
        let letters = &self.writer.letters;
        let library = |name: &str| !letters.contains_key(name);
        term_of_node_reading(node, self.targets, &library)
    }

    /// The node put as its value, where a law puts it: its `have`, with
    /// what its law needs stated first. One that is an atom as it stands,
    /// √2 or ln 2, has none.
    fn piece(&mut self, node: &Node) -> Route<()> {
        let term = self.term(node);
        let Some(kind) = kind_of(&term) else {
            return Route::Built(());
        };
        let atom = term.rpn(&self.labels);
        if self.pieces.iter().any(|p| p.atom == atom) {
            return Route::Built(());
        }
        let Route::Built(reals::Value::Exact(value)) = reals::closed_value(&term)
        else {
            return Route::no("a piece real arithmetic gives no value");
        };
        let said = match self.number(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        if said == self.real_term(&value) {
            return Route::Built(());
        }
        let law = match kind {
            Kind::Root => self.root_law(node),
            Kind::Quotient => self.quotient_law(node, &value),
            Kind::Log => self.log_law(node),
            Kind::Exp => self.exp_law(node),
            Kind::Trig(f) => self.trig_law(node, f),
            Kind::Power => self.power_law(node, &value),
        };
        let Law { tactics, leaves } = match law {
            Route::Built(l) => l,
            Route::Declined(d) => return Route::Declined(d),
        };
        let name = format!("hv{}", self.pieces.len() + 1);
        self.lines.push(Tactic::Have {
            name: name.clone(),
            says: Printed::infix(Op::EQUALS, said.clone(), leaves, LeanType::Prop),
            proof: Box::new(Proof::By(Tactic::Seq(tactics))),
        });
        self.pieces.push(Piece {
            said,
            atom,
            value,
            name,
        });
        Route::Built(())
    }

    /// The node read, as `read`.
    fn read_node(&mut self, node: &Node) -> Route<Quotient> {
        let term = self.term(node);
        match self.read(&term) {
            Some(q) => Route::Built(q),
            None => Route::no("a side holding a part real arithmetic does not read"),
        }
    }

    /// The node's value, as the decider works it out.
    fn value_of(&self, node: &Node) -> Route<Real> {
        match reals::closed_value(&self.term(node)) {
            Route::Built(reals::Value::Exact(v)) => Route::Built(v),
            _ => Route::no("a side real arithmetic gives no value"),
        }
    }

    /// The tactics closing a claim whose pieces are stated, by what it
    /// is, read as the decider reads it (`term`).
    fn closed(&mut self, claim: &Node, term: &Term) -> Route<Vec<Tactic>> {
        let kids = term.children();
        let order = |rel: &Term| match rel.label() {
            Some("clt") => Some(true),
            Some("cle") => Some(false),
            _ => None,
        };
        match (term.label(), kids) {
            (Some("wceq"), [_, _]) => {
                let [l, r] = claim.children.as_slice() else {
                    return Route::no("an equation without two sides");
                };
                let (l, r) = match (self.read_node(l), self.read_node(r)) {
                    (Route::Built(l), Route::Built(r)) => (l, r),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        return Route::Declined(d)
                    }
                };
                self.compared(l, r).map(|t| vec![t])
            }
            (Some("wne"), [_, _]) => {
                let [l, r] = claim.children.as_slice() else {
                    return Route::no("a disequality without two sides");
                };
                self.apart_proof(l, r)
            }
            (Some("wbr"), [a, _, rel]) => {
                let Some(strict) = order(rel) else {
                    return Route::no("a relation real arithmetic does not decide");
                };
                let Some((low, high)) = self.ordered_sides(claim, a) else {
                    return Route::no("an order whose sides are not the claim's");
                };
                match self.order_facts(low, high, strict) {
                    Route::Built(facts) => Route::Built(vec![linarith_only(facts)]),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            (Some("wcel"), [_, system]) => {
                match self.membership(claim, system, false) {
                    Route::Built(t) => Route::Built(t),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            (Some("wn"), [inner]) => {
                let [inner_node] = claim.children.as_slice() else {
                    return Route::no("a denial without one claim");
                };
                match (inner.label(), inner.children()) {
                    (Some("wceq"), [_, _]) => {
                        let [l, r] = inner_node.children.as_slice() else {
                            return Route::no("an equation without two sides");
                        };
                        self.apart_proof(l, r)
                    }
                    (Some("wbr"), [a, _, rel]) => {
                        self.order_refuted(inner_node, a, rel).map(|t| vec![t])
                    }
                    (Some("wcel"), [_, system]) => {
                        self.membership(inner_node, system, true)
                    }
                    _ => Route::no("a denial real arithmetic does not decide"),
                }
            }
            _ => Route::no("a claim real arithmetic does not decide"),
        }
    }

    /// The proof that the order `claim` is false, `rel` its relation and
    /// `lesser` the side the decider reads as the lesser: not x < y is
    /// y ≤ x, and not x ≤ y is y < x, which `linarith` shows from the
    /// facts the decider gives (`order_facts`).
    fn order_refuted(
        &mut self,
        claim: &Node,
        lesser: &Term,
        rel: &Term,
    ) -> Route<Tactic> {
        let strict = match rel.label() {
            Some("clt") => true,
            Some("cle") => false,
            _ => return Route::no("a relation real arithmetic does not decide"),
        };
        let Some((low, high)) = self.ordered_sides(claim, lesser) else {
            return Route::no("an order whose sides are not the claim's");
        };
        let facts = match self.order_facts(high, low, !strict) {
            Route::Built(f) => f,
            Route::Declined(d) => return Route::Declined(d),
        };
        let turn = match strict {
            true => "not_lt.mpr",
            false => "not_le.mpr",
        };
        let inside = t::bracket(t::by_term(Proof::By(linarith_only(facts))));
        Route::Built(Tactic::Exact(lemma(turn, vec![inside])))
    }

    /// The sides of an order, the lesser first: `lesser` is the side the
    /// decider reads as the lesser, which `>` and `≥` write on the right.
    fn ordered_sides<'n>(
        &self,
        order: &'n Node,
        lesser: &Term,
    ) -> Option<(&'n Node, &'n Node)> {
        let [a, b] = order.children.as_slice() else {
            return None;
        };
        let at = |n: &Node| self.term(n).rpn(&self.labels);
        let want = lesser.rpn(&self.labels);
        match (at(a) == want, at(b) == want) {
            (true, _) => Some((a, b)),
            (_, true) => Some((b, a)),
            _ => None,
        }
    }

    /// The facts `linarith` shows `low < high` (or `≤`) from, as the
    /// decider shows the sign of high − low (`reals::sign_of`): the
    /// difference stated as its value, and then that value's sign by the
    /// way the decider found it. A rational needs nothing more; rational
    /// multiples of logarithms of primes are ln r over n, r compared with
    /// 1 (`Real.log_pos`); anything else is bracketed from its factors'
    /// bounds.
    fn order_facts(
        &mut self,
        low: &Node,
        high: &Node,
        strict: bool,
    ) -> Route<Vec<Printed>> {
        let (vl, vh) = match (self.value_of(low), self.value_of(high)) {
            (Route::Built(l), Route::Built(h)) => (l, h),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let gap = vh.minus(&vl);
        let (rl, rh) = match (self.read_node(low), self.read_node(high)) {
            (Route::Built(l), Route::Built(h)) => (l, h),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let (sl, sh) = match (self.number(low), self.number(high)) {
            (Route::Built(l), Route::Built(h)) => (l, h),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let gap_poly = self.real_poly(&gap);
        let terms = match self.combination(rh.minus(&rl), Quotient::whole(gap_poly)) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The difference stated as its value where a piece or a root's
        // square makes it so; where arithmetic alone does, `linarith` sees
        // it.
        let mut facts = Vec::new();
        if !terms.is_empty() {
            let difference = Printed::infix(Op::MINUS, sh, at_least(sl, 66), real());
            let said = self.real_term(&gap);
            let hg = self.fact(eq(difference, said), Proof::By(closing(terms)));
            facts.push(t::hyp(&hg));
        }
        if gap.is_zero() {
            return match strict {
                true => Route::no("a strict order of equal sides"),
                false => Route::Built(facts),
            };
        }
        match reals::sign_of(&gap) {
            reals::Sign::Shown {
                positive: true,
                how,
            } => match how {
                reals::Shown::Rational => {}
                reals::Shown::Logarithms => {
                    let Some(read) = gap.logarithmic() else {
                        return Route::no("logarithms that do not read");
                    };
                    let Ok(r) = reals::logarithm_ratio(&read.logs) else {
                        return Route::no("a ratio of logarithms too large");
                    };
                    let hl = match self.log_fact(&r.ratio) {
                        Route::Built(h) => h,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let one = Printed::cast(whole(1, Num::Real), real());
                    let above = show(
                        less(one, rational(&r.ratio)),
                        t::call("norm_num", vec![]),
                    );
                    let log_r = log_of_rational(&r.ratio);
                    let zero = Printed::cast(whole(0, Num::Real), real());
                    let hp = self.fact(
                        less(zero, log_r),
                        Proof::Term(lemma("Real.log_pos", vec![above])),
                    );
                    facts.extend([t::hyp(&hl), t::hyp(&hp)]);
                }
                reals::Shown::Bracketed { precision } => {
                    match self.bracket_facts(&gap, precision) {
                        Route::Built(f) => facts.extend(f),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
            },
            _ => return Route::no("an order the decider does not show"),
        }
        Route::Built(facts)
    }

    /// `have hfK : says := proof`, its name.
    fn fact(&mut self, says: Printed, proof: Proof) -> String {
        self.facts += 1;
        let name = format!("hf{}", self.facts);
        self.lines.push(Tactic::Have {
            name: name.clone(),
            says,
            proof: Box::new(proof),
        });
        name
    }

    /// `ln r = Σ nₚ·ln p`, r a positive rational, by its law
    /// (`log_of`), the sum as the values write it.
    fn log_fact(&mut self, ratio: &Q) -> Route<String> {
        let law = match self.log_of(
            typed(rational(ratio)),
            Quotient::whole(field::constant(ratio.clone())),
            ratio,
            0,
        ) {
            Route::Built(l) => l,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Ok(primes) = reals::factored(ratio) else {
            return Route::no("a ratio too large to factor");
        };
        let mut value = Real::default();
        for (p, n) in primes {
            value = value.plus(
                &Real::atom(Atom::Ln(p))
                    .times(&Real::rational(Q::from_integer(BigInt::from(n)))),
            );
        }
        let said = self.real_term(&value);
        let mut tactics = law.tactics;
        if law.leaves != said {
            tactics.push(t::call("ring1", vec![]));
        }
        Route::Built(self.fact(
            eq(log_of_rational(ratio), said),
            Proof::By(Tactic::Seq(tactics)),
        ))
    }

    /// The bounds of each part of a value, from its factors' at
    /// `precision` (`reals::factor_bracket`): √p's by its square
    /// (`Real.lt_sqrt`, `Real.sqrt_lt'`), π's and e's as Mathlib states
    /// them, and ln p's by e's (`Logarithms.log_above`, `log_below`); a
    /// product's and a power's from its factors' (`mul_lt_mul''`,
    /// `pow_lt_pow_left₀`).
    fn bracket_facts(&mut self, value: &Real, precision: u32) -> Route<Vec<Printed>> {
        let mut out = Vec::new();
        let mut held: Vec<(Rpn, Bounded)> = Vec::new();
        let p = self.real_poly(value);
        for monomial in p.terms.keys() {
            let mut acc: Option<Bounded> = None;
            for (atom, power) in monomial {
                let base = match self.atoms.get(atom) {
                    Some(b) => *b,
                    None => return Route::no("a part with no bound"),
                };
                let one = match held.iter().find(|(a, _)| a == atom) {
                    Some((_, b)) => b.clone(),
                    None => {
                        let b = match self.factor_bounds(base, precision) {
                            Route::Built(b) => b,
                            Route::Declined(d) => return Route::Declined(d),
                        };
                        held.push((atom.clone(), b.clone()));
                        b
                    }
                };
                let powered = match power {
                    1 => one,
                    k => self.power_bounds(&one, *k),
                };
                acc = Some(match acc {
                    None => powered,
                    Some(a) => self.product_bounds(&a, &powered),
                });
            }
            if let Some(b) = acc {
                out.extend([t::hyp(&b.below_fact), t::hyp(&b.above_fact)]);
            }
        }
        out.dedup();
        Route::Built(out)
    }

    /// An atom's bounds as facts.
    fn factor_bounds(&mut self, base: Base, precision: u32) -> Route<Bounded> {
        let factor = match base {
            Base::Root(p) => reals::Factor::Root(p),
            Base::Log(p) => reals::Factor::Atom(Atom::Ln(p)),
            Base::Pi => reals::Factor::Atom(Atom::Pi),
            Base::E => reals::Factor::Atom(Atom::E),
        };
        let b = reals::factor_bracket(factor, precision);
        let said = base_term(base);
        // A logarithm's bounds as `Logarithms.log_above` and `log_below`
        // state them, a / b, which their casts come down to.
        let (lo, hi) = match base {
            Base::Log(_) => (fraction(&b.below), fraction(&b.above)),
            _ => (rational(&b.below), rational(&b.above)),
        };
        let zero_at_most = |x: Printed| at_least_zero(x);
        let (below, above) = match base {
            Base::Root(p) => (
                Proof::Term(mpr(
                    lemma("Real.lt_sqrt", vec![zero_at_most(lo.clone())]),
                    show_by_norm_num(less(
                        Printed::infix(
                            Op::POWER,
                            at_least(lo.clone(), 76),
                            whole(2, Num::Nat),
                            real(),
                        ),
                        whole(p, Num::Real),
                    )),
                )),
                Proof::Term(mpr(
                    lemma(
                        "Real.sqrt_lt'",
                        vec![show_by_norm_num(less(
                            Printed::cast(whole(0, Num::Real), real()),
                            hi.clone(),
                        ))],
                    ),
                    show_by_norm_num(less(
                        whole(p, Num::Real),
                        Printed::infix(
                            Op::POWER,
                            at_least(hi.clone(), 76),
                            whole(2, Num::Nat),
                            real(),
                        ),
                    )),
                )),
            ),
            Base::Pi => (
                Proof::Term(t::lemma("Real.pi_gt_three")),
                Proof::Term(t::lemma("Real.pi_lt_four")),
            ),
            Base::E => (
                Proof::Term(t::lemma("Real.exp_one_gt_two")),
                Proof::Term(t::lemma("Real.exp_one_lt_three")),
            ),
            Base::Log(p) => {
                let nat = |q: &BigInt| {
                    Printed::numeral(q.to_string(), LeanType::Num(Num::Nat))
                };
                let by_norm_num =
                    || t::bracket(t::by_term(Proof::By(t::call("norm_num", vec![]))));
                let named = |name: &str, args: Vec<(&str, Printed)>, hyps: usize| {
                    let mut out: Vec<super::doc::Arg> = args
                        .into_iter()
                        .map(|(n, v)| super::doc::Arg::Named {
                            name: n.to_string(),
                            value: v,
                        })
                        .collect();
                    for _ in 0..hyps {
                        out.push(super::doc::Arg::Explicit(by_norm_num()));
                    }
                    Printed::of(
                        TermKind::App {
                            head: Box::new(t::bridge_lemma(
                                name,
                                super::doc::bridges::BridgeModule::Logarithms,
                            )),
                            args: out,
                            explicit: false,
                        },
                        LeanType::Prop,
                    )
                };
                let above_lemma = named(
                    "LeanBridges.Logarithms.log_above",
                    vec![
                        ("p", whole(p, Num::Nat)),
                        ("a", nat(b.below.numer())),
                        ("b", nat(b.below.denom())),
                    ],
                    3,
                );
                let below_lemma = named(
                    "LeanBridges.Logarithms.log_below",
                    vec![
                        ("p", whole(p, Num::Nat)),
                        ("a", nat(b.above.numer())),
                        ("b", nat(b.above.denom())),
                    ],
                    4,
                );
                (
                    Proof::By(t::exact_mod_cast(above_lemma)),
                    Proof::By(t::exact_mod_cast(below_lemma)),
                )
            }
        };
        let below_fact = self.fact(less(lo.clone(), said.clone()), below);
        let above_fact = self.fact(less(said.clone(), hi.clone()), above);
        Route::Built(Bounded {
            said,
            below: lo,
            above: hi,
            below_fact,
            above_fact,
        })
    }

    /// The bounds of xᵏ from x's, x's lower bound at least 0.
    fn power_bounds(&mut self, x: &Bounded, k: u32) -> Bounded {
        let k_said = whole(u64::from(k), Num::Nat);
        let pow = |b: &Printed| {
            Printed::infix(Op::POWER, at_least(b.clone(), 76), k_said.clone(), real())
        };
        let nonzero = show_by_norm_num(unequal(k_said.clone(), whole(0, Num::Nat)));
        let below_fact = self.fact(
            less(pow(&x.below), pow(&x.said)),
            Proof::Term(lemma(
                "pow_lt_pow_left₀",
                vec![
                    t::hyp(&x.below_fact),
                    at_least_zero(x.below.clone()),
                    nonzero.clone(),
                ],
            )),
        );
        let above_fact = self.fact(
            less(pow(&x.said), pow(&x.above)),
            Proof::Term(lemma(
                "pow_lt_pow_left₀",
                vec![t::hyp(&x.above_fact), self.nonnegative(x), nonzero],
            )),
        );
        Bounded {
            said: pow(&x.said),
            below: pow(&x.below),
            above: pow(&x.above),
            below_fact,
            above_fact,
        }
    }

    /// The bounds of x·y from x's and y's, both lower bounds at least 0.
    fn product_bounds(&mut self, x: &Bounded, y: &Bounded) -> Bounded {
        let times = |a: &Printed, b: &Printed| {
            Printed::infix(Op::TIMES, a.clone(), at_least(b.clone(), 71), real())
        };
        let below_fact = self.fact(
            less(times(&x.below, &y.below), times(&x.said, &y.said)),
            Proof::Term(lemma(
                "mul_lt_mul''",
                vec![
                    t::hyp(&x.below_fact),
                    t::hyp(&y.below_fact),
                    at_least_zero(x.below.clone()),
                    at_least_zero(y.below.clone()),
                ],
            )),
        );
        let above_fact = self.fact(
            less(times(&x.said, &y.said), times(&x.above, &y.above)),
            Proof::Term(lemma(
                "mul_lt_mul''",
                vec![
                    t::hyp(&x.above_fact),
                    t::hyp(&y.above_fact),
                    self.nonnegative(x),
                    self.nonnegative(y),
                ],
            )),
        );
        Bounded {
            said: times(&x.said, &y.said),
            below: times(&x.below, &y.below),
            above: times(&x.above, &y.above),
            below_fact,
            above_fact,
        }
    }

    /// 0 ≤ x, from x's lower bound at least 0.
    fn nonnegative(&self, x: &Bounded) -> Printed {
        lemma(
            "le_of_lt",
            vec![t::bracket(lemma(
                "lt_of_le_of_lt",
                vec![at_least_zero(x.below.clone()), t::hyp(&x.below_fact)],
            ))],
        )
    }

    /// The proof of `x ≠ y`, as `elab::real`'s `real_apart` shows it: the
    /// difference times its cofactor is a rational not 0
    /// (`surds::cofactor`), or, for rational multiples of logarithms of
    /// primes, n times the difference is ln r for r not 1
    /// (`Real.log_ne_zero_of_pos_of_ne_one`).
    fn apart_proof(&mut self, x: &Node, y: &Node) -> Route<Vec<Tactic>> {
        let (vx, vy) = match (self.value_of(x), self.value_of(y)) {
            (Route::Built(a), Route::Built(b)) => (a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let gap = vx.minus(&vy);
        let (rx, ry) = match (self.read_node(x), self.read_node(y)) {
            (Route::Built(a), Route::Built(b)) => (a, b),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let difference = rx.minus(&ry);
        if let Some(s) = gap.as_surd() {
            if s.is_zero() {
                return Route::no("a disequality of equal sides");
            }
            let surds::Cofactor { times, norm } = surds::cofactor(&s);
            let c = Real::surd(times);
            let c_poly = self.real_poly(&c);
            let c_said = self.real_term(&c);
            let mut terms = vec![Printed::infix(
                Op::TIMES,
                t::bracket(c_said),
                t::hyp("h"),
                real(),
            )];
            match self.combination(
                Quotient::whole(field::constant(norm.clone())),
                Quotient::whole(c_poly).times(&difference),
            ) {
                Route::Built(more) => terms.extend(more),
                Route::Declined(d) => return Route::Declined(d),
            }
            let zero = eq(typed(rational(&norm)), whole(0, Num::Real));
            let reached = show(zero, closing(terms));
            return Route::Built(vec![
                Tactic::Intro(vec!["h".to_string()]),
                Tactic::Have {
                    name: "h0".to_string(),
                    says: eq(typed(rational(&norm)), whole(0, Num::Real)),
                    proof: Box::new(Proof::Term(reached)),
                },
                t::call(
                    "norm_num",
                    vec![super::doc::TacticArg::At(vec![
                        super::doc::Location::Hypothesis("h0".to_string()),
                    ])],
                ),
            ]);
        }
        if !reals::pure_logarithms(&gap) {
            return Route::no("a disequality the decider does not show");
        }
        let Some(read) = gap.logarithmic() else {
            return Route::no("logarithms that do not read");
        };
        let Ok(r) = reals::logarithm_ratio(&read.logs) else {
            return Route::no("a ratio of logarithms too large");
        };
        let hl = match self.log_fact(&r.ratio) {
            Route::Built(h) => h,
            Route::Declined(d) => return Route::Declined(d),
        };
        let n = Q::from_integer(r.scale.clone());
        let mut logs = Real::default();
        for (p, m) in reals::factored(&r.ratio).unwrap_or_default() {
            logs = logs.plus(
                &Real::atom(Atom::Ln(p))
                    .times(&Real::rational(Q::from_integer(BigInt::from(m)))),
            );
        }
        let logs_poly = self.real_poly(&logs);
        let mut terms = vec![
            self.multiple(&field::constant(n.clone()), t::hyp("h")),
            t::hyp(&hl),
        ];
        match self.combination(
            Quotient::whole(logs_poly),
            difference.times(&Quotient::whole(field::constant(n))),
        ) {
            Route::Built(more) => terms.extend(more),
            Route::Declined(d) => return Route::Declined(d),
        }
        let zero = Printed::cast(whole(0, Num::Real), real());
        let positive = show_by_norm_num(less(zero, rational(&r.ratio)));
        let not_one =
            show_by_norm_num(unequal(typed(rational(&r.ratio)), whole(1, Num::Real)));
        let is_zero = t::bracket(t::by_term(Proof::By(closing(terms))));
        Route::Built(vec![
            Tactic::Intro(vec!["h".to_string()]),
            Tactic::Exact(lemma(
                "Real.log_ne_zero_of_pos_of_ne_one",
                vec![positive, not_one, is_zero],
            )),
        ])
    }

    /// A membership of ℕ, ℕ₀ or ℤ, which Lean writes as a whole number m
    /// with `(m : ℝ) = x`, and `0 < m` or `0 ≤ m` before it: the whole
    /// number x is, and its equation; or, denied, the whole number taken
    /// and its equation brought to x's value, which is no whole number, or
    /// one its bound refutes (`omega`).
    fn membership(
        &mut self,
        claim: &Node,
        system: &Term,
        denied: bool,
    ) -> Route<Vec<Tactic>> {
        let bounded = match system.label() {
            Some("cn" | "cn0") => true,
            Some("cz") => false,
            _ => return Route::no("a membership real arithmetic does not write"),
        };
        let Some(x) = claim.children.first() else {
            return Route::no("a membership without a member");
        };
        let v = match self.value_of(x) {
            Route::Built(v) => v,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(q) = v.as_surd().and_then(|s| s.as_rational()) else {
            return Route::no("a membership of a value that is not rational");
        };
        let rx = match self.read_node(x) {
            Route::Built(r) => r,
            Route::Declined(d) => return Route::Declined(d),
        };
        if !denied {
            if !q.is_integer() {
                return Route::no("a membership of a value that is no whole number");
            }
            let terms = match self
                .combination(Quotient::whole(field::constant(q.clone())), rx)
            {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let n =
                Printed::numeral(q.to_integer().to_string(), LeanType::Num(Num::Int));
            let equation = t::bracket(t::by_term(Proof::By(closing(terms))));
            let mut items = vec![n];
            if bounded {
                items.push(t::bracket(t::by_term(Proof::By(t::call(
                    "norm_num",
                    vec![],
                )))));
            }
            items.push(equation);
            return Route::Built(vec![Tactic::Exact(Printed {
                kind: TermKind::Listed {
                    brackets: super::doc::Brackets::Angle,
                    items,
                },
                ty: None,
            })]);
        }
        let terms =
            match self.combination(rx, Quotient::whole(field::constant(q.clone()))) {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
        let name = |n: &str| Printed::letter(n, LeanType::Prop);
        let mut pattern = vec![name("m")];
        if bounded {
            pattern.push(name("hm"));
        }
        pattern.push(name("h"));
        let m_said =
            Printed::cast(Printed::letter("m", LeanType::Num(Num::Int)), real());
        let mut all = vec![t::hyp("h")];
        all.extend(terms);
        let at_h1 = || {
            super::doc::TacticArg::At(vec![super::doc::Location::Hypothesis(
                "h1".into(),
            )])
        };
        let mut out = vec![
            t::call(
                "rintro",
                vec![super::doc::TacticArg::Term(Printed {
                    kind: TermKind::Listed {
                        brackets: super::doc::Brackets::Angle,
                        items: pattern,
                    },
                    ty: None,
                })],
            ),
            Tactic::Have {
                name: "h1".to_string(),
                says: eq(m_said, rational(&q)),
                proof: Box::new(Proof::By(closing(all))),
            },
        ];
        if !q.is_integer() {
            out.push(t::call("field_simp", vec![at_h1()]));
        }
        out.push(t::call("norm_cast", vec![at_h1()]));
        out.push(t::call("omega", vec![]));
        Route::Built(out)
    }

    /// `linear_combination` closing `left = right`, each side read with
    /// the pieces as atoms (`combination`); `ring1` where it needs none.
    fn compared(&mut self, left: Quotient, right: Quotient) -> Route<Tactic> {
        match self.combination(left, right) {
            Route::Built(terms) => Route::Built(closing(terms)),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// What `left − right` is a combination of: the pieces less their
    /// values, each times what the difference multiplies it by, and the
    /// multiples of (√p)² − p the rest is.
    fn combination(&mut self, left: Quotient, right: Quotient) -> Route<Vec<Printed>> {
        let under = left.under.times(&right.under);
        let Some(under) = under.constant_value().filter(|u| !u.is_zero()) else {
            return Route::no(
                "a division the sides keep by a term that is not a number",
            );
        };
        let mut rest = left
            .over
            .times(&right.under)
            .minus(&right.over.times(&left.under))
            .scaled(&under.recip());
        let mut sum: Vec<Printed> = Vec::new();
        // Each piece put as its value in turn: what the difference loses
        // is the piece less its value times a multiple.
        for k in 0..self.pieces.len() {
            let atom = self.pieces[k].atom.clone();
            if !mentions(&rest, &atom) {
                continue;
            }
            let value = self.real_poly(&self.pieces[k].value.clone());
            let put = substituted_atom(&rest, &atom, &value);
            let gap = field::atom(&atom).minus(&value);
            let Some(times) = field::exactly(&rest.minus(&put), &gap) else {
                return Route::no("a piece the difference does not take out");
            };
            sum.push(self.multiple(&times, t::hyp(&self.pieces[k].name.clone())));
            rest = put;
        }
        let roots: IndexMap<Rpn, u64> = self
            .atoms
            .iter()
            .filter_map(|(a, b)| match b {
                Base::Root(p) => Some((a.clone(), *p)),
                _ => None,
            })
            .collect();
        let Some(multiples) = root_multiples(rest, &roots) else {
            return Route::no("the two sides are not one value");
        };
        for (p, times) in &multiples {
            let name = self.square(*p);
            sum.push(self.multiple(times, t::hyp(&name)));
        }
        Route::Built(sum)
    }

    /// `(times) * fact`, or the fact alone where it is taken once.
    fn multiple(&self, times: &Poly, fact: Printed) -> Printed {
        match times.constant_value() {
            Some(c) if c.is_one() => fact,
            _ => Printed::infix(
                Op::TIMES,
                t::bracket(self.poly_term(times)),
                fact,
                real(),
            ),
        }
    }

    /// The name of `(√p)² = p`, stated where it is first asked.
    fn square(&mut self, p: u64) -> String {
        let name = format!("hr{p}");
        if self.squares.insert(p) {
            self.lines.push(Tactic::Have {
                name: name.clone(),
                says: Printed::infix(
                    Op::EQUALS,
                    Printed::infix(
                        Op::POWER,
                        root_of_prime(p),
                        whole(2, Num::Nat),
                        real(),
                    ),
                    whole(p, Num::Real),
                    LeanType::Prop,
                ),
                proof: Box::new(Proof::Term(Printed::applied(
                    "Real.sq_sqrt",
                    Source::Mathlib,
                    vec![at_least_zero(whole(p, Num::Real))],
                    LeanType::Prop,
                ))),
            });
        }
        name
    }

    /// The term read as a quotient of polynomials in the atoms, each piece
    /// stated so far an atom of its own, and every other part a law puts
    /// as its value as that value; None where it holds anything else.
    fn read(&mut self, term: &Term) -> Option<Quotient> {
        let atom = term.rpn(&self.labels);
        if self.pieces.iter().any(|p| p.atom == atom) || self.opaque.contains_key(&atom)
        {
            return Some(Quotient::whole(field::atom(&atom)));
        }
        let atomic =
            matches!(term.label(), Some("cpi" | "ceu")) && term.children().is_empty();
        if atomic || kind_of(term).is_some() {
            let Route::Built(reals::Value::Exact(v)) = reals::closed_value(term) else {
                return None;
            };
            return Some(Quotient::whole(self.real_poly(&v)));
        }
        if let Some(n) = numerals::value(term) {
            return Some(Quotient::whole(field::constant(Q::from_integer(
                BigInt::from(n),
            ))));
        }
        let kids = term.children();
        match (term.label(), kids) {
            (Some(field::NEG), [x]) => {
                let x = self.read(x)?;
                Some(Quotient::whole(Poly::default()).minus(&x))
            }
            (Some("co"), [a, b, op]) => {
                let how = op.label()?;
                if how == field::EXP {
                    let k = whole_value(b)?;
                    if !(0..=64).contains(&k) {
                        return None;
                    }
                    let base = self.read(a)?;
                    let mut out = Quotient::whole(field::one());
                    for _ in 0..k {
                        out = out.times(&base);
                    }
                    return Some(out);
                }
                let (a, b) = (self.read(a)?, self.read(b)?);
                match how {
                    field::ADD => Some(a.plus(&b)),
                    field::SUB => Some(a.minus(&b)),
                    field::MUL => Some(a.times(&b)),
                    field::DIV => Some(a.over_under(&b)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// A value as a polynomial in the atoms, each atom noted.
    fn real_poly(&mut self, value: &Real) -> Poly {
        let mut out = Poly::default();
        for (monomial, surd) in &value.parts {
            for (basis, weight) in &surd.parts {
                let mut part = field::constant(weight.clone());
                for p in basis {
                    part = part.times(&field::atom(&self.base_atom(Base::Root(*p))));
                }
                for (a, power) in monomial {
                    let base = match a {
                        Atom::Pi => Base::Pi,
                        Atom::E => Base::E,
                        Atom::Ln(p) => Base::Log(*p),
                    };
                    let atom = field::atom(&self.base_atom(base));
                    for _ in 0..*power {
                        part = part.times(&atom);
                    }
                }
                out = out.plus(&part);
            }
        }
        out
    }

    /// The atom of a base, as the decider reads it, noted.
    fn base_atom(&mut self, base: Base) -> Rpn {
        let n = |l: &str| Term::apply(l, Vec::new());
        let numeral = |p: u64| numerals::numeral_term(&BigUint::from(p));
        let term = match base {
            Base::Root(p) => Term::apply("cfv", vec![numeral(p), n("csqrt")]),
            Base::Log(p) => Term::apply("cfv", vec![numeral(p), n("clog")]),
            Base::Pi => n("cpi"),
            Base::E => n("ceu"),
        };
        let atom = term.rpn(&self.labels);
        self.atoms.insert(atom.clone(), base);
        atom
    }

    /// A polynomial in the atoms and the pieces as a Lean term in ℝ.
    fn poly_term(&self, p: &Poly) -> Printed {
        let mut out: Option<Printed> = None;
        let mut terms: Vec<_> = p.terms.iter().collect();
        terms.sort_by_key(|(m, _)| field::order(m));
        for (monomial, weight) in terms {
            let mut parts: Vec<Printed> = coefficient_term(&weight.abs(), Num::Real)
                .into_iter()
                .collect();
            for (atom, power) in monomial {
                let said = match self.atoms.get(atom) {
                    Some(b) => base_term(*b),
                    None if self.opaque.contains_key(atom) => {
                        at_least(self.opaque[atom].clone(), 76)
                    }
                    None => {
                        let piece = self.pieces.iter().find(|p| p.atom == *atom);
                        at_least(piece.expect("an atom of a piece").said.clone(), 76)
                    }
                };
                parts.push(match power {
                    1 => said,
                    k => Printed::infix(
                        Op::POWER,
                        said,
                        whole(u64::from(*k), Num::Nat),
                        real(),
                    ),
                });
            }
            let body = parts
                .into_iter()
                .reduce(|l, r| Printed::infix(Op::TIMES, l, r, real()))
                .unwrap_or_else(|| whole(1, Num::Real));
            out = Some(match (out, weight.is_negative()) {
                (None, false) => body,
                (None, true) => Printed::of(TermKind::Neg(Box::new(body)), real()),
                (Some(s), false) => Printed::infix(Op::PLUS, s, body, real()),
                (Some(s), true) => Printed::infix(Op::MINUS, s, body, real()),
            });
        }
        out.unwrap_or_else(|| whole(0, Num::Real))
    }

    /// A value as a Lean term: each part its coefficient times its roots
    /// and then its other atoms, the parts added.
    fn real_term(&mut self, value: &Real) -> Printed {
        let p = self.real_poly(value);
        self.poly_term(&p)
    }

    /// `x = y`, proved where x reads as y.
    fn equal(&mut self, x: &Term, y: &Quotient) -> Route<Tactic> {
        let Some(read) = self.read(x) else {
            return Route::no("a part real arithmetic does not read");
        };
        self.compared(read, y.clone())
    }

    /// A root: its radicand c²·p₁·…·pₖ, the root of c² taken off as c,
    /// and the root of the product split into the roots of its primes.
    fn root_law(&mut self, root: &Node) -> Route<Law> {
        let [radicand] = root.children.as_slice() else {
            return Route::no("a root without one radicand");
        };
        let Route::Built(surds::Value::Exact(v)) =
            surds::closed_value(&self.term(radicand))
        else {
            return Route::no("a root of a number with no value");
        };
        let Some(r) = v.as_rational() else {
            return Route::no("a root of a number that is not rational");
        };
        let Ok(root_value) = surds::root_of(&r) else {
            return Route::no("a root real arithmetic does not take");
        };
        let x = match self.number(radicand) {
            Route::Built(x) => typed(x),
            Route::Declined(d) => return Route::Declined(d),
        };
        let c = rational(&root_value.coefficient);
        let primes = &root_value.primes;
        let squared = Printed::infix(
            Op::POWER,
            at_least(c.clone(), 76),
            whole(2, Num::Nat),
            real(),
        );
        let product = primes_product(primes);
        let has_square = !root_value.coefficient.is_one() || primes.is_empty();
        let target = match (has_square, &product) {
            (true, Some(p)) => {
                Printed::infix(Op::TIMES, squared.clone(), p.clone(), real())
            }
            (true, None) => squared.clone(),
            (false, Some(p)) => p.clone(),
            (false, None) => unreachable!("a root with no square part has a prime"),
        };
        let mut want = field::constant(
            root_value.coefficient.clone() * root_value.coefficient.clone(),
        );
        for p in primes {
            want = want.scaled(&field::q(*p as i64));
        }
        let worked = match self.equal(&self.term(radicand), &Quotient::whole(want)) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut rules = vec![congr("Real.sqrt", show(eq(x, target), worked))];
        if has_square {
            if let Some(p) = &product {
                rules.push(lemma(
                    "Real.sqrt_mul",
                    vec![at_least_zero_by(squared.clone(), "positivity"), p.clone()],
                ));
            }
            rules.push(lemma("Real.sqrt_sq", vec![at_least_zero(c.clone())]));
        }
        for (k, p) in primes.iter().enumerate() {
            let Some(rest) = primes_product(&primes[k + 1..]) else {
                break;
            };
            rules.push(lemma(
                "Real.sqrt_mul",
                vec![at_least_zero(whole(*p, Num::Real)), rest],
            ));
        }
        let roots = roots_product(primes);
        let leaves = match (has_square, roots) {
            (true, Some(r)) => Printed::infix(Op::TIMES, c, r, real()),
            (true, None) => c,
            (false, Some(r)) => r,
            (false, None) => unreachable!("a root with no square part has a prime"),
        };
        Route::Built(Law {
            tactics: vec![t::call("rw", vec![t::rules(rules)])],
            leaves,
        })
    }

    /// A quotient x / y, y holding a root, is its value v: y stated not 0,
    /// and x = v·y compared (`div_eq_iff`).
    fn quotient_law(&mut self, quotient: &Node, value: &Real) -> Route<Law> {
        let [x, y] = quotient.children.as_slice() else {
            return Route::no("a quotient without two sides");
        };
        let apart = match self.nonzero(y) {
            Route::Built(a) => a,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (Some(xr), Some(yr)) = (self.read(&self.term(x)), self.read(&self.term(y)))
        else {
            return Route::no("a quotient whose sides real arithmetic does not read");
        };
        let v = self.real_poly(value);
        let close = match self.compared(xr, Quotient::whole(v).times(&yr)) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let leaves = self.real_term(value);
        Route::Built(Law {
            tactics: vec![
                t::call(
                    "rw",
                    vec![t::rules(vec![lemma("div_eq_iff", vec![t::hyp(&apart)])])],
                ),
                close,
            ],
            leaves,
        })
    }

    /// A power x^(−k) is its value v: x^(−k) is (xᵏ)⁻¹ (`zpow_neg`), and
    /// that is v where v·xᵏ = 1 (`inv_eq_of_mul_eq_one_left`), compared.
    fn power_law(&mut self, power: &Node, value: &Real) -> Route<Law> {
        let [base, exponent] = power.children.as_slice() else {
            return Route::no("a power without a base and an exponent");
        };
        let Some(k) = whole_value(&self.term(exponent)).map(|k| k.unsigned_abs())
        else {
            return Route::no("a power to no whole number");
        };
        let Ok(k) = u32::try_from(k) else {
            return Route::no("a power too large");
        };
        let bs = match self.number(base) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let rb = match self.read_node(base) {
            Route::Built(r) => r,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut powered = Quotient::whole(field::one());
        for _ in 0..k {
            powered = powered.times(&rb);
        }
        let v = self.real_poly(value);
        let close = match self.compared(
            Quotient::whole(v).times(&powered),
            Quotient::whole(field::one()),
        ) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let leaves = self.real_term(value);
        let base_power = match k {
            1 => at_least(bs, 71),
            _ => Printed::infix(
                Op::POWER,
                at_least(bs, 76),
                whole(u64::from(k), Num::Nat),
                real(),
            ),
        };
        let product =
            Printed::infix(Op::TIMES, at_least(leaves.clone(), 71), base_power, real());
        let unfold = match k {
            1 => "zpow_one",
            _ => "zpow_ofNat",
        };
        Route::Built(Law {
            tactics: vec![
                t::call(
                    "rw",
                    vec![t::rules(vec![t::lemma("zpow_neg"), t::lemma(unfold)])],
                ),
                Tactic::Exact(lemma(
                    "inv_eq_of_mul_eq_one_left",
                    vec![show(eq(product, whole(1, Num::Real)), close)],
                )),
            ],
            leaves,
        })
    }

    /// `have hyK : y ≠ 0`, y a value holding a root: y times its cofactor
    /// is a rational not 0 (`surds::cofactor`, as `elab::real`'s
    /// `surd_apart` shows it), so y is not 0 (`left_ne_zero_of_mul`).
    fn nonzero(&mut self, y: &Node) -> Route<String> {
        let Route::Built(surds::Value::Exact(v)) = surds::closed_value(&self.term(y))
        else {
            return Route::no("a divisor with no value");
        };
        let surds::Cofactor { times, norm } = surds::cofactor(&v);
        let ys = match self.number(y) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(yr) = self.read(&self.term(y)) else {
            return Route::no("a divisor real arithmetic does not read");
        };
        let cofactor = Real::surd(times);
        let cofactor_poly = self.real_poly(&cofactor);
        let cofactor_said = self.real_term(&cofactor);
        let product = Printed::infix(
            Op::TIMES,
            at_least(ys.clone(), 71),
            at_least(cofactor_said, 71),
            real(),
        );
        let worked = match self.compared(
            yr.times(&Quotient::whole(cofactor_poly)),
            Quotient::whole(field::constant(norm.clone())),
        ) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let is_norm = show(eq(product.clone(), rational(&norm)), worked);
        let product_apart = show(
            unequal(product, whole(0, Num::Real)),
            Tactic::Seq(vec![
                t::call("rw", vec![t::rules(vec![is_norm])]),
                t::call("norm_num", vec![]),
            ]),
        );
        self.apart += 1;
        let name = format!("hy{}", self.apart);
        self.lines.push(Tactic::Have {
            name: name.clone(),
            says: unequal(ys, whole(0, Num::Real)),
            proof: Box::new(Proof::Term(lemma(
                "left_ne_zero_of_mul",
                vec![product_apart],
            ))),
        });
        Route::Built(name)
    }

    /// A logarithm of q·eᵏ, q = A/B: the argument written as the product
    /// of its primes' powers and eᵏ over the product of the denominator's,
    /// and each logarithm of a product, a quotient and a power taken apart.
    fn log_law(&mut self, log: &Node) -> Route<Law> {
        let Some(x) = log.children.last() else {
            return Route::no("a logarithm without an argument");
        };
        let xt = self.term(x);
        let Route::Built(reals::Value::Exact(v)) = reals::closed_value(&xt) else {
            return Route::no("a logarithm of a number with no value");
        };
        let Some((ratio, k)) = v.rational_times_e() else {
            return Route::no(
                "a logarithm of a number that is no rational times a power of e",
            );
        };
        let xs = match self.number(x) {
            Route::Built(s) => typed(s),
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(read) = self.read(&xt) else {
            return Route::no("a logarithm's argument real arithmetic does not read");
        };
        self.log_of(xs, read, &ratio, k)
    }

    /// The law of the logarithm of `xs`, read as `read`, whose value is
    /// ratio·eᵏ.
    fn log_of(&mut self, xs: Printed, read: Quotient, ratio: &Q, k: u32) -> Route<Law> {
        let Ok(primes) = reals::factored(ratio) else {
            return Route::no("a logarithm of a number too large to factor");
        };
        let mut above: Vec<Factor> = primes
            .iter()
            .filter(|(_, n)| **n > 0)
            .map(|(p, n)| Factor::Prime(*p, n.unsigned_abs() as u32))
            .collect();
        if k > 0 {
            above.push(Factor::E(k));
        }
        let below: Vec<Factor> = primes
            .iter()
            .filter(|(_, n)| **n < 0)
            .map(|(p, n)| Factor::Prime(*p, n.unsigned_abs() as u32))
            .collect();
        let top = product_term(&above);
        let target = match below.is_empty() {
            true => top.clone(),
            false => Printed::infix(
                Op::DIVIDE,
                top.clone(),
                at_least(product_term(&below), 71),
                real(),
            ),
        };
        let mut rules = Vec::new();
        if casts_dropped(&xs) != casts_dropped(&target) {
            let mut want = Quotient::whole(field::constant(ratio.clone()));
            for _ in 0..k {
                want =
                    want.times(&Quotient::whole(field::atom(&self.base_atom(Base::E))));
            }
            let worked = match self.compared(read, want) {
                Route::Built(w) => w,
                Route::Declined(d) => return Route::Declined(d),
            };
            rules.push(congr("Real.log", show(eq(xs, target), worked)));
        }
        let leaves = match below.is_empty() {
            true => log_of_product(&above, &mut rules),
            false => {
                let bottom = product_term(&below);
                rules.push(lemma(
                    "Real.log_div",
                    vec![nonzero_numeral(top), nonzero_numeral(bottom)],
                ));
                let a = log_of_product(&above, &mut rules);
                let b = log_of_product(&below, &mut rules);
                Printed::infix(Op::MINUS, a, at_least(b, 66), real())
            }
        };
        Route::Built(Law {
            tactics: vec![t::call("rw", vec![t::rules(rules)])],
            leaves,
        })
    }

    /// An exponential of k + Σ nₚ·ln p, k and each nₚ whole and at least 0:
    /// the argument written as that sum, the exponential of a sum the
    /// product of the exponentials, of n·x the n-th power of exp x, and of
    /// ln p, p.
    fn exp_law(&mut self, exp: &Node) -> Route<Law> {
        let Some(x) = exp.children.last() else {
            return Route::no("an exponential without an argument");
        };
        let xt = self.term(x);
        let Route::Built(reals::Value::Exact(v)) = reals::closed_value(&xt) else {
            return Route::no("an exponential of a number with no value");
        };
        let Some(read) = v.logarithmic() else {
            return Route::no(
                "an exponential of a number that is no sum of logarithms",
            );
        };
        let whole_of = |q: &Q| -> Option<u32> {
            q.is_integer().then(|| q.to_integer().to_u32()).flatten()
        };
        let Some(k) = whole_of(&read.constant) else {
            return Route::no(
                "an exponential of a number with no whole part at least 0",
            );
        };
        let mut terms: Vec<(Printed, Vec<Printed>, Printed)> = Vec::new();
        if k > 0 {
            let e = base_term(Base::E);
            let (said, rules, leaves) = match k {
                1 => (whole(1, Num::Real), Vec::new(), e),
                _ => (
                    Printed::infix(Op::TIMES, natural(k), whole(1, Num::Real), real()),
                    vec![lemma(
                        "Real.exp_nat_mul",
                        vec![whole(1, Num::Real), whole(u64::from(k), Num::Nat)],
                    )],
                    Printed::infix(Op::POWER, e, whole(u64::from(k), Num::Nat), real()),
                ),
            };
            terms.push((said, rules, leaves));
        }
        for (p, n) in &read.logs {
            let Some(n) = whole_of(n).filter(|n| *n > 0) else {
                return Route::no("an exponential of a logarithm taken a number of times not whole and above 0");
            };
            let log = base_term(Base::Log(*p));
            let positive = show(
                Printed::infix(
                    Op::of("<").expect("< is an operator"),
                    Printed::cast(whole(0, Num::Real), real()),
                    whole(*p, Num::Real),
                    LeanType::Prop,
                ),
                t::call("norm_num", vec![]),
            );
            let back = lemma("Real.exp_log", vec![positive]);
            let (said, rules, leaves) = match n {
                1 => (log, vec![back], whole(*p, Num::Real)),
                _ => (
                    Printed::infix(Op::TIMES, natural(n), log.clone(), real()),
                    vec![
                        lemma(
                            "Real.exp_nat_mul",
                            vec![log, whole(u64::from(n), Num::Nat)],
                        ),
                        back,
                    ],
                    Printed::infix(
                        Op::POWER,
                        whole(*p, Num::Real),
                        whole(u64::from(n), Num::Nat),
                        real(),
                    ),
                ),
            };
            terms.push((said, rules, leaves));
        }
        // exp(0) = 1 (`Real.exp_zero`), the argument written as 0 first.
        if terms.is_empty() {
            terms.push((
                whole(0, Num::Real),
                vec![t::lemma("Real.exp_zero")],
                whole(1, Num::Real),
            ));
        }
        let Some(((first_said, first_rules, first_leaves), rest)) = terms.split_first()
        else {
            unreachable!("an exponential's argument has a term at least");
        };
        let mut said = first_said.clone();
        let mut leaves = first_leaves.clone();
        let mut lemmas = first_rules.clone();
        let mut sums = Vec::new();
        for (s, r, l) in rest {
            said = Printed::infix(Op::PLUS, said, s.clone(), real());
            leaves = Printed::infix(Op::TIMES, leaves, l.clone(), real());
            lemmas.extend(r.iter().cloned());
            sums.push(lemma("Real.exp_add", Vec::new()));
        }
        // The sum is written from the left, so each `Real.exp_add` takes
        // the last term off, outermost first.
        let xs = match self.number(x) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut rules = Vec::new();
        if xs != said {
            let want = match self.read_printed_sum(&read) {
                Some(w) => w,
                None => return Route::no("an exponential's argument not read"),
            };
            let worked = match self.equal(&xt, &want) {
                Route::Built(w) => w,
                Route::Declined(d) => return Route::Declined(d),
            };
            rules.push(congr("Real.exp", show(eq(typed(xs), said), worked)));
        }
        rules.extend(sums);
        rules.extend(lemmas);
        Route::Built(Law {
            tactics: vec![t::call("rw", vec![t::rules(rules)])],
            leaves,
        })
    }

    /// k + Σ nₚ·ln p as a polynomial in the atoms.
    fn read_printed_sum(&mut self, read: &reals::Logarithmic) -> Option<Quotient> {
        let mut out = field::constant(read.constant.clone());
        for (p, n) in &read.logs {
            out = out.plus(&field::atom(&self.base_atom(Base::Log(*p))).scaled(n));
        }
        Some(Quotient::whole(out))
    }

    /// A sine or cosine of q·π: its angle written as t + π/2 + π + n·2π,
    /// where it reaches each, t one of 0, π/6, π/4 and π/3; the whole turns
    /// taken off, then π and π/2, and the value Mathlib names at t.
    fn trig_law(&mut self, node: &Node, f: Trig) -> Route<Law> {
        let Some(angle) = node.children.last() else {
            return Route::no("a sine or cosine without an angle");
        };
        let at = self.term(angle);
        let Route::Built(reals::Value::Exact(a)) = reals::closed_value(&at) else {
            return Route::no("an angle with no value");
        };
        let Some(q) = reals::multiple_of_pi(&a) else {
            return Route::no("an angle that is no rational multiple of π");
        };
        let r = reals::turned(&q);
        let turns = ((q.clone() - r.clone()) / field::q(2)).to_integer();
        let half = Q::new(BigInt::from(1), BigInt::from(2));
        let past_pi = r >= field::q(1);
        let r1 = if past_pi {
            r.clone() - field::q(1)
        } else {
            r.clone()
        };
        let past_half = r1 >= half;
        let base = if past_half { r1 - half.clone() } else { r1 };
        let pi = base_term(Base::Pi);
        let base_said = match (base.numer().to_i64(), base.denom().to_i64()) {
            (Some(0), _) => whole(0, Num::Real),
            (Some(1), Some(d)) => Printed::infix(
                Op::DIVIDE,
                pi.clone(),
                whole(d as u64, Num::Real),
                real(),
            ),
            _ => return Route::no("an angle real arithmetic does not reduce"),
        };
        let mut form = base_said.clone();
        let mut want = field::atom(&self.base_atom(Base::Pi)).scaled(&base);
        let pi_atom = field::atom(&self.base_atom(Base::Pi));
        if past_half {
            form = Printed::infix(
                Op::PLUS,
                form,
                Printed::infix(Op::DIVIDE, pi.clone(), whole(2, Num::Real), real()),
                real(),
            );
            want = want.plus(&pi_atom.scaled(&half));
        }
        if past_pi {
            form = Printed::infix(Op::PLUS, form, pi.clone(), real());
            want = want.plus(&pi_atom);
        }
        let turned = !turns.is_zero();
        if turned {
            // `((n : ℤ) : ℝ)`, as the lemma writes its whole number of turns.
            let int = LeanType::Num(Num::Int);
            let n = Printed::cast(
                Printed::cast(Printed::numeral(turns.to_string(), int.clone()), int),
                real(),
            );
            let two_pi =
                Printed::infix(Op::TIMES, whole(2, Num::Real), pi.clone(), real());
            form = Printed::infix(
                Op::PLUS,
                form,
                Printed::infix(Op::TIMES, n, t::bracket(two_pi), real()),
                real(),
            );
            want = want
                .plus(&pi_atom.scaled(&(Q::from_integer(turns.clone()) * field::q(2))));
        }
        let worked = match self.equal(&at, &Quotient::whole(want)) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        let xs = match self.number(angle) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (name, function) = match f {
            Trig::Sine => ("sin", "Real.sin"),
            Trig::Cosine => ("cos", "Real.cos"),
        };
        // The angle written as its parts where it is not so already.
        let mut rules = Vec::new();
        if casts_dropped(&xs) != casts_dropped(&form) {
            rules.push(congr(function, show(eq(xs, form), worked)));
        }
        if turned {
            rules.push(t::lemma(&format!("Real.{name}_add_int_mul_two_pi")));
        }
        // Outermost first: π off, f(x + π) = −f(x); then π/2 off,
        // sin(x + π/2) = cos(x) and cos(x + π/2) = −sin(x).
        if past_pi {
            rules.push(t::lemma(&format!("Real.{name}_add_pi")));
        }
        if past_half {
            rules.push(t::lemma(&format!("Real.{name}_add_pi_div_two")));
        }
        let left = match (past_half, f) {
            (true, Trig::Sine) => Trig::Cosine,
            (true, Trig::Cosine) => Trig::Sine,
            (false, f) => f,
        };
        let (named, mut leaves) = named_value(left, &base);
        rules.push(t::lemma(&named));
        if past_half && matches!(f, Trig::Cosine) {
            leaves = negated(leaves);
        }
        if past_pi {
            leaves = negated(leaves);
        }
        Route::Built(Law {
            tactics: vec![t::call("rw", vec![t::rules(rules)])],
            leaves,
        })
    }
}

/// `-(x)`.
fn negated(x: Printed) -> Printed {
    Printed::of(TermKind::Neg(Box::new(t::bracket(x))), real())
}

fn trig_name(f: Trig) -> &'static str {
    match f {
        Trig::Sine => "sin",
        Trig::Cosine => "cos",
    }
}

/// The lemma naming a sine's or cosine's value at t·π, t one of 0, 1/6,
/// 1/4 and 1/3, and the value as it states it.
fn named_value(f: Trig, t: &Q) -> (String, Printed) {
    let root_half = |p: u64| {
        Printed::infix(Op::DIVIDE, root_of_prime(p), whole(2, Num::Real), real())
    };
    let half =
        || Printed::infix(Op::DIVIDE, whole(1, Num::Real), whole(2, Num::Real), real());
    let twelfths = (t * field::q(12)).to_integer().to_i64().unwrap_or(-1);
    let f_name = trig_name(f);
    match (f, twelfths) {
        (Trig::Sine, 0) => ("Real.sin_zero".into(), whole(0, Num::Real)),
        (Trig::Cosine, 0) => ("Real.cos_zero".into(), whole(1, Num::Real)),
        (Trig::Sine, 2) => ("Real.sin_pi_div_six".into(), half()),
        (Trig::Cosine, 2) => ("Real.cos_pi_div_six".into(), root_half(3)),
        (_, 3) => (format!("Real.{f_name}_pi_div_four"), root_half(2)),
        (Trig::Sine, 4) => ("Real.sin_pi_div_three".into(), root_half(3)),
        (Trig::Cosine, 4) => ("Real.cos_pi_div_three".into(), half()),
        _ => unreachable!("a reduced angle is 0, π/6, π/4 or π/3"),
    }
}

/// A law's proof, and the value as it leaves it.
struct Law {
    tactics: Vec<Tactic>,
    leaves: Printed,
}

/// A factor of a logarithm's argument: a prime to a power, or e to one.
enum Factor {
    Prime(u64, u32),
    E(u32),
}

impl Factor {
    fn term(&self) -> Printed {
        let (base, k) = match self {
            Factor::Prime(p, k) => (whole(*p, Num::Real), *k),
            Factor::E(k) => (base_term(Base::E), *k),
        };
        match k {
            1 => base,
            _ => Printed::infix(Op::POWER, base, whole(u64::from(k), Num::Nat), real()),
        }
    }

    /// The rules taking its logarithm, and what they leave.
    fn logged(&self, rules: &mut Vec<Printed>) -> Printed {
        match self {
            Factor::Prime(p, 1) => base_term(Base::Log(*p)),
            Factor::Prime(p, k) => {
                rules.push(lemma(
                    "Real.log_pow",
                    vec![whole(*p, Num::Real), whole(u64::from(*k), Num::Nat)],
                ));
                Printed::infix(Op::TIMES, natural(*k), base_term(Base::Log(*p)), real())
            }
            Factor::E(1) => {
                rules.push(lemma("Real.log_exp", vec![whole(1, Num::Real)]));
                whole(1, Num::Real)
            }
            Factor::E(k) => {
                rules.push(lemma(
                    "Real.log_pow",
                    vec![base_term(Base::E), whole(u64::from(*k), Num::Nat)],
                ));
                rules.push(lemma("Real.log_exp", vec![whole(1, Num::Real)]));
                Printed::infix(Op::TIMES, natural(*k), whole(1, Num::Real), real())
            }
        }
    }
}

/// f₁·(f₂·(…)), nested from the right; 1 where there are none.
fn product_term(factors: &[Factor]) -> Printed {
    let Some((last, rest)) = factors.split_last() else {
        return whole(1, Num::Real);
    };
    rest.iter().rev().fold(last.term(), |acc, f| {
        Printed::infix(Op::TIMES, f.term(), acc, real())
    })
}

/// The logarithm of a product of factors taken apart: the rules, and the
/// sum it leaves, nested from the right as `Real.log_mul` leaves it.
fn log_of_product(factors: &[Factor], rules: &mut Vec<Printed>) -> Printed {
    let Some((first, rest)) = factors.split_first() else {
        rules.push(t::lemma("Real.log_one"));
        return whole(0, Num::Real);
    };
    if rest.is_empty() {
        return first.logged(rules);
    }
    rules.push(lemma(
        "Real.log_mul",
        vec![
            nonzero_numeral(first.term()),
            nonzero_numeral(product_term(rest)),
        ],
    ));
    let head = first.logged(rules);
    let tail = log_of_product(rest, rules);
    Printed::infix(Op::PLUS, head, at_least(tail, 66), real())
}

/// What a closed term is that a law puts as its value.
fn kind_of(term: &Term) -> Option<Kind> {
    if surds::is_root(term) {
        return Some(Kind::Root);
    }
    if surds::applies(term, "clog") {
        return Some(Kind::Log);
    }
    if surds::applies(term, "ce") {
        return Some(Kind::Exp);
    }
    if let Some(f) = Trig::of(term) {
        return Some(Kind::Trig(f));
    }
    if let [_, exponent, op] = term.children() {
        if term.label() == Some("co")
            && op.label() == Some(field::EXP)
            && whole_value(exponent).is_some_and(|k| k < 0)
        {
            return Some(Kind::Power);
        }
    }
    divides_by_root(term).then_some(Kind::Quotient)
}

/// Whether a term is a quotient by a value holding a root.
fn divides_by_root(term: &Term) -> bool {
    let [_, below, op] = term.children() else {
        return false;
    };
    term.label() == Some("co")
        && op.label() == Some(field::DIV)
        && matches!(
            surds::closed_value(below),
            Route::Built(surds::Value::Exact(v)) if v.as_rational().is_none()
        )
}

/// The whole number a closed term is, where it is one.
fn whole_value(term: &Term) -> Option<i64> {
    let Route::Built(surds::Value::Exact(v)) = surds::closed_value(term) else {
        return None;
    };
    let r = v.as_rational()?;
    r.is_integer().then(|| r.to_integer().to_i64()).flatten()
}

/// Whether a polynomial holds an atom.
fn mentions(p: &Poly, atom: &Rpn) -> bool {
    p.terms.keys().any(|m| m.iter().any(|(a, _)| a == atom))
}

/// The polynomial with an atom put as a value.
fn substituted_atom(p: &Poly, atom: &Rpn, value: &Poly) -> Poly {
    let mut out = Poly::default();
    for (monomial, weight) in &p.terms {
        let mut part = field::constant(weight.clone());
        for (a, power) in monomial {
            let factor = match a == atom {
                true => value.clone(),
                false => field::atom(a),
            };
            for _ in 0..*power {
                part = part.times(&factor);
            }
        }
        out = out.plus(&part);
    }
    out
}

/// The multiple of (√p)² − p for each prime p that the difference is the
/// sum of, as `elab::real`'s `identity` finds them: a part holding √p to
/// the power 2 or more is that power less 2 times (√p)² − p, plus p times
/// it. None where what is left is not 0.
fn root_multiples(
    mut rest: Poly,
    primes: &IndexMap<Rpn, u64>,
) -> Option<IndexMap<u64, Poly>> {
    let mut by: IndexMap<u64, Poly> = IndexMap::new();
    loop {
        let found = rest.terms.iter().find_map(|(monomial, weight)| {
            monomial.iter().find_map(|(atom, power)| {
                let p = primes.get(atom)?;
                (*power >= 2)
                    .then(|| (monomial.clone(), weight.clone(), atom.clone(), *p))
            })
        });
        let Some((monomial, weight, atom, p)) = found else {
            break;
        };
        rest.terms.shift_remove(&monomial);
        let lowered: Monomial = monomial
            .iter()
            .filter_map(|(a, power)| match (*a == atom, power) {
                (true, 2) => None,
                (true, k) => Some((a.clone(), k - 2)),
                (false, k) => Some((a.clone(), *k)),
            })
            .collect();
        let one = Poly::new(IndexMap::from([(lowered, weight)]));
        let entry = by.entry(p).or_default();
        *entry = entry.plus(&one);
        rest = rest.plus(&one.scaled(&field::q(p as i64)));
    }
    rest.zero().then_some(by)
}

/// An atom as a Lean term.
fn base_term(base: Base) -> Printed {
    let numeral = |p: u64| Printed::cast(whole(p, Num::Real), real());
    match base {
        Base::Root(p) => root_of_prime(p),
        Base::Log(p) => {
            Printed::applied("Real.log", Source::Mathlib, vec![numeral(p)], real())
        }
        Base::Pi => Printed::applied("Real.pi", Source::Mathlib, Vec::new(), real()),
        Base::E => Printed::applied(
            "Real.exp",
            Source::Mathlib,
            vec![whole(1, Num::Real)],
            real(),
        ),
    }
}

/// √p₁·(√p₂·(…)), nested from the right as `Real.sqrt_mul` leaves it.
fn roots_product(primes: &[u64]) -> Option<Printed> {
    let (last, rest) = primes.split_last()?;
    Some(rest.iter().rev().fold(root_of_prime(*last), |acc, p| {
        Printed::infix(Op::TIMES, root_of_prime(*p), acc, real())
    }))
}

/// p₁·(p₂·(…)), the primes left under a root, nested from the right.
fn primes_product(primes: &[u64]) -> Option<Printed> {
    let (last, rest) = primes.split_last()?;
    Some(rest.iter().rev().fold(whole(*last, Num::Real), |acc, p| {
        Printed::infix(Op::TIMES, whole(*p, Num::Real), acc, real())
    }))
}

/// `Real.sqrt (p : ℝ)`.
fn root_of_prime(p: u64) -> Printed {
    Printed::applied(
        "Real.sqrt",
        Source::Mathlib,
        vec![Printed::cast(whole(p, Num::Real), real())],
        real(),
    )
}

/// A whole number of type `at`.
fn whole(n: u64, at: Num) -> Printed {
    Printed::numeral(n.to_string(), LeanType::Num(at))
}

/// `((n : ℕ) : ℝ)`, a natural number cast, as `Real.log_pow` and
/// `Real.exp_nat_mul` write their exponent.
fn natural(n: u32) -> Printed {
    Printed::cast(
        Printed::cast(whole(u64::from(n), Num::Nat), LeanType::Num(Num::Nat)),
        real(),
    )
}

/// A rational as Lean writes it in ℝ.
fn rational(q: &Q) -> Printed {
    let magnitude =
        coefficient_term(&q.abs(), Num::Real).unwrap_or_else(|| whole(1, Num::Real));
    match q.is_negative() {
        true => Printed::of(TermKind::Neg(Box::new(magnitude)), real()),
        false => magnitude,
    }
}

fn real() -> LeanType {
    LeanType::Num(Num::Real)
}

/// The term stated in ℝ, which numerals alone do not fix.
fn typed(x: Printed) -> Printed {
    match &x.kind {
        TermKind::Cast { .. } => x,
        _ => Printed::cast(x, real()),
    }
}

fn eq(a: Printed, b: Printed) -> Printed {
    Printed::infix(Op::EQUALS, a, b, LeanType::Prop)
}

fn unequal(a: Printed, b: Printed) -> Printed {
    Printed::infix(Op::of("≠").expect("≠ is an operator"), a, b, LeanType::Prop)
}

/// A Mathlib lemma applied to its arguments.
fn lemma(name: &str, args: Vec<Printed>) -> Printed {
    match args.is_empty() {
        true => t::lemma(name),
        false => Printed::applied(name, Source::Mathlib, args, LeanType::Prop),
    }
}

/// `congrArg f h`: an equation carried under a function.
fn congr(function: &str, h: Printed) -> Printed {
    Printed::applied(
        "congrArg",
        Source::Core,
        vec![t::lemma(function), h],
        LeanType::Prop,
    )
}

/// `show (x : ℝ) ≠ 0 by norm_num`.
fn nonzero_numeral(x: Printed) -> Printed {
    show(
        unequal(typed(x), whole(0, Num::Real)),
        t::call("norm_num", vec![]),
    )
}

/// `show (0 : ℝ) ≤ x by norm_num`.
fn at_least_zero(x: Printed) -> Printed {
    at_least_zero_by(x, "norm_num")
}

/// `show (0 : ℝ) ≤ x by tactic`.
fn at_least_zero_by(x: Printed, tactic: &'static str) -> Printed {
    let zero = Printed::cast(whole(0, Num::Real), real());
    show(
        Printed::infix(Op::AT_MOST, zero, x, LeanType::Prop),
        t::call(tactic, vec![]),
    )
}

/// `show says by tactic`, bracketed.
fn show(says: Printed, tactic: Tactic) -> Printed {
    t::bracket(Printed {
        kind: TermKind::Show {
            says: Box::new(says),
            proof: Box::new(t::by_term(Proof::By(tactic))),
        },
        ty: None,
    })
}

/// A term bracketed unless it binds at least as tightly as `need`.
fn at_least(term: Printed, need: u32) -> Printed {
    match term.prec() < need {
        true => t::bracket(term),
        false => term,
    }
}
