//! `algebra` in Lean: the claim as a combination of the lines it cites, by
//! the multipliers the method's decision finds.
//!
//! The decision reads each equation as a polynomial over its atoms
//! (`methods::field`), the claim's and each cited line's denominators
//! multiplied out, and finds what each cited equation is multiplied by so
//! that they add up to the claim (`methods::algebra::combination`). Lean's
//! `linear_combination` checks exactly that, by `ring1`. Where a
//! denominator is not a number, `field` clears it first, from a fact for
//! each part it divides by, written as `field` writes that part
//! (`FieldOrder`) and proved from the line the checker found
//! (`CheckedTheorem::divided_by`). With no line cited the claim is an
//! identity: `ring1`'s, or `field`'s where it divides.

use indexmap::IndexMap;
use num_traits::{One, Signed};

use super::doc::forms::casts_dropped;
use super::doc::{Arg, LeanType, Location, Op, Proof, Tactic, TacticArg, TermKind};
use super::expr::{Printed, Writer};
use super::tactics as t;
use super::templates::Num;
use crate::formula::Node;
use crate::methods::algebra::{combination, denominators, readings};
use crate::methods::field::{self, Poly, Q};
use crate::methods::terms::{term_of_node, Targets};
use crate::mm::kernel::FloatLabels;
use crate::mm::Rpn;
use crate::outcome::Route;

/// A cited line's equation: its tree, and the Lean term that proves it,
/// `s3` or a part of a line, `H2.1`.
#[derive(Clone)]
pub struct Cited {
    pub node: Node,
    /// The line's proof: its name, a part of it, `H3.1`, or the line
    /// read at a letter, `(h n hK1)`.
    pub proof: Printed,
    /// What the line says in Lean, as its `have` or hypothesis states it,
    /// where it is a line of the proof's; None where it is to be written
    /// from `node`.
    pub says: Option<Printed>,
}

/// A part a step divides by, and how Lean is shown it is not zero, as the
/// checker found it (`CheckedTheorem::divided_by`).
pub struct NotZero {
    pub term: Node,
    pub by: NotZeroBy,
}

/// How Lean is shown a part a step divides by is not zero.
pub enum NotZeroBy {
    /// A line in scope, its proof turned to say `d ≠ 0`, `h.ne'` of `0 <
    /// d`, and `stated` the type the line states it in where it is a
    /// narrower type than the step's, which `exact_mod_cast` takes across.
    Line { proof: Printed, stated: Option<Num> },
    /// A positive integer by what the page says once, which `positivity`
    /// shows from the facts `0 < n` in scope and a factorial's sign.
    Positive,
}

/// The parts of a goal in the order `field` numbers them. It reads the goal
/// from the left, through products, quotients, powers to a numeral,
/// negations and sums, and numbers each part it takes whole (a letter, a
/// numeral other than 1, a function's value, a power to a letter) where it
/// first meets it, and each sum after its own parts. It writes a product
/// back with its factors in that order, `n * 9 - 3` where the goal names
/// `n` before `9`, and looks for the fact that a divisor is not 0 written
/// exactly so (Mathlib's `FieldSimp.normalize` and `qNF.evalPretty`).
struct FieldOrder {
    /// Each part, its casts taken off, in the order first met.
    parts: Vec<Printed>,
}

impl FieldOrder {
    /// The order of the parts of an equation's two sides, the goal `field`
    /// reads, left side first (Mathlib's `reduceEqQ`).
    fn of(sides: &[Printed]) -> FieldOrder {
        let mut order = FieldOrder { parts: Vec::new() };
        for side in sides {
            order.read(side);
        }
        order
    }

    fn read(&mut self, term: &Printed) {
        match &term.kind {
            TermKind::Paren(x) | TermKind::Cast { inner: x, .. } | TermKind::Neg(x) => {
                self.read(x)
            }
            TermKind::Infix { op, lhs, rhs }
                if *op == Op::TIMES || *op == Op::DIVIDE =>
            {
                self.read(lhs);
                self.read(rhs);
            }
            TermKind::Infix { op, lhs, rhs }
                if *op == Op::POWER && numeral_power(rhs) =>
            {
                self.read(lhs)
            }
            TermKind::Infix { op, lhs, rhs } if *op == Op::PLUS || *op == Op::MINUS => {
                self.read(lhs);
                self.read(rhs);
                self.name(term);
            }
            TermKind::Numeral(n) if n == "1" => {}
            _ => self.name(term),
        }
    }

    fn name(&mut self, term: &Printed) {
        let part = casts_dropped(term);
        if !self.parts.contains(&part) {
            self.parts.push(part);
        }
    }

    /// Where a factor's part was first met: a power's base's place. A
    /// factor the goal never names comes after those it does.
    fn place(&self, factor: &Printed) -> usize {
        let base = match &bare_term(factor).kind {
            TermKind::Infix { op, lhs, rhs }
                if *op == Op::POWER && numeral_power(rhs) =>
            {
                lhs
            }
            _ => factor,
        };
        let part = casts_dropped(base);
        self.parts
            .iter()
            .position(|p| *p == part)
            .unwrap_or(usize::MAX)
    }

    /// The term as `field` writes it back: each product's factors in the
    /// order their parts were met, inside the sums, quotients and powers
    /// it reads through; a part it takes whole as it stands.
    fn written(&self, term: &Printed) -> Printed {
        match &term.kind {
            TermKind::Infix { op, .. } if *op == Op::TIMES => {
                let mut factors = Vec::new();
                factors_of(term, &mut factors);
                let mut placed: Vec<(usize, Printed)> = factors
                    .into_iter()
                    .map(|f| (self.place(f), self.written(f)))
                    .collect();
                placed.sort_by_key(|(place, _)| *place);
                let ty = term.ty.clone().unwrap_or(LeanType::Prop);
                placed
                    .into_iter()
                    .map(|(_, f)| f)
                    .reduce(|l, r| Printed::infix(Op::TIMES, l, r, ty.clone()))
                    .unwrap_or_else(|| term.clone())
            }
            TermKind::Infix { op, rhs, .. }
                if [Op::DIVIDE, Op::PLUS, Op::MINUS].contains(op)
                    || (*op == Op::POWER && numeral_power(rhs)) =>
            {
                self.rebuilt(term)
            }
            TermKind::Paren(_) | TermKind::Cast { .. } | TermKind::Neg(_) => {
                self.rebuilt(term)
            }
            _ => term.clone(),
        }
    }

    /// The term with each child written back.
    fn rebuilt(&self, term: &Printed) -> Printed {
        let mut out = term.clone();
        for c in out.children_mut() {
            *c = self.written(c);
        }
        out
    }
}

/// The factors of a product, through the brackets and ascriptions that
/// Lean does not keep.
fn factors_of<'a>(term: &'a Printed, out: &mut Vec<&'a Printed>) {
    match &bare_term(term).kind {
        TermKind::Infix { op, lhs, rhs } if *op == Op::TIMES => {
            factors_of(lhs, out);
            factors_of(rhs, out);
        }
        _ => out.push(term),
    }
}

/// The term inside the brackets the writer kept.
fn bare_term(term: &Printed) -> &Printed {
    match &term.kind {
        TermKind::Paren(inner) => bare_term(inner),
        _ => term,
    }
}

/// Whether an exponent is a numeral other than 0, which `field` reads
/// through to the base.
fn numeral_power(exponent: &Printed) -> bool {
    match &casts_dropped(exponent).kind {
        TermKind::Numeral(n) => n != "0",
        _ => false,
    }
}

/// The sides of the goal `field` reads after `linear_combination e`
/// (Mathlib's `eq_of_eq`, then `eq_rearrange`): `a + e.rhs - (b + e.lhs)`
/// and 0, for the claim `a = b`.
fn combined_goal(claim: [Printed; 2], combination: [Printed; 2]) -> [Printed; 2] {
    let [a, b] = claim;
    let [e_lhs, e_rhs] = combination;
    let ty = a.ty.clone().unwrap_or(LeanType::Prop);
    let zero = Printed::numeral("0", ty.clone());
    let left = Printed::infix(
        Op::MINUS,
        Printed::infix(Op::PLUS, a, e_rhs, ty.clone()),
        Printed::infix(Op::PLUS, b, e_lhs, ty.clone()),
        ty,
    );
    [left, zero]
}

/// An equation's two sides as Lean terms of type `at`: the claim's or a
/// cited line's, with the defines the step writes out put in, as the goal
/// `field` reads has them.
fn sides_at(writer: &Writer, equation: &Node, at: Num) -> Route<[Printed; 2]> {
    let [l, r] = equation.children.as_slice() else {
        return Route::no("an equation without two sides");
    };
    match (writer.number(l, at), writer.number(r, at)) {
        (Route::Built(l), Route::Built(r)) => Route::Built([l, r]),
        (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
    }
}

/// A part `field` clears by, with how it is shown not 0.
struct NonzeroPart {
    term: Node,
    proof: PartProof,
}

/// How a part is shown not 0.
enum PartProof {
    /// A proof that the part as the page writes it is not 0.
    Page(Printed),
    /// A tactic that shows it of the part in any order of its factors.
    Tactic(Tactic),
}

/// Each part the step divides by with its proof of not 0, in a step worked
/// in `at`: a line's fact taken apart into the parts `field` clears by
/// (`nonzero_parts`).
fn nonzero_part_list(divisors: &[NotZero], at: Num) -> Vec<NonzeroPart> {
    let mut parts: Vec<NonzeroPart> = Vec::new();
    for d in divisors {
        match &d.by {
            NotZeroBy::Line { proof, stated } => {
                let proof = match stated.is_some_and(|s| s < at) {
                    true => by_tactic(t::exact_mod_cast(proof.clone())),
                    false => proof.clone(),
                };
                nonzero_parts(&d.term, proof, &mut parts);
            }
            // `positivity` reads no order in ℂ: the cast is taken off
            // first, and the integer shown not 0.
            NotZeroBy::Positive if at == Num::Complex => parts.push(NonzeroPart {
                term: d.term.clone(),
                proof: PartProof::Tactic(Tactic::Seq(vec![
                    t::call("norm_cast", vec![]),
                    t::call("positivity", vec![]),
                ])),
            }),
            NotZeroBy::Positive => parts.push(NonzeroPart {
                term: d.term.clone(),
                proof: PartProof::Tactic(t::call("positivity", vec![])),
            }),
        }
    }
    parts
}

/// `have hz1 : d ≠ 0 := …` for each part the step divides by, `d` written
/// in the type the step works in, `at`, as `field` writes it back from the
/// goal, `order`, so that it finds it.
fn nonzero_haves(
    writer: &Writer,
    parts: Vec<NonzeroPart>,
    at: Num,
    order: &FieldOrder,
) -> Route<Vec<Tactic>> {
    let ty = LeanType::Num(at);
    let mut out = Vec::new();
    for (k, part) in parts.into_iter().enumerate() {
        let page = match writer.number_fixed(&part.term, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let term = order.written(&page);
        // A proof of the part as the page writes it is turned to the order
        // `field` writes its factors in, where that differs, by `ring`.
        let proof = match part.proof {
            PartProof::Tactic(tactic) => by_tactic(tactic),
            PartProof::Page(proof) if term == page => proof,
            PartProof::Page(proof) => by_tactic(Tactic::Seq(vec![
                t::call("rw", vec![t::rules(vec![reordered(term.clone(), page)])]),
                Tactic::Exact(proof),
            ])),
        };
        let says = Printed::infix(
            Op::of("≠").expect("≠ is an operator"),
            term,
            Printed::numeral("0", ty.clone()),
            LeanType::Prop,
        );
        out.push(Tactic::Have {
            name: format!("hz{}", k + 1),
            says,
            proof: Box::new(Proof::Term(proof)),
        });
    }
    Route::Built(out)
}

/// `show a = b by ring`: a term the same as another but for the order of
/// its factors.
fn reordered(term: Printed, page: Printed) -> Printed {
    Printed {
        kind: TermKind::Show {
            says: Box::new(Printed::infix(Op::EQUALS, term, page, LeanType::Prop)),
            proof: Box::new(t::by_term(Proof::By(t::call("ring", vec![])))),
        },
        ty: None,
    }
}

/// A tactic proof as a term, bracketed, `(by positivity)`, so that the
/// tactics after a `have` on its line are not read as part of its proof.
fn by_tactic(tactic: Tactic) -> Printed {
    t::bracket(t::by_term(Proof::By(tactic)))
}

/// The parts a fact `proof : d ≠ 0` says are not 0, each with its proof:
/// the parts `field_simp` meets. Of a product each factor
/// (`left_ne_zero_of_mul`, `right_ne_zero_of_mul`), of a quotient each side
/// (`div_ne_zero_iff`), of a negation its term (`neg_ne_zero`), of a power
/// to a numeral its base (`pow_ne_zero_iff`); numerals left out, which
/// `field_simp` works out; any other term whole.
fn nonzero_parts(term: &Node, proof: Printed, out: &mut Vec<NonzeroPart>) {
    use super::doc::Source;
    use crate::notations::{
        DIVIDED, JUXTAPOSITION, MULTIPLICATIVE, NUMERAL, POWER, SUPERSCRIPT,
        UNARY_MINUS,
    };
    let apply = |name: &str, arg: Printed| {
        Printed::applied(name, Source::Mathlib, vec![arg], LeanType::Prop)
    };
    let field = |p: Printed, f: &str| Printed {
        kind: TermKind::Field {
            inner: Box::new(t::bracket(p)),
            field: f.to_string(),
        },
        ty: None,
    };
    if numeral_arithmetic(term) {
        return;
    }
    match (term.notation(), term.spelling(), term.children.as_slice()) {
        (MULTIPLICATIVE | JUXTAPOSITION, _, [a, b]) => {
            nonzero_parts(a, apply("left_ne_zero_of_mul", proof.clone()), out);
            nonzero_parts(b, apply("right_ne_zero_of_mul", proof), out);
        }
        (_, DIVIDED, [a, b]) => {
            let both = apply("div_ne_zero_iff.mp", proof);
            nonzero_parts(a, field(both.clone(), "1"), out);
            nonzero_parts(b, field(both, "2"), out);
        }
        (UNARY_MINUS, _, [a]) => nonzero_parts(a, apply("neg_ne_zero.mp", proof), out),
        (POWER | SUPERSCRIPT, _, [a, e]) if e.notation() == NUMERAL => {
            let iff = apply("pow_ne_zero_iff", by_tactic(t::call("norm_num", vec![])));
            let base = Printed::of(
                TermKind::App {
                    head: Box::new(field(iff, "mp")),
                    args: vec![Arg::Explicit(proof)],
                    explicit: false,
                },
                LeanType::Prop,
            );
            nonzero_parts(a, base, out);
        }
        _ => out.push(NonzeroPart {
            term: term.clone(),
            proof: PartProof::Page(proof),
        }),
    }
}

/// The equation a `≠` says is false, `s − 1 = 0` of `s − 1 ≠ 0`.
fn denied(node: &Node) -> Option<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (crate::notations::LOGICAL_NOT, [inner])
            if inner.notation() == crate::notations::EQUALITY =>
        {
            Some(inner)
        }
        _ => None,
    }
}

/// A `≠` claim from a cited `≠` line, s − 1 ≠ 0 from s ≠ 1: the claim's
/// equation supposed, the cited line's follows from it by the same
/// decision, which the cited line denies. None where the claim is no `≠`
/// or no cited line is one.
fn unequal(
    writer: &Writer,
    targets: &Targets,
    claim: &Node,
    cited: &[Cited],
    inside_terms: bool,
) -> Option<Route<Proof>> {
    let supposed = denied(claim)?;
    let mut declined = None;
    for c in cited {
        let Some(wanted) = denied(&c.node) else {
            continue;
        };
        let given = Cited {
            node: supposed.clone(),
            proof: t::hyp("h"),
            says: None,
        };
        match algebra(
            writer,
            targets,
            wanted,
            std::slice::from_ref(&given),
            inside_terms,
            &[],
            None,
        ) {
            Route::Built(inner) => {
                let refuted = Printed {
                    kind: TermKind::App {
                        head: Box::new(c.proof.clone()),
                        args: vec![Arg::Explicit(t::bracket(Printed {
                            kind: TermKind::By(Box::new(inner)),
                            ty: None,
                        }))],
                        explicit: false,
                    },
                    ty: None,
                };
                return Some(Route::Built(Proof::By(Tactic::Seq(vec![
                    Tactic::Intro(vec!["h".to_string()]),
                    Tactic::Exact(refuted),
                ]))));
            }
            Route::Declined(d) => declined = Some(Route::Declined(d)),
        }
    }
    declined
}

/// The Lean proof of an `algebra` claim from the equations cited.
/// `inside_terms` says the checker read two terms as one that differ inside
/// a function's argument or an exponent, F(0 + 1) and F(1), (d·1).toNat and
/// d.toNat: the check is then `ring_nf`, which normalises inside them, where
/// `ring1` takes each as its own atom. `divisors` are the parts the step
/// divides by, with how each is not 0 (`CheckedTheorem::divided_by`), and
/// `worked_in` the type a calculation the step is a row of is worked in,
/// which a row's claim may be narrower than.
pub fn algebra(
    writer: &Writer,
    targets: &Targets,
    claim: &Node,
    cited: &[Cited],
    inside_terms: bool,
    divisors: &[NotZero],
    worked_in: Option<Num>,
) -> Route<Proof> {
    if let Some(proof) = unequal(writer, targets, claim, cited, inside_terms) {
        return proof;
    }
    let labels = FloatLabels::new(IndexMap::new());
    let claimed = term_of_node(claim, targets);
    let divides = divides_by_term(claim);
    // What an identity that divides is told of its divisors, in the type
    // the step is stated in: the claim's own, or its calculation's.
    let own = match carrier_of(writer, claim) {
        Route::Built(n) => worked_in.map_or(n, |w| w.max(n)),
        Route::Declined(d) => return Route::Declined(d),
    };
    let identity_haves = match divides {
        true => {
            let order = match sides_at(writer, claim, own) {
                Route::Built(sides) => FieldOrder::of(&sides),
                Route::Declined(d) => return Route::Declined(d),
            };
            match nonzero_haves(writer, nonzero_part_list(divisors, own), own, &order) {
                Route::Built(h) => h,
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        false => Vec::new(),
    };
    // An identity, `ring1`, where it divides by no term but a number, or
    // `ring_nf` where the check normalises inside terms. Where the step
    // reads its sums as linear (`field::says_something_linear`) and the
    // claim joins a sum to a factor or to another sum, each side is
    // gathered into one sum over the range, the factors free of the letter
    // taken inside, and the summands compared index by index.
    let linear = crate::methods::field::says_something_linear(&claimed, &labels)
        && sums_joined(claim);
    let identity = || match (divides, linear) {
        (true, _) => {
            let mut steps = identity_haves.clone();
            steps.push(cleared());
            Tactic::Seq(steps)
        }
        (false, true) => Tactic::Seq(vec![
            t::simp_only(
                false,
                None,
                vec![
                    t::forwards(t::lemma("Finset.mul_sum")),
                    t::forwards(t::lemma("Finset.sum_mul")),
                    t::backwards(t::lemma("Finset.sum_add_distrib")),
                    t::backwards(t::lemma("Finset.sum_sub_distrib")),
                ],
                None,
            ),
            t::call(
                "apply",
                vec![TacticArg::Term(t::lemma("Finset.sum_congr rfl"))],
            ),
            t::call("intros", vec![]),
            t::call("ring1", vec![]),
        ]),
        (false, false) if inside_terms => t::call("ring_nf", vec![]),
        (false, false) => t::call("ring1", vec![]),
    };
    if cited.is_empty() {
        return Route::Built(Proof::By(identity()));
    }
    let Some(want) = field::equation(&claimed, &labels) else {
        return Route::no("algebra whose claim is no equation");
    };
    let mut given = Vec::new();
    let mut unders = Vec::new();
    let mut proofs = Vec::new();
    // The cited lines `given` reads, in its order.
    let mut equations: Vec<&Cited> = Vec::new();
    // Each cited equation's own denominators, and what its reading divided
    // out of it.
    let mut own_under = Vec::new();
    let mut own_taken = Vec::new();
    let mut atoms: IndexMap<Rpn, Node> = IndexMap::new();
    collect_atoms(claim, targets, &labels, &mut atoms);
    let mut divided = divides;
    for c in cited {
        let term = term_of_node(&c.node, targets);
        let Some(one) = field::equation(&term, &labels) else {
            continue;
        };
        collect_atoms(&c.node, targets, &labels, &mut atoms);
        let read = crate::methods::algebra::claim_says(&term, one, &labels);
        let under = denominators(&term, &labels);
        divided |= divides_by_term(&c.node);
        unders.push(field::exactly(&under, &read.taken));
        own_under.push(under);
        own_taken.push(read.taken.clone());
        given.push(read.says);
        proofs.push(c.proof.clone());
        equations.push(c);
    }
    // Lines cited for what they say of a divisor, and no equation: the claim
    // is an identity, cleared of its divisions by what those lines say of
    // each divisor (`divisors`).
    if given.is_empty() {
        return Route::Built(Proof::By(identity()));
    }
    let claim_under = denominators(&claimed, &labels);
    let found = readings(&claimed, want, &labels)
        .into_iter()
        .find_map(|says| {
            combination(&given, &unders, &says, &claim_under)
                .map(|how| (says.taken, how))
        });
    let Some((taken, how)) = found else {
        return Route::no("no sum of the cited equations is the claim");
    };
    // The multipliers are written in the type the step works in: the
    // claim's, or a cited line's where it is wider, as of a closed claim.
    let mut at = own;
    for c in cited {
        if c.node.notation() == crate::notations::EQUALITY {
            if let Route::Built(n) = carrier_of(writer, &c.node) {
                at = at.max(n);
            }
        }
    }
    // The decision combines each equation with its denominators multiplied
    // out, and the claim with its own, less what its reading divided out.
    // As written, the claim's difference of sides is then the sum of each
    // cited equation's difference of sides times its multiplier, times what
    // the claim's reading divided out and the equation's own denominators,
    // over the claim's denominators and what the equation's reading divided
    // out.
    // The claim's denominators side by side, kept apart, so that each is
    // one a requires line says is not 0.
    let sides: Vec<Poly> = claimed
        .children()
        .iter()
        .map(|side| field::read(side, &labels).under)
        .collect();
    // A combination in ℤ that takes half of an equation is one in ℚ. So is
    // one whose cited lines are wider than its claim: the step is moved to
    // their type by `qify` or `rify`, which casts every line alike.
    let fractional = how
        .iter()
        .any(|t| t.multiplier().terms.values().any(|c| !c.is_integer()));
    if at == Num::Int && fractional {
        at = Num::Rat;
    }
    // A claim of numerals alone is written in its cited lines' type, so
    // only one whose parts fix its type is moved.
    let pinned = claim.children.iter().any(|side| writer.pinned(side));
    let moved = match (pinned && own < at, at) {
        (true, Num::Rat) => Some("qify"),
        (true, Num::Real) => Some("rify"),
        _ => None,
    };
    let ty = LeanType::Num(at);
    let one = Printed::numeral("1", ty.clone());
    // The parts the step divides by that a fact says are not 0.
    let parts = nonzero_part_list(divisors, at);
    // The page's divisors, each beside its polynomial: what the claim and
    // the cited lines divide by, the terms the record names, and the parts
    // of them that a fact says are not 0.
    let mut written: Vec<(Poly, Node)> = Vec::new();
    let page_divisors = std::iter::once(claim)
        .chain(cited.iter().map(|c| &c.node))
        .flat_map(|n| n.walk())
        .filter(|n| n.spelling() == crate::notations::DIVIDED)
        .filter_map(|n| n.children.get(1).cloned())
        .chain(divisors.iter().map(|d| d.term.clone()))
        .chain(parts.iter().map(|p| p.term.clone()));
    for d in page_divisors {
        let read = field::read(&term_of_node(&d, targets), &labels);
        let whole = read.under.constant_value().is_some_and(|c| c.is_one());
        if whole && !written.iter().any(|(p, _)| *p == read.over) {
            written.push((read.over, d));
        }
    }
    let mut sum: Option<Printed> = None;
    // The combination's two sides, each cited line's side times its
    // multiplier, summed: what `field` reads after the claim's sides.
    let mut combined: Option<[Printed; 2]> = None;
    for how_one in &how {
        let over = how_one
            .multiplier()
            .times(&taken)
            .times(&own_under[how_one.which]);
        let mut under: Vec<Poly> = sides.clone();
        under.push(own_taken[how_one.which].clone());
        let multiplier = match ratio_term(writer, over, under, &atoms, at, &written) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let proof = proofs[how_one.which].clone();
        if divided {
            let sides = match sides_at(writer, &equations[how_one.which].node, at) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            let scaled = sides.map(|side| match multiplier == one {
                true => side,
                false => Printed::infix(
                    Op::TIMES,
                    t::bracket(multiplier.clone()),
                    side,
                    ty.clone(),
                ),
            });
            combined = Some(match combined {
                None => scaled,
                Some([l, r]) => {
                    let [sl, sr] = scaled;
                    [
                        Printed::infix(Op::PLUS, l, sl, ty.clone()),
                        Printed::infix(Op::PLUS, r, sr, ty.clone()),
                    ]
                }
            });
        }
        let part = match multiplier == one {
            true => proof,
            false => {
                Printed::infix(Op::TIMES, t::bracket(multiplier), proof, ty.clone())
            }
        };
        sum = Some(match sum {
            None => part,
            Some(s) => Printed::infix(Op::PLUS, s, part, ty.clone()),
        });
    }
    let sum = sum.unwrap_or_else(|| Printed::numeral("0", ty));
    // The step moved to its cited lines' type first, where it is, and then
    // checked by the field's normal form where it divides.
    let mut steps: Vec<Tactic> = moved
        .map(|c| t::call(c, vec![TacticArg::At(vec![Location::Everywhere])]))
        .into_iter()
        .collect();
    if divided {
        let claim_sides = match sides_at(writer, claim, at) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let goal = match combined {
            Some(c) => combined_goal(claim_sides, c),
            None => claim_sides,
        };
        match nonzero_haves(writer, parts, at, &FieldOrder::of(&goal)) {
            Route::Built(h) => steps.extend(h),
            Route::Declined(d) => return Route::Declined(d),
        }
    }
    steps.push(match divided {
        true => t::call(
            "linear_combination",
            vec![
                TacticArg::Setting {
                    key: "norm",
                    value: Box::new(Tactic::Group(Box::new(cleared()))),
                },
                TacticArg::Term(sum),
            ],
        ),
        false if inside_terms => t::call(
            "linear_combination",
            vec![
                TacticArg::Setting {
                    key: "norm",
                    value: Box::new(t::call("ring_nf", vec![])),
                },
                TacticArg::Term(sum),
            ],
        ),
        false => t::linear_combination(sum),
    });
    Route::Built(Proof::By(Tactic::Seq(steps)))
}

/// `over` divided by the product of `under`, as a Lean term of type `at`:
/// each factor of `under` that divides `over` exactly divided out, and the
/// rest written as a product of the factors, each of which a line says is
/// not 0, rather than multiplied out, which `field_simp` could not see is
/// not 0.
/// A factor below that is one of the page's divisors, `written`, as a
/// polynomial, is written as the page writes it, `3n − 1` and not `−1 +
/// n·3`, so that it meets the line saying it is not 0 as written.
fn ratio_term(
    writer: &Writer,
    mut over: Poly,
    under: Vec<Poly>,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
    written: &[(Poly, Node)],
) -> Route<Printed> {
    let mut kept = Vec::new();
    for factor in split_by_written(under, written) {
        if constant(&factor) {
            match factor.constant_value() {
                Some(c) if !c.is_one() => kept.push(factor),
                _ => {}
            }
            continue;
        }
        match field::exactly(&over, &factor) {
            Some(rest) => over = rest,
            None => kept.push(factor),
        }
    }
    let top = match poly_term(writer, &over, atoms, at) {
        Route::Built(t) => t,
        Route::Declined(d) => return Route::Declined(d),
    };
    if kept.is_empty() {
        return Route::Built(top);
    }
    let ty = LeanType::Num(at);
    let mut bottom: Option<Printed> = None;
    for f in &kept {
        let factor = match written.iter().find(|(p, _)| p == f) {
            Some((_, page)) => writer.number_fixed(page, at),
            None => poly_term(writer, f, atoms, at),
        };
        let factor = match factor {
            Route::Built(t) => t::bracket(t),
            Route::Declined(d) => return Route::Declined(d),
        };
        bottom = Some(match bottom {
            None => factor,
            Some(b) => Printed::infix(Op::TIMES, b, factor, ty.clone()),
        });
    }
    let Some(bottom) = bottom else {
        return Route::Built(top);
    };
    Route::Built(Printed::infix(
        Op::DIVIDE,
        t::bracket(top),
        t::bracket(bottom),
        ty,
    ))
}

/// Each factor taken apart into the page's divisors it is a product of,
/// `4·T²·(−1 + i√3)·(−1 − i√3)` of `−4·i²·√3²·T² + 4·T²`, and what is
/// left: `field` finds a fact for each divisor the page writes, and none
/// for their product multiplied out.
fn split_by_written(under: Vec<Poly>, written: &[(Poly, Node)]) -> Vec<Poly> {
    let mut out = Vec::new();
    for mut factor in under {
        for (divisor, _) in written {
            if constant(divisor) {
                continue;
            }
            while !constant(&factor) {
                match field::exactly(&factor, divisor) {
                    Some(rest) => {
                        out.push(divisor.clone());
                        factor = rest;
                    }
                    None => break,
                }
            }
        }
        out.push(factor);
    }
    out
}

/// The type an equation is computed in.
fn carrier_of(writer: &Writer, claim: &Node) -> Route<Num> {
    let mut out = Num::Int;
    for side in &claim.children {
        match writer.carrier(side) {
            Route::Built(n) => out = out.max(n),
            Route::Declined(d) => return Route::Declined(d),
        }
    }
    Route::Built(out)
}

/// Whether a statement as the page writes it divides by a term other than
/// numerals and their arithmetic: by a letter, 1/(1/p) among them, which
/// the field reading takes whole, or by π or √2 − 1. Lean clears such a
/// division only knowing the term is not 0.
fn divides_by_term(node: &Node) -> bool {
    node.walk().iter().any(|n| {
        n.spelling() == crate::notations::DIVIDED
            && n.children.get(1).is_some_and(|d| !numeral_arithmetic(d))
    })
}

/// `field`: the divisions cleared, by the facts in scope that each divisor
/// is not 0, and what is left checked by `ring1`, Mathlib's finishing
/// tactic for an identity of a field.
fn cleared() -> Tactic {
    t::call("field", vec![])
}

/// Whether a statement as the page writes it multiplies a finite sum by a
/// factor, or adds one sum to another or takes one from another: what the
/// lemmas that gather sums into one (`Finset.mul_sum`,
/// `Finset.sum_add_distrib`) act on.
fn sums_joined(node: &Node) -> bool {
    use crate::notations::{JUXTAPOSITION, MINUS, MULTIPLICATIVE, PLUS, SUM};
    let sum = |n: &Node| n.notation() == SUM;
    node.walk().iter().any(|n| {
        let product = [JUXTAPOSITION, MULTIPLICATIVE].contains(&n.notation());
        let joined = [PLUS, MINUS].contains(&n.spelling());
        (product && n.children.iter().any(sum))
            || (joined && n.children.len() == 2 && n.children.iter().all(sum))
    })
}

/// Whether a term is numerals joined by +, −, ·, / and powers alone.
fn numeral_arithmetic(term: &Node) -> bool {
    use crate::notations::{
        DIVIDED, JUXTAPOSITION, MINUS, MULTIPLICATIVE, NUMERAL, PLUS, POWER,
        SUPERSCRIPT, UNARY_MINUS,
    };
    let arithmetic = term.notation() == NUMERAL
        || [
            JUXTAPOSITION,
            MULTIPLICATIVE,
            POWER,
            SUPERSCRIPT,
            UNARY_MINUS,
        ]
        .contains(&term.notation())
        || [PLUS, MINUS, DIVIDED].contains(&term.spelling());
    arithmetic && term.children.iter().all(numeral_arithmetic)
}

/// Whether a polynomial is a number.
fn constant(p: &Poly) -> bool {
    p.constant_value().is_some()
}

/// Every part of a tree by the atom the decision reads it as, so that an
/// atom of a multiplier is written as the page wrote it.
fn collect_atoms(
    node: &Node,
    targets: &Targets,
    labels: &FloatLabels,
    out: &mut IndexMap<Rpn, Node>,
) {
    for part in node.walk() {
        let rpn = term_of_node(&part, targets).rpn(labels);
        out.entry(rpn).or_insert(part);
    }
}

/// A polynomial as a Lean term of type `at`, each atom written as the page
/// wrote it.
fn poly_term(
    writer: &Writer,
    p: &Poly,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
) -> Route<Printed> {
    let ty = LeanType::Num(at);
    let mut terms: Vec<_> = p.terms.iter().collect();
    terms.sort_by_key(|(m, _)| field::order(m));
    let mut out: Option<Printed> = None;
    for (monomial, weight) in terms {
        let mut factors = Vec::new();
        for (atom, power) in monomial {
            let Some(node) = atoms.get(atom) else {
                return Route::no("a multiplier with a part the page does not write");
            };
            let printed: Printed = match writer.number(node, at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            factors.push(if *power == 1 {
                at_least(printed, 71)
            } else {
                let exponent =
                    Printed::numeral(power.to_string(), LeanType::Num(Num::Nat));
                Printed::infix(Op::POWER, at_least(printed, 76), exponent, ty.clone())
            });
        }
        let negative = weight.is_negative();
        let mut parts: Vec<Printed> =
            coefficient_term(&weight.abs(), at).into_iter().collect();
        parts.extend(factors);
        let body = parts
            .into_iter()
            .reduce(|l, r| Printed::infix(Op::TIMES, l, r, ty.clone()))
            .unwrap_or_else(|| Printed::numeral("1", ty.clone()));
        out = Some(match (out, negative) {
            (None, false) => body,
            (None, true) => Printed::of(TermKind::Neg(Box::new(body)), ty.clone()),
            (Some(sum), false) => Printed::infix(Op::PLUS, sum, body, ty.clone()),
            (Some(sum), true) => Printed::infix(Op::MINUS, sum, body, ty.clone()),
        });
    }
    Route::Built(out.unwrap_or_else(|| Printed::numeral("0", ty)))
}

/// A term bracketed unless it binds at least as tightly as `need`.
fn at_least(term: Printed, need: u32) -> Printed {
    match term.prec() < need {
        true => t::bracket(term),
        false => term,
    }
}

/// A positive rational coefficient as Lean writes it, `(1 / 2 : ℚ)` of a
/// fraction; None for 1.
pub(super) fn coefficient_term(q: &Q, at: Num) -> Option<Printed> {
    if q.is_one() {
        return None;
    }
    let whole = LeanType::Num(Num::Int);
    if q.is_integer() {
        return Some(Printed::numeral(
            q.to_integer().to_string(),
            LeanType::Num(at),
        ));
    }
    let fraction = Printed::infix(
        Op::DIVIDE,
        Printed::numeral(q.numer().to_string(), whole.clone()),
        Printed::numeral(q.denom().to_string(), whole),
        LeanType::Num(at),
    );
    Some(Printed::cast(fraction, LeanType::Num(at)))
}
