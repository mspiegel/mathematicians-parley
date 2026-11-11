//! `algebra` in Lean: the claim as a combination of the lines it cites, by
//! the multipliers the method's decision finds.
//!
//! The decision reads each equation as a polynomial over its atoms
//! (`methods::field`), the claim's and each cited line's denominators
//! multiplied out, and finds what each cited equation is multiplied by so
//! that they add up to the claim (`methods::algebra::combination`). Lean's
//! `linear_combination` checks exactly that, by `ring`. Where a denominator
//! is not a number, `field_simp` clears it first, from the lines that say
//! it is not 0. With no line cited the claim is an identity, `ring`'s, or
//! `field_simp`'s and then `ring`'s where it divides (`parley_ring`).

use indexmap::IndexMap;
use num_traits::{One, Signed};

use super::doc::bridges::BridgeTactic;
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
    /// read at a letter, `(h n (by parley_side))`.
    pub proof: Printed,
    /// What the line says in Lean, as its `have` or hypothesis states it,
    /// where it is a line of the proof's; None where it is to be written
    /// from `node`.
    pub says: Option<Printed>,
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
        match algebra(writer, targets, wanted, std::slice::from_ref(&given)) {
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
pub fn algebra(
    writer: &Writer,
    targets: &Targets,
    claim: &Node,
    cited: &[Cited],
) -> Route<Proof> {
    if let Some(proof) = unequal(writer, targets, claim, cited) {
        return proof;
    }
    let labels = FloatLabels::new(IndexMap::new());
    let claimed = term_of_node(claim, targets);
    if cited.is_empty() {
        return Route::Built(Proof::By(t::bridge(BridgeTactic::Ring, vec![])));
    }
    let Some(want) = field::equation(&claimed, &labels) else {
        return Route::no("algebra whose claim is no equation");
    };
    let divides = !constant(&denominators(&claimed, &labels));
    let mut given = Vec::new();
    let mut unders = Vec::new();
    let mut proofs = Vec::new();
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
        divided |= !constant(&under);
        unders.push(field::exactly(&under, &read.taken));
        own_under.push(under);
        own_taken.push(read.taken.clone());
        given.push(read.says);
        proofs.push(c.proof.clone());
    }
    // Lines cited for what they say of a divisor, and no equation: the claim
    // is an identity, cleared of its divisions by those lines. A line that
    // puts a letter of a wider type in ℕ, x ∈ ℕ of a real x, is unpacked
    // first, x the natural number it is, above 0, as set.mm's x ∈ ℕ gives
    // x ≠ 0.
    if given.is_empty() {
        let mut steps: Vec<Tactic> = cited
            .iter()
            .filter_map(|c| member_unpacked(writer, c))
            .collect();
        steps.push(t::bridge(BridgeTactic::Ring, vec![]));
        return Route::Built(Proof::By(Tactic::Seq(steps)));
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
    let own = match carrier_of(writer, claim) {
        Route::Built(n) => n,
        Route::Declined(d) => return Route::Declined(d),
    };
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
    let mut sum: Option<Printed> = None;
    for how_one in &how {
        let over = how_one
            .multiplier()
            .times(&taken)
            .times(&own_under[how_one.which]);
        let mut under: Vec<Poly> = sides.clone();
        under.push(own_taken[how_one.which].clone());
        let multiplier = match ratio_term(writer, over, under, &atoms, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let proof = proofs[how_one.which].clone();
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
    let norm = if divided {
        BridgeTactic::Field
    } else {
        BridgeTactic::Norm
    };
    let mut steps: Vec<Tactic> = moved
        .map(|c| t::call(c, vec![TacticArg::At(vec![Location::Everywhere])]))
        .into_iter()
        .collect();
    steps.push(t::call(
        "linear_combination",
        vec![
            TacticArg::Setting {
                key: "norm",
                value: Box::new(t::bridge(norm, vec![])),
            },
            TacticArg::Term(sum),
        ],
    ));
    Route::Built(Proof::By(Tactic::Seq(steps)))
}

/// `over` divided by the product of `under`, as a Lean term of type `at`:
/// each factor of `under` that divides `over` exactly divided out, and the
/// rest written as a product of the factors, each of which a line says is
/// not 0, rather than multiplied out, which `field_simp` could not see is
/// not 0.
/// `obtain` of a cited line that puts a letter of a wider type in ℕ, ℕ₀ or
/// ℤ, written `∃ m, …, (m : T) = x`: the letter becomes that number. None
/// for any other line.
fn member_unpacked(writer: &Writer, cited: &Cited) -> Option<Tactic> {
    let [x, set] = cited.node.children.as_slice() else {
        return None;
    };
    if cited.node.notation() != crate::notations::MEMBERSHIP || !x.is_name() {
        return None;
    }
    let system = super::expr::system_of(set)?;
    let own = writer.carrier(x).built()?;
    let pattern: &[&str] = match system {
        super::expr::System::Positive if own > Num::Int => &["_", "_", "rfl"],
        super::expr::System::NonNegative if own > Num::Int => &["_", "rfl"],
        super::expr::System::Type(Num::Int) if own > Num::Int => &["_", "rfl"],
        _ => return None,
    };
    Some(Tactic::Obtain {
        names: pattern.iter().map(|p| p.to_string()).collect(),
        says: None,
        from: cited.proof.clone(),
    })
}

fn ratio_term(
    writer: &Writer,
    mut over: Poly,
    under: Vec<Poly>,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
) -> Route<Printed> {
    let mut kept = Vec::new();
    for factor in under {
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
        let factor = match poly_term(writer, f, atoms, at) {
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
fn coefficient_term(q: &Q, at: Num) -> Option<Printed> {
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
