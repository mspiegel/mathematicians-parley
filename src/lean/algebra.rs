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
use super::doc::{Arg, Location, Proof, Tactic, TacticArg, TermKind};
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
pub struct Cited {
    pub node: Node,
    pub proof: String,
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
            proof: "h".to_string(),
        };
        match algebra(writer, targets, wanted, std::slice::from_ref(&given)) {
            Route::Built(inner) => {
                let refuted = Printed {
                    kind: TermKind::App {
                        head: Box::new(Printed::atom(c.proof.clone())),
                        args: vec![Arg::Explicit(t::bracket(Printed::atom(
                            inner.text(),
                        )))],
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
    let mut parts = Vec::new();
    for t in &how {
        let over = t.multiplier().times(&taken).times(&own_under[t.which]);
        let mut under: Vec<Poly> = sides.clone();
        under.push(own_taken[t.which].clone());
        let multiplier = match ratio_text(writer, over, under, &atoms, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let proof = &proofs[t.which];
        parts.push(if multiplier == "1" {
            proof.clone()
        } else {
            format!("({multiplier}) * {proof}")
        });
    }
    let sum = if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join(" + ")
    };
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
            TacticArg::Term(Printed::atom(sum)),
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
        from: Printed::atom(cited.proof.clone()),
    })
}

fn ratio_text(
    writer: &Writer,
    mut over: Poly,
    under: Vec<Poly>,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
) -> Route<String> {
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
    let top = match poly_text(writer, &over, atoms, at) {
        Route::Built(t) => t,
        Route::Declined(d) => return Route::Declined(d),
    };
    if kept.is_empty() {
        return Route::Built(top);
    }
    let mut bottom = Vec::new();
    for f in &kept {
        match poly_text(writer, f, atoms, at) {
            Route::Built(t) => bottom.push(format!("({t})")),
            Route::Declined(d) => return Route::Declined(d),
        }
    }
    Route::Built(format!("({top}) / ({})", bottom.join(" * ")))
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
fn poly_text(
    writer: &Writer,
    p: &Poly,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
) -> Route<String> {
    let mut terms: Vec<_> = p.terms.iter().collect();
    terms.sort_by_key(|(m, _)| field::order(m));
    let mut out = String::new();
    for (i, (monomial, weight)) in terms.into_iter().enumerate() {
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
                printed.at(71)
            } else {
                format!("{} ^ {power}", printed.at(76))
            });
        }
        let negative = weight.is_negative();
        let size = weight.abs();
        let coefficient = coefficient_text(&size, at);
        let body = match (coefficient, factors.is_empty()) {
            (None, true) => "1".to_string(),
            (None, false) => factors.join(" * "),
            (Some(c), true) => c,
            (Some(c), false) => format!("{c} * {}", factors.join(" * ")),
        };
        if i == 0 {
            if negative {
                out.push('-');
            }
            out.push_str(&body);
        } else {
            out.push_str(if negative { " - " } else { " + " });
            out.push_str(&body);
        }
    }
    if out.is_empty() {
        out.push('0');
    }
    Route::Built(out)
}

/// A positive rational coefficient as Lean writes it; None for 1.
fn coefficient_text(q: &Q, at: Num) -> Option<String> {
    if q.is_one() {
        return None;
    }
    if q.is_integer() {
        return Some(q.to_integer().to_string());
    }
    Some(format!("({} / {} : {})", q.numer(), q.denom(), at.lean()))
}
