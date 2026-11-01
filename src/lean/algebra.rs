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
//! `field_simp`'s and then `ring`'s where it divides.

use indexmap::IndexMap;
use num_traits::{One, Signed};

use super::expr::{Printed, Writer};
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

/// The Lean proof of an `algebra` claim from the equations cited.
pub fn algebra(
    writer: &Writer,
    targets: &Targets,
    claim: &Node,
    cited: &[Cited],
) -> Route<String> {
    let labels = FloatLabels::new(IndexMap::new());
    let claimed = term_of_node(claim, targets);
    let divides = !constant(&denominators(&claimed, &labels));
    let writes_division = claim
        .walk()
        .iter()
        .any(|n| n.spelling() == crate::notations::DIVIDED);
    if cited.is_empty() {
        let divides = divides || writes_division;
        return Route::Built(if divides {
            "by parley_ring".to_string()
        } else {
            "by ring".to_string()
        });
    }
    let Some(want) = field::equation(&claimed, &labels) else {
        return Route::no("algebra whose claim is no equation");
    };
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
    if given.is_empty() {
        return Route::no("algebra citing no equation");
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
    let at = match carrier_of(writer, claim) {
        Route::Built(n) => n,
        Route::Declined(d) => return Route::Declined(d),
    };
    // The decision combines each equation with its denominators multiplied
    // out, and the claim with its own, less what its reading divided out.
    // As written, the claim's difference of sides is then the sum of each
    // cited equation's difference of sides times its multiplier, times what
    // the claim's reading divided out and the equation's own denominators,
    // over the claim's denominators and what the equation's reading divided
    // out.
    let mut parts = Vec::new();
    for t in &how {
        let over = t.multiplier().times(&taken).times(&own_under[t.which]);
        let under = claim_under.times(&own_taken[t.which]);
        let multiplier = match ratio_text(writer, &over, &under, &atoms, at) {
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
    Route::Built(if divided {
        format!("by linear_combination (norm := parley_field) {sum}")
    } else {
        format!("by linear_combination {sum}")
    })
}

/// `over / under` as a Lean term of type `at`: a polynomial where `under`
/// divides `over` exactly, a quotient otherwise.
fn ratio_text(
    writer: &Writer,
    over: &Poly,
    under: &Poly,
    atoms: &IndexMap<Rpn, Node>,
    at: Num,
) -> Route<String> {
    if let Some(whole) = field::exactly(over, under) {
        return poly_text(writer, &whole, atoms, at);
    }
    let top = match poly_text(writer, over, atoms, at) {
        Route::Built(t) => t,
        Route::Declined(d) => return Route::Declined(d),
    };
    let bottom = match poly_text(writer, under, atoms, at) {
        Route::Built(t) => t,
        Route::Declined(d) => return Route::Declined(d),
    };
    Route::Built(format!("({top}) / ({bottom})"))
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
