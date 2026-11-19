//! Terms, orders and rational casts of Lean statements.

use super::*;

/// Lean's statement of a "for all" line once each of its leading letters is
/// given its value (`lean_instance`).
pub(super) struct LeanInstance {
    /// Each condition taken off, outermost first, at the values.
    pub(super) conditions: Vec<Printed>,
    /// What is left once they are.
    pub(super) left: Printed,
}

/// What Lean's statement of a "for all" line, `line`, says once each of its
/// leading letters is given its value of `given` in order, a guard's proof
/// after a value that has one, and then `conditions` of its conditions'
/// proofs: each letter put as its value wherever it stands, a cast of it a
/// cast of the value, `↑1` of `↑x` at x := 1, as Lean instantiates it.
/// Declined where the statement has fewer binders or conditions.
pub(super) fn lean_instance(
    line: &Printed,
    given: &[(Printed, bool)],
    conditions: usize,
) -> Route<LeanInstance> {
    use super::super::doc::TermKind;
    let bare = |t: Printed| match t.kind {
        TermKind::Paren(inner) => *inner,
        _ => t,
    };
    let arrow_rhs = |t: Printed| match bare(t).kind {
        TermKind::Infix { op, rhs, .. } if op.symbol == "→" => Some(*rhs),
        _ => None,
    };
    let mut at = line.clone();
    let mut values = std::collections::BTreeMap::new();
    for (value, guarded) in given {
        let TermKind::Quantified {
            letter,
            guard,
            body,
            ..
        } = bare(at).kind
        else {
            return Route::no("a line Lean states with fewer letters than are given");
        };
        values.insert(letter, value.clone());
        at = *body;
        // A guard Lean writes as a condition of the body, `0 < x → P`.
        if *guarded && guard.is_none() {
            at = match arrow_rhs(at) {
                Some(rest) => rest,
                None => return Route::no("a guarded letter Lean states with no guard"),
            };
        }
    }
    let mut taken = Vec::new();
    for _ in 0..conditions {
        let TermKind::Infix { op, lhs, rhs } = bare(at).kind else {
            return Route::no("a line Lean states with fewer conditions");
        };
        if op.symbol != "→" {
            return Route::no("a line Lean states with fewer conditions");
        }
        taken.push(super::super::doc::forms::substituted_all(&lhs, &values));
        at = *rhs;
    }
    Route::Built(LeanInstance {
        conditions: taken,
        left: super::super::doc::forms::substituted_all(&at, &values),
    })
}

/// What turns Lean's bound for a membership of ℕ or ℕ₀, `0 < x` or `0 ≤ x`,
/// into the fact the lemma `lemma` says of it (`rules::IMPLIED`): the bound
/// itself, None, or the field of it that says the fact, `ne'` for `x ≠ 0`.
/// None for a lemma not in that table.
pub(super) fn system_fact_field(lemma: &str) -> Option<Option<&'static str>> {
    match lemma {
        "nngt0" | "nnge1" | "nn0ge0" => Some(None),
        "nnne0" => Some(Some("ne'")),
        _ => None,
    }
}

/// `_`: an argument Lean fills from what the term is used as.
pub(super) fn elided_term() -> Printed {
    Printed {
        kind: super::super::doc::TermKind::Elided,
        ty: None,
    }
}

/// A hypothesis applied to arguments by place, `hD1 j h`.
pub(super) fn hyp_applied(hyp: &str, args: Vec<Printed>) -> Printed {
    Printed {
        kind: super::super::doc::TermKind::App {
            head: Box::new(super::super::tactics::hyp(hyp)),
            args: args
                .into_iter()
                .map(super::super::doc::Arg::Explicit)
                .collect(),
            explicit: false,
        },
        ty: None,
    }
}

/// The bounds a range line gives, `x ∈ Finset.Icc a b` proved by `proof`:
/// `a ≤ x` and `x ≤ b`, by `Finset.mem_Icc`; none for any other line.
pub(super) fn range_bounds(says: &Printed, proof: &Printed) -> Vec<(Printed, Printed)> {
    use super::super::doc::{Arg, LeanType, Op, Source, TermKind};
    let TermKind::Infix { op, lhs, rhs } = &says.kind else {
        return Vec::new();
    };
    let TermKind::App { head, args, .. } = &rhs.kind else {
        return Vec::new();
    };
    let (true, TermKind::Const(c), [Arg::Explicit(a), Arg::Explicit(b)]) =
        (op.symbol == "∈", &head.kind, args.as_slice())
    else {
        return Vec::new();
    };
    if c.name != "Finset.Icc" {
        return Vec::new();
    }
    let both = Printed::applied(
        "Finset.mem_Icc.mp",
        Source::Mathlib,
        vec![proof.clone()],
        LeanType::Prop,
    );
    let side = |field: &str| Printed {
        kind: TermKind::Field {
            inner: Box::new(super::super::tactics::bracket(both.clone())),
            field: field.to_string(),
        },
        ty: Some(LeanType::Prop),
    };
    let at_most = |l: &Printed, r: &Printed| {
        Printed::infix(Op::AT_MOST, l.clone(), r.clone(), LeanType::Prop)
    };
    vec![(side("1"), at_most(a, lhs)), (side("2"), at_most(lhs, b))]
}

/// The parts of a sentence's "and" as the page writes it, `node`, each as
/// Lean writes it, `says` taken apart alike, with the term that proves the
/// part where `proof` proves the whole, `.1` and `.2` as it nests; a part
/// of a truth has none.
pub(super) fn and_leaves(
    node: &Node,
    says: &Printed,
    proof: Option<Printed>,
    out: &mut Vec<(Printed, Option<Printed>)>,
    w: &Writer,
) {
    match (w.and_sides(node), and_sides(says)) {
        (Some((nl, nr)), Some((l, r))) => {
            let side = |field: &str| {
                proof
                    .clone()
                    .map(|p| fields(super::super::tactics::bracket(p), &[field]))
            };
            and_leaves(nl, &l, side("1"), out, w);
            and_leaves(nr, &r, side("2"), out, w);
        }
        _ => out.push((says.clone(), proof)),
    }
}

/// The proof of `owe`, the sentence `node`, from the proofs of its parts in
/// order, `⟨a, b⟩` as the page's "and" nests (`and_leaves`); None where
/// too few are left.
pub(super) fn assembled_as(
    node: &Node,
    owe: &Printed,
    proofs: &mut impl Iterator<Item = Proved>,
    w: &Writer,
) -> Option<Proved> {
    match (w.and_sides(node), and_sides(owe)) {
        (Some((nl, nr)), Some((l, r))) => {
            let a = assembled_as(nl, &l, proofs, w)?.term();
            let b = assembled_as(nr, &r, proofs, w)?.term();
            Some(Proved::Term(super::super::expr::anonymous(vec![a, b])))
        }
        _ => proofs.next(),
    }
}

/// `trivial`, the proof of `True`.
pub(super) fn trivial() -> Printed {
    Printed::constant(
        "trivial",
        super::super::doc::Source::Core,
        super::super::doc::LeanType::Prop,
    )
}

/// A proof of `says` turned round: `Ne.symm` of a denied equation, and
/// `.symm` of an equation, a congruence or an "if and only if"; under each
/// "for all" and "if" it opens with, the turn taken inside, `fun k h_k =>
/// (h k h_k).symm`.
pub(super) fn turned_proof(proof: Printed, says: &Printed) -> Printed {
    turned_under(proof, says, None)
}

/// `turned_proof`, inside the binders of the letter `letter` where there is
/// one, whose condition's hypothesis is named after it.
pub(super) fn turned_under(
    proof: Printed,
    says: &Printed,
    letter: Option<&str>,
) -> Printed {
    use super::super::doc::{Quant, TermKind};
    // `fun a h => body`, the letters' types left to Lean.
    let fun = |letters: Vec<String>, body: Printed| Printed {
        kind: TermKind::Lambda {
            letters,
            body: Box::new(body),
        },
        ty: None,
    };
    let mut bare = says;
    while let TermKind::Paren(inner) = &bare.kind {
        bare = inner;
    }
    match &bare.kind {
        TermKind::Quantified {
            quant: Quant::ForAll,
            letter: x,
            letter_ty,
            guard,
            body,
            ..
        } => {
            let at = applied_to(proof, Printed::letter(x, letter_ty.clone()));
            match guard {
                Some(_) => {
                    let h = format!("h_{x}");
                    let at = applied_to(at, super::super::tactics::hyp(&h));
                    fun(vec![x.clone(), h], turned_under(at, body, Some(x)))
                }
                None => fun(vec![x.clone()], turned_under(at, body, Some(x))),
            }
        }
        TermKind::Infix { op, rhs, .. } if op.symbol == "→" => {
            let h = format!("h_{}", letter.unwrap_or("p"));
            let at = applied_to(proof, super::super::tactics::hyp(&h));
            fun(vec![h], turned_under(at, rhs, None))
        }
        _ => match super::super::doc::forms::denies_equation(says) {
            true => Printed::applied(
                "Ne.symm",
                super::super::doc::Source::Core,
                vec![proof],
                super::super::doc::LeanType::Prop,
            ),
            false => super::super::tactics::symm(proof),
        },
    }
}

/// A proof of an equation or congruence used the way the checker found it
/// faces the claim (`record::Facing`): as it stands, or `.symm`.
pub(super) fn faced(proof: Printed, facing: Facing) -> Printed {
    match facing {
        Facing::Straight => proof,
        Facing::Turned => super::super::tactics::symm(proof),
    }
}

/// The facing of a meeting the checker records as turned or not
/// (`matching::Meeting::turned`).
pub(super) fn facing_of_turned(turned: bool) -> Facing {
    match turned {
        true => Facing::Turned,
        false => Facing::Straight,
    }
}

/// Mathlib's rewrite that drops an identity element the checker dropped
/// (`matching::Dropped`): `add_zero` of x + 0, `zero_add` of 0 + x, and so
/// for the other operations; None for one it has no rewrite of.
pub(super) fn identity_lemma(d: &crate::matching::Dropped) -> Option<&'static str> {
    Some(match (d.literal.as_str(), d.hole) {
        ("+", 0) => "zero_add",
        ("+", 1) => "add_zero",
        ("−", 1) => "sub_zero",
        ("·", 0) => "one_mul",
        ("·", 1) => "mul_one",
        ("/", 1) => "div_one",
        (_, 1) if d.operation == "power" => "pow_one",
        _ => return None,
    })
}

/// Whether the writer turns the parts of this notation, one that stands in
/// no order, by a lemma of its own (`turning_rewrites`).
pub(super) fn turns_notation(notation: &str) -> bool {
    matches!(
        notation,
        "distance"
            | "collinear"
            | "forms-a-triangle"
            | "between"
            | "midpoint"
            | "same-side"
            | "opposite-sides"
    )
}

/// The rewrites by which `from` becomes `to`, two writings of one statement
/// that differ only in the order of the parts of notations that stand in no
/// order: each an exact instance of a swap lemma for a node, `dist_comm B A`
/// of `dist B A`, the permutation lemma of the three points of a triangle,
/// in the order the nodes stand. Empty where they are written alike, or
/// where they differ otherwise than so.
pub(super) fn turning_rewrites(from: &Printed, to: &Printed) -> Vec<Printed> {
    use super::super::doc::{Arg, TermKind};
    use super::super::tactics as t;
    let (here, there) = (from.walk(), to.walk());
    if here.len() != there.len() {
        return Vec::new();
    }
    let applied = |lemma: &str, args: Vec<Arg>| Printed {
        kind: TermKind::App {
            head: Box::new(t::lemma(lemma)),
            args,
            explicit: false,
        },
        ty: None,
    };
    let explicit = |terms: &[&Printed]| -> Vec<Arg> {
        terms.iter().map(|x| Arg::Explicit((*x).clone())).collect()
    };
    // The lemma that takes three parts as they stand to the order `to` has
    // them in.
    let permutation =
        |family: &str, parts: [&Printed; 3], goal: [&Printed; 3]| -> Option<Printed> {
            let mut taken = [false; 3];
            let mut idx = [0usize; 3];
            for (k, g) in goal.iter().enumerate() {
                let found =
                    (0..3).find(|&j| !taken[j] && parts[j].text() == g.text())?;
                taken[found] = true;
                idx[k] = found;
            }
            let suffix = match idx {
                [0, 1, 2] => return None,
                [1, 0, 2] => "swap_12",
                [0, 2, 1] => "swap_23",
                [2, 1, 0] => "swap_13",
                [1, 2, 0] => "rot_231",
                _ => "rot_312",
            };
            Some(applied(
                &format!("LeanBridges.Geometry.{family}_{suffix}"),
                explicit(&parts),
            ))
        };
    let mut out = Vec::new();
    for (node, goal) in here.into_iter().zip(there) {
        match (&node.kind, &goal.kind) {
            (
                TermKind::App { head, args, .. },
                TermKind::App {
                    args: wanted_args, ..
                },
            ) => {
                let TermKind::Const(c) = &head.kind else {
                    continue;
                };
                let at = |a: &'_ Vec<Arg>, k: usize| match a.get(k) {
                    Some(Arg::Explicit(x)) => Some(x.clone()),
                    _ => None,
                };
                match (c.name.as_str(), args.len()) {
                    ("dist", 2) => {
                        if let (Some(a), Some(b), Some(w)) =
                            (at(args, 0), at(args, 1), at(wanted_args, 0))
                        {
                            if a.text() != w.text() {
                                out.push(applied("dist_comm", explicit(&[&a, &b])));
                            }
                        }
                    }
                    ("Sbtw", 4) => {
                        if let (Some(x), Some(y), Some(z), Some(w)) =
                            (at(args, 1), at(args, 2), at(args, 3), at(wanted_args, 1))
                        {
                            if x.text() != w.text() {
                                out.push(applied(
                                    "sbtw_comm",
                                    [("x", &x), ("y", &y), ("z", &z)]
                                        .into_iter()
                                        .map(|(name, v)| Arg::Named {
                                            name: name.to_string(),
                                            value: v.clone(),
                                        })
                                        .collect(),
                                ));
                            }
                        }
                    }
                    ("LeanBridges.Geometry.Triangle", 3) => {
                        if let (Some(a), Some(b), Some(c), Some(x), Some(y), Some(z)) = (
                            at(args, 0),
                            at(args, 1),
                            at(args, 2),
                            at(wanted_args, 0),
                            at(wanted_args, 1),
                            at(wanted_args, 2),
                        ) {
                            out.extend(permutation(
                                "triangle",
                                [&a, &b, &c],
                                [&x, &y, &z],
                            ));
                        }
                    }
                    ("Collinear", 2) => {
                        if let (
                            Some(Printed {
                                kind: TermKind::Listed { items, .. },
                                ..
                            }),
                            Some(Printed {
                                kind: TermKind::Listed { items: wanted, .. },
                                ..
                            }),
                        ) = (at(args, 1), at(wanted_args, 1))
                        {
                            if let ([a, b, c], [x, y, z]) =
                                (items.as_slice(), wanted.as_slice())
                            {
                                out.extend(permutation(
                                    "collinear",
                                    [a, b, c],
                                    [x, y, z],
                                ));
                            }
                        }
                    }
                    _ => {}
                }
            }
            (
                TermKind::Infix { op, lhs, rhs },
                TermKind::Infix {
                    lhs: wanted_lhs, ..
                },
            ) if op.symbol == "*" => {
                let imaginary = |x: &Printed| {
                    matches!(&x.kind, TermKind::App { head, .. }
                        if matches!(&head.kind, TermKind::Const(c) if c.name == "Complex.im"))
                };
                if imaginary(lhs) && imaginary(rhs) && lhs.text() != wanted_lhs.text() {
                    out.push(applied("mul_comm", explicit(&[lhs, rhs])));
                }
            }
            _ => {}
        }
    }
    // A rewrite takes every place of its left side at once, so a node
    // written twice alike is turned by one.
    let mut once: Vec<Printed> = Vec::new();
    for r in out {
        if !once.iter().any(|seen| seen.text() == r.text()) {
            once.push(r);
        }
    }
    once
}

/// Which of the two ways a flip's term is written a rewrite starts from.
#[derive(Clone, Copy)]
pub(super) enum Toward<'s> {
    /// The way the first tree the checker met writes it, `Flip::term`.
    FromFirst,
    /// The way the second writes it, `Flip::turned`.
    FromSecond,
    /// Whichever this statement holds, where the meeting's trees stand
    /// either way round to the proof at hand.
    Holding(&'s Printed),
}

/// The rewrites that take a statement across each flip the checker
/// recorded (`matching::Flip`): of the two ways the flip's term is written,
/// its own and its parts in the flip's order, the one `toward` names is
/// rewritten to the other by an exact instance of the notation's swap
/// lemma, `dist_comm C A` of `dist C A`. A flip whose term the statement
/// `Toward::Holding` names holds in neither way gives none. None where a
/// flip's notation has no lemma, or its term does not print.
pub(super) fn flip_rewrites(
    writer: &super::super::expr::Writer,
    flips: &[crate::matching::Flip],
    toward: Toward<'_>,
) -> Option<Vec<Printed>> {
    use super::super::doc::{Arg, TermKind};
    use super::super::tactics as t;
    use super::super::templates::Num;
    let applied = |lemma: &str, args: Vec<Arg>| Printed {
        kind: TermKind::App {
            head: Box::new(t::lemma(lemma)),
            args,
            explicit: false,
        },
        ty: None,
    };
    let print = |node: &Node| match node.notation_name().as_ref() {
        "distance" => writer.number_fixed(node, Num::Real).built(),
        _ => writer.formula(node).built(),
    };
    let points = |node: &Node| -> Option<Vec<Printed>> {
        node.children
            .iter()
            .map(|c| writer.number_fixed(c, Num::Complex).built())
            .collect()
    };
    let mut out: Vec<Printed> = Vec::new();
    for flip in flips {
        if !turns_notation(&flip.notation) {
            return None;
        }
        let (first, second) = (flip.term.clone(), flip.turned());
        let back = || {
            let mut back = vec![0; flip.order.len()];
            for (k, &j) in flip.order.iter().enumerate() {
                if let Some(slot) = back.get_mut(j) {
                    *slot = k;
                }
            }
            back
        };
        // The term rewritten, and the order its parts go to: from the first
        // tree's way to the second's, `order`; from the second's back, its
        // inverse.
        let (node, idx): (Node, Vec<usize>) = match toward {
            Toward::FromFirst => (first, flip.order.clone()),
            Toward::FromSecond => (second, back()),
            Toward::Holding(says) => {
                let text = says.text();
                if text.contains(&print(&first)?.text()) {
                    (first, flip.order.clone())
                } else if text.contains(&print(&second)?.text()) {
                    (second, back())
                } else {
                    continue;
                }
            }
        };
        let parts = points(&node)?;
        let explicit =
            |terms: Vec<Printed>| terms.into_iter().map(Arg::Explicit).collect();
        let rewrite = match (flip.notation.as_str(), idx.as_slice()) {
            ("distance", [1, 0]) => applied("dist_comm", explicit(parts)),
            ("between", [0, 2, 1]) => {
                let [p, a, b] = <[Printed; 3]>::try_from(parts).ok()?;
                applied(
                    "sbtw_comm",
                    [("x", a), ("y", p), ("z", b)]
                        .into_iter()
                        .map(|(name, value)| Arg::Named {
                            name: name.to_string(),
                            value,
                        })
                        .collect(),
                )
            }
            // `M is the midpoint of AB`, its ends exchanged.
            ("midpoint", [0, 2, 1]) => {
                applied("LeanBridges.Geometry.midpoint_comm", explicit(parts))
            }
            ("collinear" | "forms-a-triangle", [i, j, k]) => {
                let family = match flip.notation.as_str() {
                    "collinear" => "collinear",
                    _ => "triangle",
                };
                let suffix = match [*i, *j, *k] {
                    [1, 0, 2] => "swap_12",
                    [0, 2, 1] => "swap_23",
                    [2, 1, 0] => "swap_13",
                    [1, 2, 0] => "rot_231",
                    [2, 0, 1] => "rot_312",
                    _ => return None,
                };
                applied(
                    &format!("LeanBridges.Geometry.{family}_{suffix}"),
                    explicit(parts),
                )
            }
            ("same-side" | "opposite-sides", [1, 0, 2, 3]) => {
                // The two factors of the side test, as Lean writes the term.
                let whole = print(&node)?;
                let product = whole.walk().into_iter().find_map(|n| match &n.kind {
                    TermKind::Infix { op, lhs, rhs } if op.symbol == "*" => {
                        Some(((**lhs).clone(), (**rhs).clone()))
                    }
                    _ => None,
                })?;
                applied("mul_comm", explicit(vec![product.0, product.1]))
            }
            _ => return None,
        };
        if !out.iter().any(|seen| seen.text() == rewrite.text()) {
            out.push(rewrite);
        }
    }
    Some(out)
}

/// `proof`, a proof of a statement Lean writes, rewritten by `rewrites`
/// (`flip_rewrites`), and given the statement `to` it then proves, so that
/// inside an unnamed `have` `rw` has no open goal of its own to close.
pub(super) fn rewritten_to(
    proof: Printed,
    rewrites: Vec<Printed>,
    to: &Printed,
) -> Printed {
    use super::super::tactics as t;
    if rewrites.is_empty() {
        return proof;
    }
    let rules = rewrites.into_iter().map(t::forwards).collect();
    let turned = t::by_term(super::super::doc::Proof::By(t::on_h(
        &proof,
        vec![
            t::call(
                "rw",
                vec![super::super::doc::TacticArg::Rules(rules), t::at_h(false)],
            ),
            super::super::doc::Tactic::Exact(t::hyp("h")),
        ],
    )));
    Printed {
        kind: super::super::doc::TermKind::Ascribed {
            proof: Box::new(turned),
            says: Box::new(to.clone()),
        },
        ty: None,
    }
}

/// An algebra's proof whose lines are taken to one order of the parts of
/// the notations that stand in no order (`Proof::with_commuted`): each
/// fact it states first, a divisor's `hz1 : |PA| ≠ 0`, stated in that order
/// too, its proof turned to it.
pub(super) fn haves_in_one_order(
    proof: super::super::doc::Proof,
) -> super::super::doc::Proof {
    use super::super::doc::{Proof, Tactic};
    let ordered = |t: Tactic| match t {
        Tactic::Have { name, says, proof } => match *proof {
            Proof::Term(term) => {
                let to = says.in_one_order();
                Tactic::Have {
                    name,
                    proof: Box::new(Proof::Term(turned_to(term, &says, &to))),
                    says: to,
                }
            }
            other => Tactic::Have {
                name,
                says,
                proof: Box::new(other),
            },
        },
        other => other,
    };
    match proof {
        Proof::By(Tactic::Seq(steps)) => {
            Proof::By(Tactic::Seq(steps.into_iter().map(ordered).collect()))
        }
        Proof::Block(steps) => Proof::Block(steps.into_iter().map(ordered).collect()),
        other => other,
    }
}

/// `proof`, a proof of `from`, taken to a proof of `to`, the same statement
/// with the parts of notations that stand in no order in another order
/// (`turning_rewrites`); `proof` itself where they are written alike.
pub(super) fn turned_to(proof: Printed, from: &Printed, to: &Printed) -> Printed {
    rewritten_to(proof, turning_rewrites(from, to), to)
}

/// Whether every notation a meeting paired in another order is one with
/// no swap lemma, a listed set, whose members the writer takes in the
/// claim's order (`reordered`); a meeting of any other is turned by its
/// notation's lemmas (`met_proof`).
pub(super) fn permuted_only_listed(met: &crate::matching::Meeting) -> bool {
    met.flips.iter().all(|f| !turns_notation(&f.notation))
}

/// The two sides of an "and", as Lean writes it: `a ∧ b`, bracketed or
/// not; of several sentences, which group to the right, the first and the
/// rest.
pub(super) fn and_sides(term: &Printed) -> Option<(Printed, Printed)> {
    use super::super::doc::{Op, TermKind};
    match &term.kind {
        TermKind::Paren(inner) => and_sides(inner),
        TermKind::Infix { op, lhs, rhs } if *op == Op::AND => {
            Some(((**lhs).clone(), (**rhs).clone()))
        }
        _ => None,
    }
}

/// What a block, a part of one or a theorem owes at its end
/// (`Proof::closing`).
pub(super) enum Owing<'a> {
    /// The record's sentences as the page writes them (`Owed::written`);
    /// None, or none, for a block that ends on a contradiction.
    Written(Option<&'a [Node]>),
    /// The goal as Lean has it, where Lean makes it itself: an induction's
    /// motive at its start or at the next value, `goal`, with the record's
    /// sentences it says (`nodes`), whose "and" the parts are split by.
    Lean {
        nodes: Option<&'a [Node]>,
        goal: Vec<Printed>,
    },
}

/// What ends a block, a part of one or a theorem (`Proof::closing`).
pub(super) enum Closing {
    /// Its last step, by name, says what is owed as Lean writes it: the
    /// step's proof proves the goal.
    Last(String),
    /// A tactic that closes the goal.
    Tactic(Box<Tactic>),
    /// Nothing: the last step, shown impossible, closed it.
    Closed,
}

/// A proof given as an argument: a line's name or `(by norm_num)`.
pub(super) fn proof_arg(proof: super::super::expr::Printed) -> super::super::doc::Arg {
    super::super::doc::Arg::Explicit(proof)
}

/// The module a declaration's full name is in, `Parley.Items.Stdlib.Counting`
/// of `Parley.Items.Stdlib.Counting.mun_card_singleton`.
pub(super) fn module_of_decl(decl: &str) -> String {
    match decl.rsplit_once('.') {
        Some((module, _)) => module.to_string(),
        None => decl.to_string(),
    }
}

/// Where a line of a Lean file comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The line of the Lean file, from 1.
    pub line: usize,
    /// The line of the proof file it was written for.
    pub page_line: usize,
    /// What it was written for.
    pub spot: Spot,
}

/// What a line of a Lean file was written for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spot {
    /// The theorem's statement, or a line of the file around it.
    Statement,
    /// A step, by its number as the page writes it.
    Step(String),
}

/// What writing a theorem reads: the corpus as checked, the notations and
/// items in Lean, and the theorems of the corpus as items in Lean.
pub struct Sources<'a> {
    pub checked: &'a CheckedCorpus,
    pub templates: &'a Templates,
    /// What each notation is to the methods' decisions, which `algebra`
    /// asks for its multipliers.
    pub targets: &'a crate::methods::terms::Targets,
    /// Every item a citation may name that has a Lean form, by full name:
    /// the library's records and the corpus's theorems.
    pub items: &'a IndexMap<String, Item>,
    /// What the checker matches terms with, its identity elements among
    /// them, so that a step is read as the checker decided it.
    pub ctx: &'a crate::matching::Context,
}

/// The terms a theorem puts in a hole of type ℝ, the A/B of ⌊A/B⌋ (set.mm's
/// floor being of reals), as the page prints them: each is a real wherever
/// the theorem writes it, so that a line about it meets the floor's.
pub(super) fn held_real(rec: &CheckedTheorem, writer: &Writer) -> Vec<String> {
    let mut out = Vec::new();
    for (_, node) in rec.page.entries() {
        for n in node.walk() {
            // A letter has its own type; a term of numerals alone, the 2 of
            // √2, takes the type of where it stands.
            for arg in writer.always_real_args(&n) {
                let printed = writer.grammar.print(arg);
                let of_letters = arg.walk().iter().any(|m| m.is_name());
                if !arg.is_name() && of_letters && !out.contains(&printed) {
                    out.push(printed);
                }
            }
        }
    }
    out
}

/// Why a function a proof defines whose values are sets, I(k) = {|x| : x ∈
/// 𝒫{1, …, k}}, is not written: the writer types a function letter as one
/// into numbers only.
pub const SET_VALUED: &str = "a function a proof defines whose values are sets";

/// Whether the checker reads the name a proof defines as a function whose
/// values are sets.
pub fn set_valued(rec: &CheckedTheorem, name: &str) -> bool {
    matches!(
        rec.sorts.get(name).and_then(|s| s.full()),
        Some(crate::formula::Whole::Function(_, to))
            if matches!(**to, crate::formula::Whole::Set(_))
    )
}

/// Whether the record sorts a letter as a function whose values are pairs,
/// f(i) = (L(i), M(i)).
pub fn pair_valued(rec: &CheckedTheorem, name: &str) -> bool {
    matches!(
        rec.sorts.get(name).and_then(|s| s.full()),
        Some(crate::formula::Whole::Function(_, to))
            if matches!(**to, crate::formula::Whole::Pair(_, _))
    )
}

/// The record the writer reads: the checker's with what the theorem's file
/// defines outside it written out (`CheckedTheorem::written`), or as read
/// where it defines nothing so.
pub fn as_written(rec: &CheckedTheorem) -> &CheckedTheorem {
    rec.written.as_deref().unwrap_or(rec)
}

/// The theorem as an item of the library: its statement's binders, and its
/// `then` sentences joined into one Lean statement, each taken by its
/// projection.
pub fn as_item(sources: &Sources, thm: &Theorem, rec: &CheckedTheorem) -> Route<Item> {
    let rec = as_written(rec);
    let mut writer = super::statement_writer(sources, rec);
    let stated = match statement(&mut writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    let module = super::super::names::module_of(&thm.qualified());
    let decl = format!("{module}.{}", snake(&thm.name));
    let n = stated.conclusion.len();
    let mut written: Vec<Node> = hypothesis_sentences(thm, rec)
        .into_iter()
        .flat_map(|(_, s)| s.into_iter().map(|s| s.node))
        .collect();
    written.extend(stated.conclusion.iter().map(|c| c.says.clone()));
    let mut arithmetic = super::super::readback::page_arithmetic(&writer, &written);
    for (op, n) in recursion_arithmetic(&writer, thm, rec) {
        *arithmetic.entry(op).or_insert(0) += n;
    }
    let sentences = stated
        .conclusion
        .into_iter()
        .enumerate()
        .map(|(i, c)| Sentence {
            decl: decl.clone(),
            binders: stated.binders.clone(),
            says: c.says,
            prop: c.prop,
            part: projection_path(i, n),
            arithmetic: arithmetic.clone(),
            general: None,
            domains: writer.domains.clone(),
        })
        .collect();
    Route::Built(Item {
        module,
        sentences,
        proofs: Vec::new(),
    })
}

/// The parts of an "and" as its tree nests them, in order: ((A ∧ B) ∧ C)
/// gives A, B, C; anything else is one part.
pub(super) fn and_parts<'n>(node: &'n Node, w: &Writer) -> Vec<&'n Node> {
    match w.and_sides(node) {
        Some((l, r)) => {
            let mut out = and_parts(l, w);
            out.extend(and_parts(r, w));
            out
        }
        None => vec![node],
    }
}

/// The projection that takes part `i` of an "and" as its tree nests it,
/// `.1.2` for B of ((A ∧ B) ∧ C); None where it has no part `i`.
pub(super) fn leaf_path(
    node: &Node,
    i: usize,
    w: &Writer,
) -> Option<Vec<&'static str>> {
    match w.and_sides(node) {
        Some((l, r)) => {
            let left = and_parts(l, w).len();
            let (side, rest) = match i < left {
                true => ("1", leaf_path(l, i, w)),
                false => ("2", leaf_path(r, i - left, w)),
            };
            rest.map(|mut path| {
                path.insert(0, side);
                path
            })
        }
        _ => (i == 0).then(Vec::new),
    }
}

/// A recursion's rules as one hypothesis: its starts, then for every k
/// from 0 its steps, `F 0 = a ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = b`.
pub(super) fn rules_said(
    k: &str,
    starts: Vec<Printed>,
    steps: Vec<Printed>,
) -> Printed {
    use super::super::doc::{LeanType, Op};
    let int = LeanType::Num(super::super::templates::Num::Int);
    let from_0 = Printed::infix(
        Op::AT_MOST,
        Printed::numeral("0", int.clone()),
        super::super::tactics::hyp(k),
        LeanType::Prop,
    );
    let every = Printed::of(
        super::super::doc::TermKind::Quantified {
            quant: super::super::doc::Quant::ForAll,
            letter: k.to_string(),
            letter_ty: int,
            guard: Some(Box::new(from_0)),
            body: Box::new(conjunction(steps).unwrap_or_else(Printed::truth)),
            bounded: false,
        },
        LeanType::Prop,
    );
    // One chain to the right, the starts and then the steps' "for all",
    // `F 0 = a ∧ G 0 = b ∧ ∀ k : ℤ, …`, whose projections take each.
    let mut parts = starts;
    parts.push(every);
    conjunction(parts).unwrap_or_else(Printed::truth)
}

/// The parts joined by `∧`, which chains to the right; None of no parts.
pub(super) fn conjunction(parts: Vec<Printed>) -> Option<Printed> {
    parts.into_iter().rev().reduce(|right, left| {
        Printed::infix(
            super::super::doc::Op::AND,
            left,
            right,
            super::super::doc::LeanType::Prop,
        )
    })
}

/// Whether the statement applies a function to a numeral, through brackets
/// and casts: `Complex.cos 0`.
pub(super) fn function_of_numeral(statement: &Printed) -> bool {
    use super::super::doc::{Arg, TermKind};
    fn bare(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) | TermKind::Cast { inner, .. } => bare(inner),
            _ => t,
        }
    }
    statement.walk().iter().any(|t| {
        let TermKind::App { args, .. } = &t.kind else {
            return false;
        };
        args.iter().any(|a| match a {
            Arg::Explicit(v) | Arg::Named { value: v, .. } => {
                matches!(bare(v).kind, TermKind::Numeral(_))
            }
        })
    })
}

/// Whether the term holds a cast whose term, through brackets, is a
/// `toNat`: `((2^p − 1).toNat : ℤ)`.
pub(super) fn casts_a_to_nat(term: &Printed) -> bool {
    use super::super::doc::TermKind;
    fn bare(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) => bare(inner),
            _ => t,
        }
    }
    term.walk().iter().any(|t| {
        matches!(&t.kind, TermKind::Cast { inner, .. }
            if matches!(bare(inner).kind, TermKind::ToNat(_)))
    })
}

/// Lean's lemma `name` applied to `args`, a proof.
pub(super) fn applied(name: &str, args: Vec<super::super::doc::Arg>) -> Printed {
    Printed {
        kind: super::super::doc::TermKind::App {
            head: Box::new(super::super::tactics::lemma(name)),
            args,
            explicit: false,
        },
        ty: Some(super::super::doc::LeanType::Prop),
    }
}

/// `start` with `letter` put at each of `places`, each a path of children
/// from the top (`matching::SubstitutionPlaces`); a path that leads nowhere
/// puts nothing.
pub(super) fn mark_places(start: &Node, places: &[Vec<usize>], letter: &Node) -> Node {
    if places.iter().any(|p| p.is_empty()) {
        return letter.clone();
    }
    let kids: Vec<Node> = start
        .children
        .iter()
        .enumerate()
        .map(|(k, child)| {
            let below: Vec<Vec<usize>> = places
                .iter()
                .filter(|p| p.first() == Some(&k))
                .map(|p| p[1..].to_vec())
                .collect();
            match below.is_empty() {
                true => child.clone(),
                false => mark_places(child, &below, letter),
            }
        })
        .collect();
    start.with_children(kids)
}

/// A fact an order step adds, as the writer reads it (`order_fact`).
pub(super) struct OrderFactTerm {
    /// The term that proves it.
    pub(super) proof: Printed,
    /// What Lean states it as.
    pub(super) says: Printed,
    /// The fact as the page writes it, which is stated again in a wider
    /// type where the step works in one.
    pub(super) node: Node,
    /// Whether `node` states, in a wider type, what `proof` proves. Not of
    /// a define's kind, whose fact the page writes of the define's value
    /// and Lean proves of its letter.
    pub(super) widens: bool,
    /// Whether it is the equation of a define the step cites.
    pub(super) define: bool,
}

/// The number type a relation Lean states is in; None for one in no
/// number type, or in an item's general type.
pub(super) fn number_type(says: &Printed) -> Option<super::super::templates::Num> {
    match super::super::doc::forms::relation_type(says)? {
        super::super::doc::LeanType::Num(n) => Some(n),
        _ => None,
    }
}

/// Whether the relation `narrow` states in ℚ is taken to `wide`, the same
/// relation in ℝ.
pub(super) fn rat_crossing(narrow: &Printed, wide: &Printed) -> bool {
    use super::super::templates::Num;
    (number_type(narrow), number_type(wide)) == (Some(Num::Rat), Some(Num::Real))
}

/// The lemma that casts a relation of ℚ to the same relation in a wider
/// field, by the relation: `Rat.cast_le`, `Rat.cast_lt`, `Rat.cast_inj`.
/// None of a disequality or anything else.
pub(super) fn rat_relation_lemma(says: &Printed) -> Option<&'static str> {
    match relation_symbol(says)? {
        "≤" | "≥" => Some("Rat.cast_le"),
        "<" | ">" => Some("Rat.cast_lt"),
        "=" => Some("Rat.cast_inj"),
        _ => None,
    }
}

/// The proof of a relation of ℝ from `proof` of the same relation of ℚ,
/// `says`, which holds no cast to ℝ for `norm_cast` to take up: by the
/// relation's lemma at ℝ, ℚ's casts pushed down to the letters and
/// numerals (`rat_cast_lemmas`), and the casts left in both pushed alike.
/// None of a relation with no such lemma.
pub(super) fn rat_lifted(proof: Printed, says: &Printed) -> Option<Printed> {
    use super::super::tactics as t;
    let lemma = rat_relation_lemma(says)?;
    let up = applied_to(
        fields(
            rat_relation_at(lemma, super::super::templates::Num::Real),
            &["mpr"],
        ),
        proof,
    );
    let both = super::super::doc::TacticArg::At(vec![
        super::super::doc::Location::Hypothesis("h".to_string()),
        super::super::doc::Location::Goal,
    ]);
    Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
        t::name_h(&up),
        t::simp_only(false, None, rat_cast_lemmas(says), Some(t::at_h(false))),
        t::push_cast(Some(both)),
        Tactic::Exact(t::hyp("h")),
    ]))))
}

/// `(Rat.cast_le (K := ℝ))`: the relation lemma `lemma` at the field `to`.
pub(super) fn rat_relation_at(
    lemma: &str,
    to: super::super::templates::Num,
) -> Printed {
    use super::super::doc::{Arg, LeanType, Source, TermKind};
    // Mathlib names the field `α` in `Rat.cast_inj` and `K` in the orders'.
    let field = match lemma {
        "Rat.cast_inj" => "α",
        _ => "K",
    };
    super::super::tactics::bracket(Printed::of(
        TermKind::App {
            head: Box::new(Printed::head(lemma, Source::Mathlib)),
            args: vec![Arg::Named {
                name: field.to_string(),
                value: Printed::letter(to.lean(), LeanType::Prop),
            }],
            explicit: false,
        },
        LeanType::Prop,
    ))
}

/// The lemmas that push a cast from ℚ through each operation `says`
/// holds, down to its letters and numerals, in a fixed order: ℚ's own
/// (`Rat.cast_div`, `Rat.cast_pow`, …), never a step through ℕ.
pub(super) fn rat_cast_lemmas(says: &Printed) -> Vec<super::super::doc::Rule> {
    use super::super::doc::{BoundForm, TermKind};
    const ORDER: [&str; 15] = [
        "Rat.cast_sum",
        "Rat.cast_prod",
        "Rat.cast_add",
        "Rat.cast_sub",
        "Rat.cast_mul",
        "Rat.cast_div",
        "Rat.cast_neg",
        "Rat.cast_pow",
        "Rat.cast_zpow",
        "Rat.cast_inv",
        "Rat.cast_zero",
        "Rat.cast_one",
        "Rat.cast_ofNat",
        "Rat.cast_intCast",
        "Rat.cast_natCast",
    ];
    let mut used = std::collections::BTreeSet::new();
    for t in says.walk() {
        let lemma = match &t.kind {
            TermKind::Infix { op, rhs, .. } => match op.symbol {
                "+" => "Rat.cast_add",
                "-" => "Rat.cast_sub",
                "*" => "Rat.cast_mul",
                "/" => "Rat.cast_div",
                // To an integer exponent, Lean's `zpow`.
                "^" if rhs.ty
                    == Some(super::super::doc::LeanType::Num(
                        super::super::templates::Num::Int,
                    )) =>
                {
                    "Rat.cast_zpow"
                }
                "^" => "Rat.cast_pow",
                _ => continue,
            },
            TermKind::Neg(_) => "Rat.cast_neg",
            TermKind::Postfix { .. } => "Rat.cast_inv",
            TermKind::Bound {
                form: BoundForm::BigOp { product, .. },
                ..
            } => match product {
                true => "Rat.cast_prod",
                false => "Rat.cast_sum",
            },
            TermKind::Numeral(n) => match n.as_str() {
                "0" => "Rat.cast_zero",
                "1" => "Rat.cast_one",
                _ => "Rat.cast_ofNat",
            },
            TermKind::Cast { inner, .. } => match &inner.ty {
                Some(super::super::doc::LeanType::Num(
                    super::super::templates::Num::Int,
                )) => "Rat.cast_intCast",
                Some(super::super::doc::LeanType::Num(
                    super::super::templates::Num::Nat,
                )) => "Rat.cast_natCast",
                _ => continue,
            },
            _ => continue,
        };
        used.insert(lemma);
    }
    ORDER
        .iter()
        .filter(|l| used.contains(*l))
        .map(|l| super::super::tactics::forwards(super::super::tactics::lemma(l)))
        .collect()
}

/// A fact of ℚ, `proof` of `narrow`, stated in ℝ as `wide`: the relation
/// cast whole by its lemma, then the cast pushed down by ℚ's cast lemmas
/// alone. `exact_mod_cast` would first write a power of a numeral, `(2 :
/// ℚ) ^ n`, as a cast of ℕ, which it cannot then move through a division,
/// and leave the fact in ℚ and the goal in ℝ (measured on HalvesSeries).
/// None of a relation with no such lemma.
pub(super) fn rat_to_real(
    proof: Printed,
    narrow: &Printed,
    wide: Printed,
) -> Option<Printed> {
    use super::super::doc::{LeanType, Proof, TermKind};
    use super::super::tactics as t;
    // A negated equation, `a ≠ b` or `¬ a = b`, is cast by its equation's
    // lemma, negated (`Rat.cast_inj.not`).
    let (lemma, path): (_, &[&str]) = match &unparenthesized(narrow).kind {
        TermKind::Not(inner) if relation_symbol(inner) == Some("=") => {
            ("Rat.cast_inj", &["not", "mpr"])
        }
        _ if relation_symbol(narrow) == Some("≠") => {
            ("Rat.cast_inj", &["not", "mpr"])
        }
        _ => (rat_relation_lemma(narrow)?, &["mpr"]),
    };
    let to = number_type(&wide)?;
    let cast = Printed::of(
        TermKind::App {
            head: Box::new(fields(rat_relation_at(lemma, to), path)),
            args: vec![super::super::doc::Arg::Explicit(proof)],
            explicit: false,
        },
        LeanType::Prop,
    );
    // Where no cast is left inside to push down, the relation's cast is
    // the fact in ℝ as it stands.
    let lemmas = rat_cast_lemmas(&wide);
    if lemmas.is_empty() {
        return Some(cast);
    }
    let steps = vec![
        Tactic::Name {
            name: "h".to_string(),
            term: cast,
        },
        t::simp_only(false, None, lemmas, Some(t::at_h(false))),
        Tactic::Exact(t::hyp("h")),
    ];
    Some(t::bracket(shown(wide, Proof::By(Tactic::Seq(steps)))))
}

/// A claim of ℚ, `narrow`, proved from `wide`, the same relation in ℝ,
/// which `proof` proves: its relation lemma backwards, the goal's cast
/// pushed down by ℚ's cast lemmas alone, as `rat_to_real` goes up. None of
/// a relation with no such lemma.
pub(super) fn real_to_rat(
    proof: super::super::doc::Proof,
    narrow: &Printed,
    wide: Printed,
) -> Option<super::super::doc::Proof> {
    use super::super::doc::{LeanType, Proof, TermKind};
    use super::super::tactics as t;
    let lemma = rat_relation_lemma(narrow)?;
    let to = number_type(&wide)?;
    let lemmas = rat_cast_lemmas(&wide);
    let pushed = Proof::By(Tactic::Seq(vec![
        t::simp_only(false, None, lemmas, None),
        Tactic::Exact(t::hyp("h")),
    ]));
    let back = Printed::of(
        TermKind::App {
            head: Box::new(fields(rat_relation_at(lemma, to), &["mp"])),
            args: vec![super::super::doc::Arg::Explicit(t::bracket(t::by_term(
                pushed,
            )))],
            explicit: false,
        },
        LeanType::Prop,
    );
    Some(Proof::Block(vec![
        Tactic::Have {
            name: "h".to_string(),
            says: wide,
            proof: Box::new(proof),
        },
        Tactic::Exact(back),
    ]))
}

/// Whether `exact_mod_cast` takes the relation `narrow` states to the same
/// relation in the type `to`: `norm_cast` moves a cast of that pair of
/// types through the relation and, with each side cast up as a whole,
/// through every operation inside it (the cast table). A cast the narrow
/// statement already holds, a letter's ℤ to ℚ, stays where it stands in
/// both and is read as an atom: `norm_cast` reads the wide statement's ℤ
/// to ℝ as ℤ to ℚ to ℝ, so only the cast to `to` moves.
pub(super) fn lifts_whole(narrow: &Printed, to: super::super::templates::Num) -> bool {
    use super::super::doc::{LeanType, TermKind};
    let narrow = match &narrow.kind {
        TermKind::Paren(inner) => inner,
        _ => narrow,
    };
    let TermKind::Infix { op, lhs, rhs } = &narrow.kind else {
        return false;
    };
    let wide = LeanType::Num(to);
    let lifted = Printed::infix(
        *op,
        Printed::cast(casts_as_atoms(lhs), wide.clone()),
        Printed::cast(casts_as_atoms(rhs), wide.clone()),
        LeanType::Prop,
    );
    super::super::casts::norm_cast_lifts_relation(narrow, &wide)
        && super::super::casts::norm_cast_moves_all(&lifted)
}

/// `term` with each cast in it a letter of the type it is cast to, which
/// the cast table reads as an atom.
pub(super) fn casts_as_atoms(term: &Printed) -> Printed {
    use super::super::doc::TermKind;
    if let TermKind::Cast { to, .. } = &term.kind {
        return Printed::letter("x", to.clone());
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = casts_as_atoms(c);
    }
    out
}

/// An order turned to face the other way, `0 < 2` of `2 > 0`.
pub(super) struct OrderTurn {
    /// The lemma that turns its proof, `gt_iff_lt.mp`.
    pub(super) lemma: &'static str,
    /// The order as it then stands.
    pub(super) faced: Printed,
}

/// How `says`, an order, is turned to face as `wanted` faces: `2 > 0`
/// where `wanted` writes `<` by `gt_iff_lt.mp`, to `0 < 2`. None where the
/// two face alike, or either is no order.
pub(super) fn order_turn(says: &Printed, wanted: &Printed) -> Option<OrderTurn> {
    use super::super::doc::TermKind;
    let (lemma, turned) = match (relation_symbol(says)?, relation_symbol(wanted)?) {
        (">", "<") => ("gt_iff_lt.mp", "<"),
        ("≥", "≤") => ("ge_iff_le.mp", "≤"),
        ("<", ">") => ("gt_iff_lt.mpr", ">"),
        ("≤", "≥") => ("ge_iff_le.mpr", "≥"),
        _ => return None,
    };
    let TermKind::Infix { lhs, rhs, .. } = &unparenthesized(says).kind else {
        return None;
    };
    let faced = Printed::infix(
        super::super::doc::Op::of(turned)?,
        (**rhs).clone(),
        (**lhs).clone(),
        super::super::doc::LeanType::Prop,
    );
    Some(OrderTurn { lemma, faced })
}

/// How Lean writes a disequality with its sides swapped, `b ≠ a` of
/// `a ≠ b`; None of anything else.
pub(super) fn turned_relation_text(says: &Printed) -> Option<String> {
    use super::super::doc::TermKind;
    match &says.kind {
        TermKind::Infix { op, lhs, rhs } if op.symbol == "≠" => Some(
            Printed::infix(
                *op,
                (**rhs).clone(),
                (**lhs).clone(),
                super::super::doc::LeanType::Prop,
            )
            .text(),
        ),
        TermKind::Not(inner) => match &inner.kind {
            TermKind::Infix { op, lhs, rhs } if op.symbol == "=" => {
                let swapped = Printed::infix(
                    *op,
                    (**rhs).clone(),
                    (**lhs).clone(),
                    super::super::doc::LeanType::Prop,
                );
                Some(
                    Printed::of(
                        TermKind::Not(Box::new(swapped)),
                        super::super::doc::LeanType::Prop,
                    )
                    .text(),
                )
            }
            _ => None,
        },
        _ => None,
    }
}

/// The equations that tie a numeral over a term to the term's reciprocal,
/// `div_eq_mul_one_div 2 (n + 1)`, for each term `stated` divides by more
/// than one numeral: the checker reads 2/(n + 1) as 2·(1/(n + 1)), one atom
/// with 1/(n + 1) (`METHODS.md`, inequalities, Atoms), where Lean's
/// `linarith` takes each quotient as an atom of its own.
pub(super) fn reciprocals(stated: &[&Printed]) -> Vec<Printed> {
    use super::super::doc::{LeanType, Source, TermKind};
    let numeral = |t: &Printed| matches!(&t.kind, TermKind::Numeral(_));
    // Each quotient with the number type of the relation it stands in.
    let mut quotients: Vec<(&Printed, &Printed, Option<super::super::templates::Num>)> =
        Vec::new();
    for s in stated {
        let ty = number_type(s);
        for term in s.walk() {
            if let TermKind::Infix { op, lhs, rhs } = &term.kind {
                if op.symbol == "/" && numeral(lhs) && !numeral(rhs) {
                    let seen = quotients.iter().any(|(l, r, _)| {
                        l.text() == lhs.text() && r.text() == rhs.text()
                    });
                    if !seen {
                        quotients.push((lhs, rhs, ty));
                    }
                }
            }
        }
    }
    quotients
        .iter()
        .filter(|(lhs, rhs, _)| {
            lhs.text() != "1"
                && quotients
                    .iter()
                    .any(|(l, r, _)| r.text() == rhs.text() && l.text() != lhs.text())
        })
        .map(|(lhs, rhs, ty)| {
            // The numeral at the relation's type, which Lean does not find
            // from the lemma's own.
            let numeral = match ty {
                Some(n) => Printed::cast((*lhs).clone(), LeanType::Num(*n)),
                None => (*lhs).clone(),
            };
            Printed::applied(
                "div_eq_mul_one_div",
                Source::Mathlib,
                vec![numeral, super::super::tactics::bracket((*rhs).clone())],
                LeanType::Prop,
            )
        })
        .collect()
}

/// A "for all" Lean states, `says`, proved by `proof`, read at the names
/// the claim is opened under, `intros` (`Writer::intros_now`): each of its
/// letters at the next name, and its guard, where it has one, at the guard's
/// name after it, `r1 x h_x`. The term and the body it proves; None where
/// `says` is no "for all" or its letters are not the names, in order.
pub(super) fn read_at_intros(
    proof: &Printed,
    says: &Printed,
    intros: &[String],
) -> Option<(Printed, Printed)> {
    use super::super::doc::{Arg, LeanType, Quant, TermKind};
    let mut body = says;
    let mut args = Vec::new();
    let mut names = intros.iter();
    while let TermKind::Quantified {
        quant: Quant::ForAll,
        letter,
        guard,
        body: inner,
        ..
    } = &body.kind
    {
        if names.next()? != letter {
            return None;
        }
        args.push(Arg::Explicit(super::super::tactics::hyp(letter)));
        if guard.is_some() {
            let guarded = names.next()?;
            if *guarded != format!("h_{letter}") {
                return None;
            }
            args.push(Arg::Explicit(super::super::tactics::hyp(guarded)));
        }
        body = inner;
    }
    if args.is_empty() || names.next().is_some() {
        return None;
    }
    let applied = Printed::of(
        TermKind::App {
            head: Box::new(proof.clone()),
            args,
            explicit: false,
        },
        LeanType::Prop,
    );
    Some((applied, body.clone()))
}

/// `by linarith only [facts]`, as a term. Where `split` holds disequalities
/// an order step takes both ways, each is split first:
/// `(Ne.lt_or_gt d).elim (fun h1 => …) (fun h1 => …)`, with h1, the order
/// each case gives, among the facts below it.
pub(super) fn split_linarith(split: &[Printed], facts: Vec<Printed>) -> Printed {
    use super::super::doc::{LeanType, Proof, Source, TacticArg, TermKind};
    use super::super::tactics as t;
    let Some((apart, rest)) = split.split_first() else {
        // A step resting on no line, `N ≤ N + 1`, is plain `linarith`:
        // with nothing to name, `only []` says nothing a reader needs.
        let args = match facts.is_empty() {
            true => Vec::new(),
            false => vec![TacticArg::Only, t::rules(facts)],
        };
        return t::by_term(Proof::By(t::call("linarith", args)));
    };
    let name = format!("h{}", split.len());
    let mut with = facts;
    with.push(t::hyp(&name));
    let case = Printed::of(
        TermKind::Lambda {
            letters: vec![name],
            body: Box::new(split_linarith(rest, with)),
        },
        LeanType::Prop,
    );
    let either = Printed::applied(
        "Ne.lt_or_gt",
        Source::Mathlib,
        vec![apart.clone()],
        LeanType::Prop,
    );
    Printed::applied(
        "Or.elim",
        Source::Mathlib,
        vec![either, case.clone(), case],
        LeanType::Prop,
    )
}

/// `(fun x : T => body)`: a function by its values, bracketed as an
/// argument.
pub(super) fn lambda(
    letter: &str,
    ty: super::super::doc::LeanType,
    body: Printed,
) -> Printed {
    use super::super::doc::LeanType;
    let to = body.ty.clone().unwrap_or(LeanType::Prop);
    let fun = Printed::of(
        super::super::doc::TermKind::Quantified {
            quant: super::super::doc::Quant::Fun,
            letter: letter.to_string(),
            letter_ty: ty.clone(),
            guard: None,
            body: Box::new(body),
            bounded: false,
        },
        LeanType::Fun {
            from: Box::new(ty),
            to: Box::new(to),
        },
    );
    super::super::tactics::bracket(fun)
}

/// `(fun x : A => ((f (x : B) : C) : D))`: a function of numbers taken at
/// the members a letter runs over, A, and its values cast up to the type
/// wanted, D, through the types it takes and gives, B and C.
pub(super) fn mapped_through(
    f: Printed,
    from: super::super::doc::LeanType,
    takes: super::super::templates::Num,
    gives: super::super::templates::Num,
    wanted: super::super::templates::Num,
) -> Printed {
    use super::super::doc::LeanType;
    let x = Printed::cast(super::super::tactics::hyp("x"), LeanType::Num(takes));
    let value = Printed::cast(applied_to(f, x), LeanType::Num(gives));
    lambda("x", from, Printed::cast(value, LeanType::Num(wanted)))
}

/// A function or proof applied to one more argument: `f a b` and `h`
/// give `f a b h`.
pub(super) fn applied_to(term: Printed, arg: Printed) -> Printed {
    match term.kind {
        super::super::doc::TermKind::App {
            head,
            mut args,
            explicit,
        } => {
            args.push(super::super::doc::Arg::Explicit(arg));
            Printed {
                kind: super::super::doc::TermKind::App {
                    head,
                    args,
                    explicit,
                },
                ty: None,
            }
        }
        kind => Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(Printed { kind, ty: term.ty }),
                args: vec![super::super::doc::Arg::Explicit(arg)],
                explicit: false,
            },
            ty: None,
        },
    }
}

/// `(h).mp p`: an "if and only if" read forwards, `premise` its left side.
pub(super) fn forwards_of(iff: Printed, premise: Printed) -> Printed {
    let mp = fields(super::super::tactics::bracket(iff), &["mp"]);
    applied_to(mp, premise)
}

/// The proof of a fact Lean proves as it stands, whatever line states it:
/// something in the whole of a type (`in_univ`); an order, an equation or
/// a disequality of numerals alone, worked out where it is asked as
/// `forms::meets` reads one (`norm_num`);
/// an equation whose two sides Lean writes alike, `a % b = a % b` of a
/// value the citation puts on both (`rfl`); `True`, what Lean writes of a
/// membership its types give (`trivial`); and a number's membership of the
/// number system it is in, which Lean writes as the number it is, `∃ m :
/// ℤ, (m : ℤ) = a - b` (`⟨_, rfl⟩`). None for any other statement.
pub(super) fn lean_truth(statement: &Printed) -> Option<Printed> {
    use super::super::doc::{LeanType, Quant, TermKind};
    if let Some(p) = in_univ(statement) {
        return Some(p);
    }
    if statement.is_truth() {
        return Some(super::super::tactics::by_term(
            super::super::doc::Proof::By(super::super::tactics::call(
                "trivial",
                vec![],
            )),
        ));
    }
    if let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        letter_ty: letter_ty @ LeanType::Num(_),
        guard: None,
        body,
        ..
    } = &bare_term(statement).kind
    {
        let is_letter = |t: &Printed| matches!(&bare_term(t).kind, TermKind::Letter(l) if l == letter);
        let named = match &bare_term(body).kind {
            TermKind::Infix { op, lhs, rhs } if op.symbol == "=" => {
                is_letter(lhs) && !rhs.walk().iter().any(|t| is_letter(t))
            }
            _ => false,
        };
        if named
            && super::super::doc::forms::relation_type(body).as_ref() == Some(letter_ty)
        {
            return Some(super::super::expr::anonymous(vec![
                Printed::of(TermKind::Elided, LeanType::Prop),
                Printed::constant(
                    "rfl",
                    super::super::doc::Source::Core,
                    LeanType::Prop,
                ),
            ]));
        }
    }
    if !statement.lettered()
        && matches!(
            relation_symbol(statement),
            Some("<" | "≤" | ">" | "≥" | "=" | "≠")
        )
    {
        return Some(norm_num_term());
    }
    match &bare_term(statement).kind {
        TermKind::Infix { op, lhs, rhs }
            if op.symbol == "=" && lhs.untyped() == rhs.untyped() =>
        {
            Some(Printed::constant(
                "rfl",
                super::super::doc::Source::Core,
                super::super::doc::LeanType::Prop,
            ))
        }
        _ => None,
    }
}

/// Whether `statement` is `0 ≤ x` of an x Lean writes as a natural number
/// cast up, `(Int.gcd s w : ℤ)`.
pub(super) fn natural_cast_bounded(statement: &Printed) -> bool {
    use super::super::doc::{LeanType, TermKind};
    let TermKind::Infix { op, rhs, .. } = &bare_term(statement).kind else {
        return false;
    };
    let cast_up = |t: &Printed| {
        matches!(&t.kind, TermKind::Cast { inner, .. }
            if inner.ty == Some(LeanType::Num(super::super::templates::Num::Nat)))
    };
    let mut x = &**rhs;
    while let TermKind::Paren(inner) = &x.kind {
        x = inner;
    }
    op.symbol == "≤" && cast_up(x)
}

/// The row of `rules::RANGE_WITHIN` putting a range that starts at `start`
/// inside `system`; None where no row does.
pub(super) fn range_row(
    system: Option<crate::rules::System>,
    start: &Node,
) -> Option<&'static crate::rules::RangeWithin> {
    let first = (start.notation() == crate::notations::NUMERAL)
        .then(|| start.text.parse::<u32>().ok())
        .flatten()
        .and_then(crate::rules::numeral_label);
    crate::rules::RANGE_WITHIN.iter().find(|row| {
        crate::rules::System::of_label(row.system) == system
            && (row.first.is_none() || row.first == first)
    })
}

/// The bound a member of a range has in the system holding it, from
/// `membership`, `k ∈ Icc a b` by `set_lemma` (`Finset.mem_Icc` or
/// `Set.mem_Icc`), and the numeral a's own bound: `lemma (by norm_num)
/// ((set_lemma.mp membership).1)`, `lemma` the row's of
/// `rules::RANGE_WITHIN`.
pub(super) fn range_bound(
    lemma: &str,
    set_lemma: &str,
    membership: Printed,
) -> Printed {
    let bounds = applied_to(
        fields(super::super::tactics::lemma(set_lemma), &["mp"]),
        membership,
    );
    Printed::applied(
        lemma,
        super::super::doc::Source::Mathlib,
        vec![
            norm_num_term(),
            fields(super::super::tactics::bracket(bounds), &["1"]),
        ],
        super::super::doc::LeanType::Prop,
    )
}

/// The proof of `wanted`, `∀ k ∈ {a, …, b}, P k` as Lean asks it, from
/// `proof` of a line saying it over a system holding the range
/// (`Supplied::narrowed`): `fun k h_k => h k (lemma (by norm_num)
/// (Finset.mem_Icc.mp h_k).1)`, the member's bound in the line's system
/// from the range's lower bound by the Lean lemma of the row of
/// `rules::RANGE_WITHIN` that puts the range in it; `fun k _ => h k` where
/// Lean's type gives the membership. None where the range starts at no
/// numeral, or no row relates the two sets.
pub(super) fn narrowed_proof(
    n: &crate::checker::record::Narrowed,
    proof: Printed,
    wanted: &Printed,
) -> Option<Printed> {
    use super::super::doc::{Quant, TermKind};
    use crate::notations::{INTEGER_RANGE, NUMBER_SYSTEMS};
    let TermKind::Quantified {
        quant: Quant::ForAll,
        letter,
        letter_ty,
        ..
    } = &bare_term(wanted).kind
    else {
        return None;
    };
    let ([start, _], true, true) = (
        n.to.children.as_slice(),
        n.to.notation() == INTEGER_RANGE,
        n.from.notation() == NUMBER_SYSTEMS,
    ) else {
        return None;
    };
    let row = range_row(crate::rules::System::of_sign(&n.from.text), start)?;
    let h = format!("h_{letter}");
    let at = applied_to(proof, Printed::letter(letter, letter_ty.clone()));
    let (letters, body) = match row.lean {
        Some(lemma) => {
            let member =
                range_bound(lemma, "Finset.mem_Icc", super::super::tactics::hyp(&h));
            (
                vec![letter.clone(), h],
                applied_to(at, super::super::tactics::bracket(member)),
            )
        }
        None => (vec![letter.clone(), "_".to_string()], at),
    };
    Some(Printed {
        kind: TermKind::Lambda {
            letters,
            body: Box::new(body),
        },
        ty: None,
    })
}

/// The lines whose numbers `term` names, the h of each `Classical.choose
/// h`, each once.
pub(super) fn chosen_witnesses(term: &Printed) -> Vec<Printed> {
    use super::super::doc::{Arg, TermKind};
    let mut out: Vec<Printed> = Vec::new();
    for t in term.walk() {
        if let TermKind::App { head, args, .. } = &t.kind {
            if let ([Arg::Explicit(h)], true) =
                (args.as_slice(), is_constant(head, "Classical.choose"))
            {
                if !out.iter().any(|o| o.untyped() == h.untyped()) {
                    out.push(h.clone());
                }
            }
        }
    }
    out
}

/// The membership the claim's own "for all" gives its letter, as the page
/// writes the letter: the hypothesis Lean introduces with it, `h_t`
/// (`peel`).
pub(super) fn bound_proof(letter: &str) -> Printed {
    super::super::tactics::hyp(&format!("h_{}", super::super::names::letter(letter)))
}

/// A "there is" Lean asks, read as its witness and what it asks of the
/// witness (`number_member`, `member_named`).
pub(super) struct Witnessed {
    /// The witness, `N` of `∃ m : ℤ, 0 ≤ m ∧ (m : ℤ) = N`.
    pub(super) witness: Printed,
    /// What is asked of it, `0 ≤ N`.
    pub(super) asked: Printed,
}

/// `statement` read as `Witnessed` where it is a membership of a number
/// system Lean writes as the number it is with what the system asks of
/// it, `∃ m : T, P m ∧ (m : T) = t`, t free of m; None for any other
/// statement.
pub(super) fn number_member(statement: &Printed) -> Option<Witnessed> {
    use super::super::doc::{Quant, TermKind};
    let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        guard,
        body,
        ..
    } = &bare_term(statement).kind
    else {
        return None;
    };
    // What is asked of m, as the condition on it or the first side of
    // the body's "and".
    let (asked, named) = match guard {
        Some(g) => ((**g).clone(), (**body).clone()),
        None => and_sides(body)?,
    };
    let TermKind::Infix { op, lhs, rhs } = &bare_term(&named).kind else {
        return None;
    };
    let is_letter =
        |t: &Printed| matches!(&bare_term(t).kind, TermKind::Letter(l) if l == letter);
    if op.symbol != "=" || !is_letter(lhs) || rhs.walk().iter().any(|t| is_letter(t)) {
        return None;
    }
    let number = bare_term(rhs).clone();
    Some(Witnessed {
        asked: asked.substituted(&std::collections::BTreeMap::from([(
            letter.clone(),
            number.clone(),
        )])),
        witness: number,
    })
}

/// `wanted` read as `Witnessed` where it says a set has a member, `∃ s ∈
/// S, True`, and `says` names one, `a ∈ S`: the witness a, asked `a ∈ S`
/// as Lean writes the set. None for any other two.
pub(super) fn member_named(wanted: &Printed, says: &Printed) -> Option<Witnessed> {
    use super::super::doc::{Quant, TermKind};
    let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        guard: Some(guard),
        body,
        ..
    } = &bare_term(wanted).kind
    else {
        return None;
    };
    let TermKind::Infix { op, lhs, .. } = &bare_term(says).kind else {
        return None;
    };
    if !body.is_truth() || op.symbol != "∈" {
        return None;
    }
    let witness = bare_term(lhs).clone();
    Some(Witnessed {
        asked: guard.substituted(&std::collections::BTreeMap::from([(
            letter.clone(),
            witness.clone(),
        )])),
        witness,
    })
}

/// The proof of `statement` where it says only that something is in the
/// whole of a type, which holds of anything in Lean: a map into it,
/// `Set.MapsTo f X Set.univ` (`Set.mapsTo_univ`); a member of it, `t ∈
/// Set.univ` (`Set.mem_univ`); and that of each member of a set, `∀ x ∈ D,
/// f x ∈ Set.univ`. None for any other statement. The page's set is one
/// the citation leaves open or gives as a number system, which Lean writes
/// as the whole of its type.
pub(super) fn in_univ(statement: &Printed) -> Option<Printed> {
    use super::super::doc::{LeanType, Quant, TermKind};
    let elided = || Printed::of(TermKind::Elided, LeanType::Prop);
    let lemma = |name: &str, args: usize| {
        Printed::applied(
            name,
            super::super::doc::Source::Mathlib,
            (0..args).map(|_| elided()).collect(),
            LeanType::Prop,
        )
    };
    if maps_to_codomain(statement).is_some_and(|to| is_constant(to, "Set.univ")) {
        return Some(lemma("Set.mapsTo_univ", 2));
    }
    match &bare_term(statement).kind {
        TermKind::Infix { op, rhs, .. }
            if op.symbol == "∈" && is_constant(rhs, "Set.univ") =>
        {
            Some(lemma("Set.mem_univ", 1))
        }
        TermKind::Quantified {
            quant: Quant::ForAll,
            letter,
            guard: Some(_),
            body,
            ..
        } => {
            in_univ(body)?;
            let shown = Tactic::Seq(vec![
                Tactic::Intro(vec![letter.clone(), "_".to_string()]),
                Tactic::Exact(lemma("Set.mem_univ", 1)),
            ]);
            matches!(&bare_term(body).kind, TermKind::Infix { .. }).then(|| {
                super::super::tactics::by_term(super::super::doc::Proof::By(shown))
            })
        }
        _ => None,
    }
}

/// The term inside its brackets and type ascriptions.
pub(super) fn bare_term(t: &Printed) -> &Printed {
    match &t.kind {
        super::super::doc::TermKind::Paren(inner)
        | super::super::doc::TermKind::Cast { inner, .. } => bare_term(inner),
        _ => t,
    }
}
