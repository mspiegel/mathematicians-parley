//! What a step proves and how it cites.

use super::*;

/// A line of a proof as the writer pushes it, which may hold several of the
/// file's lines, and what it was written for; its line number is set where
/// the file is put together.
pub(super) struct ProofLine {
    /// How deep in the proof's blocks it stands.
    pub(super) depth: usize,
    pub(super) tactic: Tactic,
    pub(super) origin: Origin,
}

/// One sentence of a line the page can cite, with the Lean name of its
/// proof.
#[derive(Clone, Debug)]
pub(super) struct LineSentence {
    /// Its place among the sentences the line writes, from 0, as the
    /// checker counts a cited line's sentences (`FirstAt::sentence`).
    pub(super) at: usize,
    pub(super) node: Node,
    /// The Lean name the sentence is proved under, a hypothesis or a
    /// `have`; None for one proved as a projection of another's, a sentence
    /// of a line that says several.
    pub(super) name: Option<String>,
    /// The term that proves it: its name, or the projection, `hA1.2.1`.
    pub(super) proof: Printed,
    /// What it says in Lean, as written where the line is stated
    /// (`Proof::stated`), so that every reading of the line reads it so;
    /// None where the writer there could not write it.
    pub(super) says: Option<Printed>,
}

impl LineSentence {
    /// A sentence proved under the name `name`.
    pub(super) fn named(at: usize, node: Node, name: String) -> LineSentence {
        LineSentence {
            at,
            node,
            proof: super::super::tactics::hyp(&name),
            name: Some(name),
            says: None,
        }
    }

    /// A line's one sentence.
    pub(super) fn only(node: Node, name: String) -> LineSentence {
        LineSentence::named(0, node, name)
    }

    /// The sentence with the term that proves it.
    pub(super) fn cited(&self) -> super::super::algebra::Cited {
        super::super::algebra::Cited {
            node: self.node.clone(),
            proof: self.proof.clone(),
            says: self.says.clone(),
        }
    }
}

/// How what a block owes is proved from its last step's lines
/// (`Proof::proved_from`).
pub(super) enum Proved {
    /// By this term.
    Term(Printed),
    /// By the line `line`, once the goal and it are rewritten by Mathlib's
    /// lemmas `rules`.
    Simplified {
        rules: Vec<&'static str>,
        line: Printed,
    },
    /// By the line `line`, its casts and the goal's moved alike by `by`,
    /// once each is rewritten by the `set` equations its letters name
    /// (`forms::CastsApart`).
    Cast {
        apart: super::super::doc::forms::CastsApart,
        by: CastsBy,
        line: Printed,
    },
    /// By the line `line`, the two apart in casts the cast table does not
    /// say one tactic moves: both pushed down to the letters, where in one
    /// type they are one statement; where the line is in a narrower type
    /// (`CastsApart::lift`), it is then lifted to the goal's. Each side is
    /// first rewritten by the `set` equations its letters name, as
    /// `Proved::Cast` rewrites them.
    Unsettled {
        line: Printed,
        apart: super::super::doc::forms::CastsApart,
        /// Whether the claim names no letter (`no_letter`): pushing the
        /// casts would work it out by itself, so it is worked out whole.
        numerals: bool,
    },
}

/// The tactic that moves the casts of a line and a goal apart only in them,
/// by what the cast table says of both (`cast_proved`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CastsBy {
    /// `exact_mod_cast`: `norm_cast` moves every cast of both, and so
    /// brings them to one form, a line in a narrower type than the goal's
    /// among them.
    NormCast,
    /// `push_cast at h ⊢; exact h`: `push_cast` moves every cast of both to
    /// the letters and numerals and `norm_cast` does not, a numeral
    /// quotient among them, and neither is in a narrower type.
    PushCast,
}

/// The proof of `wanted` from `line`, which says `says`, the two apart only
/// in casts (`apart`): by whichever of `norm_cast` and `push_cast` the cast
/// table says moves every cast of both; by the ways tried in order where
/// neither does, or where only `push_cast` does and the line is in a
/// narrower type, which it does not lift.
pub(super) fn cast_proved(
    apart: super::super::doc::forms::CastsApart,
    line: Printed,
    says: &Printed,
    wanted: &Printed,
) -> Option<Proved> {
    use super::super::casts::{norm_cast_moves_all, push_cast_moves_all_in_sides};
    // A line whose numbers are of a narrower field than the goal's, under
    // its "for all"s as well, ℚ for ℝ, is lifted to it.
    // A relation of ℚ for the same of ℝ: by ℚ's lemma for it, as
    // `norm_cast` does not take a fact of ℚ with no cast to ℝ up to it.
    if rat_crossing(says, wanted) {
        if let Some(lifted) = rat_lifted(line.clone(), says) {
            return Some(Proved::Term(lifted));
        }
    }
    let fields = super::super::spelling::fields_of;
    let mut apart = apart;
    apart.lift |= fields(says).last() < fields(wanted).last();
    let by = if norm_cast_moves_all(says) && norm_cast_moves_all(wanted) {
        CastsBy::NormCast
    } else if !apart.lift
        && push_cast_moves_all_in_sides(says)
        && push_cast_moves_all_in_sides(wanted)
    {
        CastsBy::PushCast
    } else {
        return Some(Proved::Unsettled {
            line,
            apart,
            numerals: no_letter(wanted),
        });
    };
    Some(Proved::Cast { apart, by, line })
}

impl Proved {
    /// The tactic that closes the goal by it: `exact` of a term.
    pub(super) fn closer(&self) -> Tactic {
        use super::super::tactics as t;
        match self {
            Proved::Term(term) => Tactic::Exact(term.clone()),
            Proved::Simplified { rules, line } => {
                t::simpa_only(rules.clone(), line.clone())
            }
            // Casts the table does not say one tactic moves: both pushed down
            // to the letters, where in one type they are one statement; a
            // line in a narrower type is then lifted to the goal's. Lifting
            // where neither is narrower would read a division of casts one
            // way on one side and another on the other. A claim of numerals
            // alone, which the pushing would work out by itself, is worked
            // out whole with the line put in the goal.
            Proved::Unsettled {
                line,
                apart,
                numerals,
            } => {
                let rewrite = |by: &[String], at: super::super::doc::Location| {
                    t::call(
                        "rw",
                        vec![
                            t::rules(by.iter().map(|e| t::hyp(e)).collect()),
                            TacticArg::At(vec![at]),
                        ],
                    )
                };
                let mut steps = Vec::new();
                if !apart.at_given.is_empty() {
                    steps.push(rewrite(
                        &apart.at_given,
                        super::super::doc::Location::Hypothesis("h".to_string()),
                    ));
                }
                if !apart.at_line.is_empty() {
                    steps.push(rewrite(
                        &apart.at_line,
                        super::super::doc::Location::Goal,
                    ));
                }
                if *numerals {
                    steps.push(t::call("revert", vec![TacticArg::Term(t::hyp("h"))]));
                    steps.push(t::call("norm_num", vec![]));
                    return t::on_h(line, steps);
                }
                let last = match apart.lift {
                    true => t::exact_mod_cast(t::hyp("h")),
                    false => Tactic::Exact(t::hyp("h")),
                };
                steps.push(t::push_cast(Some(t::at_h(true))));
                steps.push(last);
                t::on_h(line, steps)
            }
            // Each side rewritten by the `set` equations its letters name, and
            // then the casts moved by the tactic the cast table gives
            // (`CastsBy`).
            Proved::Cast { apart, by, line } => {
                let super::super::doc::TermKind::Letter(name) = &line.kind else {
                    return match by {
                        CastsBy::NormCast => t::exact_mod_cast(line.clone()),
                        CastsBy::PushCast => t::on_h(
                            line,
                            vec![
                                t::push_cast(Some(t::at_h(true))),
                                Tactic::Exact(t::hyp("h")),
                            ],
                        ),
                    };
                };
                let rewrite = |by: &[String], at: Vec<super::super::doc::Location>| {
                    t::call(
                        "rw",
                        vec![
                            t::rules(by.iter().map(|e| t::hyp(e)).collect()),
                            TacticArg::At(at),
                        ],
                    )
                };
                let mut steps = Vec::new();
                if !apart.at_given.is_empty() {
                    let at =
                        vec![super::super::doc::Location::Hypothesis(name.clone())];
                    steps.push(rewrite(&apart.at_given, at));
                }
                if !apart.at_line.is_empty() {
                    steps.push(rewrite(
                        &apart.at_line,
                        vec![super::super::doc::Location::Goal],
                    ));
                }
                match by {
                    CastsBy::NormCast => steps.push(t::exact_mod_cast(line.clone())),
                    CastsBy::PushCast => {
                        let both = vec![
                            super::super::doc::Location::Hypothesis(name.clone()),
                            super::super::doc::Location::Goal,
                        ];
                        steps.push(t::push_cast(Some(TacticArg::At(both))));
                        steps.push(Tactic::Exact(line.clone()));
                    }
                }
                match steps.len() {
                    1 => steps.remove(0),
                    _ => Tactic::Seq(steps),
                }
            }
        }
    }

    /// As a term: a tactic's proof standing as `by t`.
    pub(super) fn term(self) -> Printed {
        match self {
            Proved::Term(t) => t,
            other => super::super::tactics::by_term(super::super::doc::Proof::By(
                other.closer(),
            )),
        }
    }
}

/// The goal left once `intro` has taken `names` binders off it, as Lean
/// takes them: a "for all"'s letter, then its guard, `∀ j, 0 < j → P` to
/// `0 < j → P` and then P, and an "if", `A → B` to B. None where the goal
/// has fewer binders.
pub(super) fn goal_after_intros(goal: &Printed, names: usize) -> Option<Printed> {
    use super::super::doc::{LeanType, Op, TermKind};
    let mut goal = goal.clone();
    let mut left = names;
    while left > 0 {
        let bare = match goal.kind {
            TermKind::Paren(inner) => *inner,
            _ => goal,
        };
        left -= 1;
        goal = match bare.kind {
            TermKind::Infix { op, rhs, .. } if op.symbol == "→" => *rhs,
            TermKind::Quantified {
                guard: Some(guard),
                body,
                ..
            } => Printed::infix(Op::of("→")?, *guard, *body, LeanType::Prop),
            TermKind::Quantified { body, .. } => *body,
            _ => return None,
        };
    }
    Some(goal)
}

/// The atoms `ring1` and `linarith` read a statement over: each greatest
/// part that is no sum, difference, product, quotient, negation, numeral,
/// cast or power to a natural exponent, as `push_cast` leaves the casts
/// (`casts::norm_cast_form`). `ring` normalises only the arithmetic between
/// atoms, and an atom is compared as it is written, so
/// `choose (m + 1 - 0) 1` and `choose (m + 1) 1` are two. The exponent of a
/// power is an atom unless it is a numeral.
pub(super) fn ring_atoms(term: &Printed, out: &mut Vec<Printed>) {
    use super::super::doc::TermKind;
    match &term.kind {
        TermKind::Numeral(_) => {}
        // An instance's conditions met stand as `True` beside its statement,
        // `True ∧ L p ≤ U p`, whose parts `linarith` takes apart.
        _ if term.is_truth() => {}
        TermKind::Cast { inner, .. }
        | TermKind::Paren(inner)
        | TermKind::Neg(inner) => ring_atoms(inner, out),
        TermKind::Infix { op, lhs, rhs }
            if matches!(
                op.symbol,
                "+" | "-" | "*" | "/" | "=" | "≠" | "<" | ">" | "≤" | "≥" | "∧"
            ) =>
        {
            ring_atoms(lhs, out);
            ring_atoms(rhs, out);
        }
        // A natural exponent is arithmetic `ring` takes apart as well, x^(m
        // + n) as x^m·x^n: its atoms are the exponent's. An integer one,
        // Lean's integer power, `ring` keeps whole unless a numeral.
        TermKind::Infix { op, lhs, rhs } if op.symbol == "^" => {
            ring_atoms(lhs, out);
            let natural = rhs.ty
                == Some(super::super::doc::LeanType::Num(
                    super::super::templates::Num::Nat,
                ));
            if natural {
                ring_atoms(rhs, out);
            } else if !matches!(
                super::super::casts::norm_cast_form(rhs).kind,
                TermKind::Numeral(_)
            ) {
                out.push(super::super::casts::norm_cast_form(rhs));
            }
        }
        _ => out.push(super::super::casts::norm_cast_form(term)),
    }
}

/// Whether the two statements are over the same atoms (`ring_atoms`), each
/// of the one alike one of the other with the `set` letters read as their
/// values and bound letters renamed (`forms::alike_once_set`), as Lean
/// takes them.
pub(super) fn same_ring_atoms(
    one: &Printed,
    other: &Printed,
    values: &super::super::doc::forms::Values,
) -> bool {
    // Each read with its `toNat`s taken apart (`to_nat_read`).
    let (mut a, mut b) = (Vec::new(), Vec::new());
    ring_atoms(&to_nat_read(one), &mut a);
    ring_atoms(&to_nat_read(other), &mut b);
    let within = |xs: &[Printed], ys: &[Printed]| {
        xs.iter().all(|x| {
            ys.iter()
                .any(|y| super::super::doc::forms::alike_once_set(x, y, values))
        })
    };
    within(&a, &b) && within(&b, &a)
}

/// The casts a statement as Lean writes it takes, each by its text, a cast
/// of a term to its own type left out, in order.
pub(super) fn cast_texts(term: &Printed) -> Vec<String> {
    term.walk()
        .into_iter()
        .filter(|t| match &t.kind {
            super::super::doc::TermKind::Cast { inner, to } => {
                inner.ty.as_ref() != Some(to)
            }
            _ => false,
        })
        .map(|t| t.untyped().text())
        .collect()
}

/// How the checker met one conclusion of a citation with the claim.
#[derive(Clone, Copy)]
pub(super) struct HowMet<'m> {
    /// Which way the item's equation faces the claim (`Cited::facings`).
    pub(super) facing: Option<Facing>,
    /// What was taken to meet them: identities dropped, parts paired out of
    /// their places (`Cited::meetings`).
    pub(super) meeting: Option<&'m crate::matching::Meeting>,
}

/// An equation a substitution puts in that no line says, as Lean has it:
/// a row's change, proved by its reason, `c2 : 3 * 3 + 3 = 12`, put into
/// the row above (`SubstitutedInto::RowAbove`); or a step's own equation,
/// worked out by arithmetic or a define's, put where the record says.
pub(super) struct GivenEquation {
    /// The equation, its proof and what Lean states for it.
    pub(super) change: super::super::algebra::Cited,
    /// The row above, by its name and what it says, for a row's change.
    pub(super) above: Option<super::super::algebra::Cited>,
}

/// The two terms of a substitution: the one put for, and the one put in
/// its place.
#[derive(Clone, Copy)]
pub(super) struct PutTerms<'n> {
    pub(super) was: &'n Node,
    pub(super) now: &'n Node,
}

/// The claim a citation is met with, as Lean prints it.
#[derive(Clone, Copy)]
pub(super) struct StepClaim<'p> {
    pub(super) printed: &'p Printed,
    /// Whether it is the `have` the step states, which shows the form its
    /// counts are in; a claim printed afresh does not.
    pub(super) stated: bool,
}

/// How an item's statement at a citation's values reads as the claim where
/// the item is stated over more than its values are in, as the record's
/// `Cited::item_letters` say: the lemmas `simpa only` takes it by, or the
/// cast `exact_mod_cast` moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CitedBridge {
    Rules(Vec<&'static str>),
    Cast,
}

/// The bridge the record's `item_letters` give a citation of `sentence`
/// (`CitedBridge`); None where every letter's value is in what the item
/// takes it in. Each row is a Lean fact, checked in `CloserTable.lean`:
/// - a set letter given ℕ or ℕ₀, `m ∈ {n : ℤ | 0 < n}` for `0 < m`:
///   `Set.mem_ofPred_eq`, and `Set.mem_sep_iff` for a set-builder over it;
/// - a set letter given a whole type, `∀ x ∈ Set.univ` for `∀ x`:
///   `Set.mem_univ`, `true_implies`;
/// - an item over any ring at integers, ℕ₀ said `∃ m : ℤ, 0 ≤ m ∧ m = n`:
///   `Int.cast_id`, `exists_eq_right`;
/// - an item stated in ℂ at reals, or in ℝ at rationals: the cast,
///   `Complex.ofReal_*` and `Rat.cast_*`, by `exact_mod_cast`.
pub(super) fn cited_bridge(
    cited: &Cited,
    sentence: &Sentence,
    at: &Cites,
) -> Option<CitedBridge> {
    use super::super::templates::Num;
    use crate::rules::System;
    // A claim naming a letter a `set` gives, `b ∈ T`, reads as the item
    // only once the letter is its value, which `simpa only` does not do.
    if at.names_set_letter {
        return None;
    }
    let mut rules: Vec<&'static str> = Vec::new();
    // A set letter given a number system: the set-builder, the system as a
    // set, and `Set.univ` read as membership, all at once, as one step may
    // ask several (`t ∈ {t ∈ Set.univ | P t}`).
    // Only where the item's sentence reads each such letter as a set its
    // members belong to (`read_as_members`): the lemmas read membership,
    // and an image `f '' (X ∩ Y)` they leave as it stands.
    let sets: Vec<_> = cited
        .item_letters
        .iter()
        .filter(|l| l.value_set.is_some())
        .collect();
    if !sets.is_empty() {
        if !sets
            .iter()
            .all(|l| read_as_members(&sentence.says, l.letter))
        {
            return None;
        }
        rules.extend([
            "Set.mem_sep_iff",
            "Set.mem_ofPred_eq",
            "Set.mem_univ",
            "Filter.univ_mem",
            "true_and",
            "true_implies",
        ]);
    }
    // An item over any ring at integers, where the claim is a membership of
    // ℕ or ℕ₀, which the item says `∃ m : ℤ, 0 ≤ m ∧ (m : ℤ) = n`.
    let integers = cited
        .item_letters
        .iter()
        .filter_map(|l| l.value_system)
        .all(|v| v.within(System::Z));
    if sentence.general.is_some() && integers && at.claims_natural {
        rules.extend(["Int.cast_id", "exists_eq_right"]);
    }
    rules.sort_unstable();
    rules.dedup();
    if !rules.is_empty() {
        return Some(CitedBridge::Rules(rules));
    }
    // An item stated in ℂ for a claim Lean states in ℝ, or in ℝ for one in
    // ℚ, the item's letters at values of the claim's field: the cast.
    // `norm_cast` moves a cast out through a function only of a cast,
    // `Complex.exp ↑x` to `↑(Real.exp x)`: a value that is a numeral alone,
    // `Complex.exp 1`, stands at the wider type with no cast to move, so
    // each widened letter's value is one with a letter in it.
    let mut widened = false;
    for l in &cited.item_letters {
        if matches!(
            (l.item_system, l.value_system),
            (Some(System::C | System::R), Some(v)) if Some(v) != l.item_system
        ) {
            if cited
                .binding
                .get(&l.letter)
                .is_none_or(|v| v.names().is_empty())
            {
                return None;
            }
            widened = true;
        }
    }
    let crossed = matches!(
        at.types,
        (Some(Num::Complex), Some(Num::Real)) | (Some(Num::Real), Some(Num::Rat))
    );
    (sentence.general.is_none() && widened && crossed && at.casts_move)
        .then_some(CitedBridge::Cast)
}

/// Whether every place `says` names the letter `set` is the set something
/// belongs to: of `x ∈ X`, `for all x ∈ X`, `there is x ∈ X` or
/// `{t ∈ X | P}`, each of which holds it second.
pub(super) fn read_as_members(
    says: &Node,
    set: crate::formula::symbol::Symbol,
) -> bool {
    use crate::notations::{FOR_ALL, MEMBERSHIP, SET_BUILDER, THERE_IS};
    let holds = matches!(
        says.notation(),
        MEMBERSHIP | FOR_ALL | THERE_IS | SET_BUILDER
    );
    says.children.iter().enumerate().all(|(i, c)| {
        if c.is_name() && c.text == set {
            holds && i == 1
        } else {
            read_as_members(c, set)
        }
    })
}

/// What a citation's claim says that `cited_bridge` reads: the page's claim
/// and the two statements as the writer states them.
pub(super) struct Cites {
    /// The claim names a letter a `set` gives.
    pub(super) names_set_letter: bool,
    /// The claim is a membership of ℕ or ℕ₀.
    pub(super) claims_natural: bool,
    /// The number types the item's statement and the claim are stated in.
    pub(super) types: (
        Option<super::super::templates::Num>,
        Option<super::super::templates::Num>,
    ),
    /// The cast table says `norm_cast` moves every cast of both
    /// (`casts::norm_cast_moves_all`).
    pub(super) casts_move: bool,
}

impl Cites {
    pub(super) fn of(
        node: &Node,
        says: Option<&Printed>,
        claim: Option<&Printed>,
        values: &super::super::doc::forms::Values,
    ) -> Cites {
        use super::super::doc::LeanType;
        let num = |t: Option<&Printed>| match t
            .and_then(super::super::doc::forms::relation_type)
        {
            Some(LeanType::Num(n)) => Some(n),
            _ => None,
        };
        let names_set_letter =
            node.names().iter().any(|n| values.contains_key(n.as_str()));
        let claims_natural = node.notation() == crate::notations::MEMBERSHIP
            && node.children.get(1).is_some_and(|set| {
                set.notation() == crate::notations::NUMBER_SYSTEMS
                    && matches!(
                        crate::rules::System::of_sign(&set.text),
                        Some(crate::rules::System::N | crate::rules::System::N0)
                    )
            });
        let moves = |t: Option<&Printed>| {
            t.is_some_and(super::super::casts::norm_cast_moves_all)
        };
        Cites {
            names_set_letter,
            claims_natural,
            types: (num(says), num(claim)),
            casts_move: moves(says) && moves(claim),
        }
    }
}

/// Whether the statement raises to a complex exponent, `↑x ^ ↑y` in ℂ: that
/// power is the real one only at a base not negative, a fact no cast moves,
/// so an item in ℂ written with one is not read at reals.
pub(super) fn complex_exponent(term: &Printed) -> bool {
    use super::super::doc::{LeanType, Op, TermKind};
    let complex = Some(LeanType::Num(super::super::templates::Num::Complex));
    term.walk().iter().any(|t| {
        matches!(&t.kind, TermKind::Infix { op, rhs, .. }
            if *op == Op::POWER && rhs.ty == complex)
    })
}

/// Whether the step's lines' writing of an item's part, `written`, and Lean's
/// statement of it, `said`, are one statement: written alike and naming the
/// same number types. An item with no letter is stated in one type,
/// `(abs 0 : ℤ) = 0`, which a calculation's row in ℝ writes alike, and the
/// two are then read one as the other by the bridge.
pub(super) fn one_statement(written: &Printed, said: &Printed) -> bool {
    super::super::doc::forms::written_alike(written, said)
        && number_types(written) == number_types(said)
}

/// How many integer powers the statement writes under its binders, x^(m − k)
/// in a sum over k, whose exponent's fact holds only there: two statements
/// of one fact that write as many have spelt each such power alike, none
/// taken to `toNat` on one side alone, which the reading of the item
/// (`spelling::read_as_written`) has no fact to join.
pub(super) fn integer_powers_under_binders(term: &Printed) -> usize {
    use super::super::doc::{LeanType, Op, TermKind};
    let int = Some(LeanType::Num(super::super::templates::Num::Int));
    match &term.kind {
        TermKind::Quantified { .. }
        | TermKind::Bound { .. }
        | TermKind::Lambda { .. } => term
            .walk()
            .iter()
            .filter(|t| {
                matches!(&t.kind, TermKind::Infix { op, rhs, .. }
                    if *op == Op::POWER && rhs.ty == int)
            })
            .count(),
        _ => term
            .children()
            .into_iter()
            .map(integer_powers_under_binders)
            .sum(),
    }
}

/// The statement with each `toNat` read as `ring_combination`'s `simp
/// only` reads it, by the Lean facts it takes them apart by:
/// - of numerals alone, the numeral it works out to (`Int.reduceToNat`),
///   `(2 : ℤ).toNat` as `2`;
/// - of a sum, the sum of the parts' (`Int.toNat_add`), and of a product,
///   the product of the parts' (`Int.toNat_mul`);
/// - of a natural number written in ℤ, that number (`casts::as_natural`,
///   `Int.toNat_natCast`).
///
/// The writer writes `(t).toNat` only of a term the said-once rule puts in
/// ℕ₀ (`Writer::said_whole`), which puts a sum or a product there by its
/// parts: the facts 0 ≤ a and 0 ≤ b these two ask hold, and `omega`, the
/// `simp`'s discharger, reads them. A difference's `toNat` stays whole: subtraction in
/// ℕ stops at 0.
pub(super) fn to_nat_read(term: &Printed) -> Printed {
    use super::super::doc::{LeanType, TermKind};
    use super::super::templates::Num;
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = to_nat_read(c);
    }
    let TermKind::ToNat(inner) = &out.kind else {
        return out;
    };
    if let Some(natural) = super::super::casts::as_natural(inner) {
        return natural;
    }
    if !inner.lettered() {
        return super::super::doc::forms::ascriptions_dropped(inner);
    }
    match &super::super::doc::forms::ascriptions_dropped(inner).kind {
        TermKind::Infix { op, lhs, rhs } if matches!(op.symbol, "+" | "*") => {
            let part = |p: &Printed| {
                to_nat_read(&Printed::of(
                    TermKind::ToNat(Box::new(p.clone())),
                    LeanType::Num(Num::Nat),
                ))
            };
            Printed::infix(*op, part(lhs), part(rhs), LeanType::Num(Num::Nat))
        }
        _ => out,
    }
}

/// Whether a relation is between terms of ℕ∞, counts of sets not known
/// finite.
pub(super) fn in_extended(relation: &Printed) -> bool {
    match &unparenthesized(relation).kind {
        super::super::doc::TermKind::Infix { lhs, rhs, .. } => [lhs, rhs]
            .iter()
            .any(|s| s.ty == Some(super::super::doc::LeanType::ENat)),
        _ => false,
    }
}

/// `linear_combination proof` of a claim stated `wanted` from a line stated
/// `says`, each first brought to the atoms `ring1` reads alike
/// (`same_ring_atoms`): its `toNat`s of sums, products and numerals taken
/// apart where it has one (`to_nat_read`), by the facts 0 ≤ a in scope, and
/// its casts pushed in where it casts a compound term (`casts_compound`).
/// The line is named `h` where it is changed.
pub(super) fn ring_combination(
    proof: &Printed,
    says: &Printed,
    wanted: &Printed,
) -> Tactic {
    use super::super::doc::Location;
    use super::super::tactics as t;
    let to_nat = |p: &Printed| to_nat_read(p).untyped() != p.untyped();
    let places = |test: &dyn Fn(&Printed) -> bool| {
        let mut at = Vec::new();
        if test(says) {
            at.push(Location::Hypothesis("h".to_string()));
        }
        if test(wanted) {
            at.push(Location::Goal);
        }
        at
    };
    let mut steps = Vec::new();
    let nat_at = places(&to_nat);
    if !nat_at.is_empty() {
        steps.push(t::simp_only(
            false,
            Some(t::call("omega", vec![])),
            ["Int.toNat_add", "Int.toNat_mul", "Int.reduceToNat"]
                .into_iter()
                .map(|l| t::forwards(t::lemma(l)))
                .collect(),
            Some(TacticArg::At(nat_at)),
        ));
    }
    let cast_at = places(&casts_compound);
    if !cast_at.is_empty() {
        steps.push(t::push_cast(Some(TacticArg::At(cast_at))));
    }
    if steps.is_empty() {
        return t::linear_combination(proof.clone());
    }
    steps.push(t::linear_combination(t::hyp("h")));
    t::on_h(proof, steps)
}

/// The statement with each `toNat` of a natural number written in ℤ read
/// as that number (`casts::as_natural`), `((a : ℤ) * (b : ℤ)).toNat` as `a
/// * b`, as `norm_cast` reads it by `Int.toNat_natCast`; every other
/// `toNat` left.
pub(super) fn naturals_read(term: &Printed) -> Printed {
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = naturals_read(c);
    }
    if let super::super::doc::TermKind::ToNat(inner) = &out.kind {
        if !matches!(
            unparenthesized(inner).kind,
            super::super::doc::TermKind::ToNat(_)
        ) {
            if let Some(natural) = super::super::casts::as_natural(inner) {
                return natural;
            }
        }
    }
    out
}

/// The `toNat`s a statement as Lean writes it takes, each by its text, in
/// order, taken apart (`to_nat_read`), with no
/// ascription of a term to its own type and its bound letters renamed in
/// order (`forms::bound_renamed`).
pub(super) fn to_nat_texts(term: &Printed) -> Vec<String> {
    use super::super::doc::TermKind;
    let read = super::super::doc::forms::bound_renamed(
        &super::super::doc::forms::ascriptions_dropped(&to_nat_read(term)),
    );
    read.walk()
        .into_iter()
        .filter(|t| match &t.kind {
            TermKind::ToNat(inner) => inner.lettered(),
            _ => false,
        })
        .map(|t| t.untyped().text())
        .collect()
}

/// The proof of `claim` from `term`, whose statement `says` is worked in ℂ
/// beyond the claim's fields, taken down to it: each complex operation
/// read as the real one (`spelling::read_from_complex`). None where it
/// names no wider field, or only ℝ, which the step meets by its other ways.
pub(super) fn read_down(
    term: &Printed,
    says: &Printed,
    claim: &Printed,
) -> Option<Tactic> {
    use super::super::templates::Num;
    let claimed = fields_of(claim);
    let wider = fields_of(says)
        .into_iter()
        .filter(|n| !claimed.contains(n))
        .max();
    match wider {
        Some(Num::Complex) => {
            Some(super::super::spelling::read_from_complex(term, says))
        }
        _ => None,
    }
}
