//! Paths, conjuncts, intros and the conversions a citation needs.

use std::collections::{BTreeMap, BTreeSet};

use super::super::doc::bridges::BridgeModule;
use super::super::doc::{Arg, LeanType, Op, Quant, Source, TermKind};
use super::super::templates::Num;
use super::super::{doc, tactics as t};
use super::*;
use crate::formula::notation::Binds;
use crate::formula::notation_id::NotationId;
use crate::formula::page;
use crate::matching;
use crate::matching::{Binding, FxIndexMap, Meeting};
use crate::notations::{
    APPLICATION, HOLDS_OF, INTEGER_RANGE, MEMBERSHIP, MOD, NUMBER_SYSTEMS, PROPERTY_OF,
};
use crate::rules::System;

/// The child indices that lead from `node` to a part of the shape of `part`,
/// the first in the tree's order; None where there is none.
pub(super) fn path_to(node: &Node, part: &Node) -> Option<Vec<usize>> {
    if node.spelt_alike(part) {
        return Some(Vec::new());
    }
    node.children.iter().enumerate().find_map(|(i, c)| {
        let mut rest = path_to(c, part)?;
        rest.insert(0, i);
        Some(rest)
    })
}

/// The part of `node` the child indices lead to; None where they lead off
/// the tree.
pub(super) fn at_path<'n>(node: &'n Node, path: &[usize]) -> Option<&'n Node> {
    match path.split_first() {
        None => Some(node),
        Some((i, rest)) => at_path(node.children.get(*i)?, rest),
    }
}

/// Whether the node is the function `f` applied at the letter `k`, N(k).
pub(super) fn applied_at(node: &Node, f: &str, k: &str) -> bool {
    match node.children.as_slice() {
        [head, arg] => {
            node.notation() == APPLICATION
                && head.is_name()
                && &*head.text == f
                && arg.is_name()
                && &*arg.text == k
        }
        _ => false,
    }
}

/// A letter for a value no letter of the writer's or `taken` is: v, or w,
/// u, or v with a number.
pub(super) fn fresh_letter(writer: &Writer, taken: &str) -> String {
    let free = |l: &str| l != taken && !writer.letters.contains_key(l);
    if let Some(l) = ["v", "w", "u"].into_iter().find(|l| free(l)) {
        return l.to_string();
    }
    let mut i = 1;
    loop {
        let l = format!("v{i}");
        if free(&l) {
            return l;
        }
        i += 1;
    }
}

/// A sentence's parts, a conjunction taken apart by Lean's projections,
/// `H3.1` and `H3.2`, as the tree joins them.
pub(super) fn conjuncts(
    node: &Node,
    proof: Printed,
    says: Option<Printed>,
    out: &mut Vec<super::super::algebra::Cited>,
    w: &Writer,
) {
    if let Some((left, right)) = w.and_sides(node) {
        // The statement as stated, taken apart as the tree is; None where it
        // is no "and".
        let (said_left, said_right) = match says.as_ref().and_then(and_sides) {
            Some((l, r)) => (Some(l), Some(r)),
            None => (None, None),
        };
        conjuncts(left, fields(proof.clone(), &["1"]), said_left, out, w);
        conjuncts(right, fields(proof, &["2"]), said_right, out, w);
        return;
    }
    // a = b = c: its links, as the writer joins them, `a = b ∧ b = c`, the
    // first by `.1` and the rest from `.2` on.
    if let Some(links) = page::chain_links(w.grammar, node) {
        let (mut proof, mut says) = (proof, says);
        let last = links.len().saturating_sub(1);
        for (k, link) in links.iter().enumerate() {
            if k == last {
                conjuncts(link, proof, says, out, w);
                break;
            }
            let (said_link, said_rest) = match says.as_ref().and_then(and_sides) {
                Some((l, r)) => (Some(l), Some(r)),
                None => (None, None),
            };
            conjuncts(link, fields(proof.clone(), &["1"]), said_link, out, w);
            proof = fields(proof, &["2"]);
            says = said_rest;
        }
        return;
    }
    out.push(super::super::algebra::Cited {
        node: node.clone(),
        proof,
        says,
    });
}

/// A claim proved from a term that gives it, as the claim's shape asks:
/// an equation by the ring identity between the two, an order by linear
/// arithmetic, anything else as it stands.
/// A sentence of an item with each property the citation gives by what it
/// says, P := t ↦ …, applied where the sentence applies it: P(u) its body
/// with u's value for t. The item's other letters stay as its statement
/// has them, as Lean's statement of it does.
pub(super) fn read_at_values(
    node: &Node,
    binding: &Binding,
    binders: &FxIndexMap<NotationId, Binds>,
) -> Node {
    // A property holds of a term, P(x), and a function letter applied to
    // one, t(k): each read as the rule the citation gives the letter,
    // `property-of`, with the term for its letter.
    if let (HOLDS_OF | APPLICATION, [p, arg]) =
        (node.notation(), node.children.as_slice())
    {
        if let Some(stands) = binding.get(&p.text).filter(|_| p.is_name()) {
            if let (PROPERTY_OF, [body]) =
                (stands.notation(), stands.children.as_slice())
            {
                let arg = matching::substitute_apart_by(arg, binding, binders);
                let put = Binding::from([(stands.text, arg)]);
                return matching::substitute_apart_by(body, &put, binders);
            }
        }
    }
    if node.children.is_empty() {
        return node.clone();
    }
    node.with_children(
        node.children
            .iter()
            .map(|c| read_at_values(c, binding, binders))
            .collect(),
    )
}

/// An `obtain` pattern for a sentence, one name to each part of its "and"
/// as it nests, the names taken in order; a part left with no name is `_`.
pub(super) fn shaped_pattern(said: &Node, names: &[String], w: &Writer) -> String {
    match (names, w.and_sides(said)) {
        ([], _) => "_".to_string(),
        ([one], _) => one.clone(),
        // Each side takes as many names as it has parts, the left as many
        // as it can while the right keeps one: an "and" that is one
        // sentence of the page stays whole.
        (_, Some((l, r))) => {
            let take = conjunct_count(l, w).min(names.len() - 1);
            let take = take.max(names.len().saturating_sub(conjunct_count(r, w)));
            let (left, right) = names.split_at(take.min(names.len()));
            format!(
                "⟨{}, {}⟩",
                shaped_pattern(l, left, w),
                shaped_pattern(r, right, w)
            )
        }
        (_, None) => names[0].clone(),
    }
}

/// The parts of `said` an obtain pattern of `count` names takes, in order,
/// split as `shaped_pattern` splits it.
pub(super) fn shaped_parts(said: &Node, count: usize, w: &Writer) -> Vec<Node> {
    match (count, w.and_sides(said)) {
        (0, _) => Vec::new(),
        (1, _) => vec![said.clone()],
        (_, Some((l, r))) => {
            let take = conjunct_count(l, w).min(count - 1);
            let take = take.max(count.saturating_sub(conjunct_count(r, w)));
            let take = take.min(count);
            let mut out = shaped_parts(l, take, w);
            out.extend(shaped_parts(r, count - take, w));
            out
        }
        _ => vec![said.clone()],
    }
}

/// A sentence an obtain takes under a name of its own, `from`, where Lean
/// states it as `lean` and the page as `says`, stated after as the page
/// says it under its own name.
pub(super) struct Restated {
    pub(super) name: String,
    pub(super) says: Printed,
    pub(super) from: String,
    pub(super) lean: Printed,
}

/// How many parts an "and" holds, each "and" in it taken apart.
pub(super) fn conjunct_count(node: &Node, w: &Writer) -> usize {
    match w.and_sides(node) {
        Some((l, r)) => conjunct_count(l, w) + conjunct_count(r, w),
        None => 1,
    }
}

/// A proof of a claim said "for all", made of a proof of its body: the
/// letters introduced, then the body's proof. A body proved by a block of
/// tactics on lines of their own, `by` and a line break, takes the `intro`
/// as its first line, at the block's indentation, since a block cannot
/// follow `intro …;` on its line.
pub(super) fn after_intros(
    intros: &[String],
    proof: super::super::doc::Proof,
) -> super::super::doc::Proof {
    let intro = Tactic::Intro(intros.to_vec());
    match proof {
        doc::Proof::Block(mut tactics) => {
            tactics.insert(0, intro);
            doc::Proof::Block(tactics)
        }
        other => doc::Proof::By(Tactic::Seq(vec![intro, tactic_of(&other)])),
    }
}

/// A proof of a claim said of every member of a set, proved of one taken
/// as these letters: `intro` first, inside the proof's `by`.
pub(super) fn with_intros(
    intros: &[String],
    proof: super::super::doc::Proof,
) -> super::super::doc::Proof {
    if intros.is_empty() {
        return proof;
    }
    let intro = Tactic::Intro(intros.to_vec());
    match proof {
        doc::Proof::By(t) => doc::Proof::By(Tactic::Seq(vec![intro, t])),
        doc::Proof::Block(mut ts) => {
            ts.insert(0, intro);
            doc::Proof::Block(ts)
        }
        doc::Proof::Term(t) => {
            doc::Proof::By(Tactic::Seq(vec![intro, Tactic::Exact(t)]))
        }
    }
}

/// A proof as a tactic that closes the goal with it: `(t)` of `by t`,
/// `exact (t)` of a term, `exact (by …)` of a block.
/// A proof written on one line, as a term inside another needs it: a block's
/// tactics joined by `;`, and each `have`'s own tactic proof in brackets, so
/// that it does not take the tactics after it as its own.
pub(super) fn on_one_line(proof: super::super::doc::Proof) -> super::super::doc::Proof {
    match proof {
        doc::Proof::Block(tactics) => doc::Proof::By(Tactic::Seq(
            tactics.into_iter().map(have_bracketed).collect(),
        )),
        other => other,
    }
}

/// A `have` whose proof is tactics, its proof as a bracketed `by` term; any
/// other tactic as it is.
pub(super) fn have_bracketed(tactic: Tactic) -> Tactic {
    match tactic {
        Tactic::Have { name, says, proof } => {
            let proof = match *proof {
                doc::Proof::Term(t) => doc::Proof::Term(t),
                tactics => doc::Proof::Term(super::super::tactics::bracket(
                    super::super::tactics::by_term(on_one_line(tactics)),
                )),
            };
            Tactic::Have {
                name,
                says,
                proof: Box::new(proof),
            }
        }
        other => other,
    }
}

pub(super) fn tactic_of(proof: &super::super::doc::Proof) -> Tactic {
    match proof {
        doc::Proof::By(t) => Tactic::Group(Box::new(t.clone())),
        doc::Proof::Term(t) => Tactic::Exact(super::super::tactics::bracket(t.clone())),
        doc::Proof::Block(_) => Tactic::Exact(super::super::tactics::bracket(
            super::super::tactics::by_term(proof.clone()),
        )),
    }
}

/// The proof `by t` of the one way a step is closed; declined, for `why`,
/// where the writer has several and nothing to choose among them by, as a
/// generated proof tries no ways in turn.
pub(super) fn ways_proof(
    why: ListReason,
    ways: Vec<Tactic>,
) -> Route<super::super::doc::Proof> {
    match <[Tactic; 1]>::try_from(ways) {
        Ok([one]) => Route::Built(super::super::doc::Proof::By(one)),
        Err(_) => several_ways(why),
    }
}

/// A step the writer could close several ways, for `why`, with nothing
/// to choose among them by: declined, as a generated proof tries no ways
/// in turn.
pub(super) fn several_ways<T>(why: ListReason) -> Route<T> {
    Route::no(format!(
        "a step with several ways to close it and no fact to choose one by: {}",
        why.text()
    ))
}

/// Why a cited statement `says` and the claim, both as Lean states them,
/// keep a list: the first of the closer's checks that does not hold of
/// them, in the order the closer asks them.
pub(super) fn apart(
    claim_node: &Node,
    says: &Printed,
    claim: &Printed,
    values: &super::super::doc::forms::Values,
    facing: Option<Facing>,
) -> ListReason {
    let types_apart = super::super::doc::forms::relation_types_apart(says, claim);
    let shaped = matches!(claim_node.notation(), EQUALITY | ORDER);
    if types_apart {
        ListReason::CitedTypesApart
    } else if !shaped {
        ListReason::CitedOtherShape
    } else if to_nat_texts(says) != to_nat_texts(claim) {
        ListReason::CitedToNatApart
    } else if !(super::super::casts::push_cast_moves_all_in_sides(says)
        && super::super::casts::push_cast_moves_all_in_sides(claim))
        || (claim_node.notation() == ORDER && cast_texts(says) != cast_texts(claim))
    {
        ListReason::CitedCastsUnmoved
    } else if !same_ring_atoms(says, claim, values) {
        ListReason::CitedAtomsApart
    } else if claim_node.notation() == EQUALITY && facing.is_none() {
        ListReason::CitedFacingUnknown
    } else {
        ListReason::CitedOtherShape
    }
}

/// The cited statement taken with its listed sets in the claim's order: an
/// equation of sets member by member, which takes a listed set in any order
/// and of any size; another relation, a membership or subset of a listed
/// set, read in both as the members' equations it says, which `tauto` takes
/// in any order.
pub(super) fn reordered(cited: &Printed, equation: bool) -> Tactic {
    let h = || t::hyp("h");
    if !equation {
        return t::on_h(
            cited,
            vec![
                t::simp_only(
                    false,
                    None,
                    vec![
                        t::forwards(t::lemma("Set.mem_insert_iff")),
                        t::forwards(t::lemma("Set.mem_singleton_iff")),
                        t::forwards(t::lemma("Set.insert_subset_iff")),
                        t::forwards(t::lemma("Set.singleton_subset_iff")),
                    ],
                    Some(t::at_h(true)),
                ),
                t::call("tauto", vec![]),
            ],
        );
    }
    let x = t::hyp("x");
    let applied = Printed {
        kind: super::super::doc::TermKind::App {
            head: Box::new(h()),
            args: vec![super::super::doc::Arg::Explicit(x.clone())],
            explicit: false,
        },
        ty: None,
    };
    t::on_h(
        cited,
        vec![
            t::call("ext", vec![TacticArg::Term(x)]),
            t::call(
                "rw",
                vec![t::rules(vec![t::lemma("Set.ext_iff")]), t::at_h(false)],
            ),
            t::call("specialize", vec![TacticArg::Term(applied)]),
            t::simp_only(
                false,
                None,
                vec![
                    t::forwards(t::lemma("Set.mem_insert_iff")),
                    t::forwards(t::lemma("Set.mem_singleton_iff")),
                ],
                Some(t::at_h(true)),
            ),
            t::call("tauto", vec![]),
        ],
    )
}

/// An exponent the record shows at least 0, as Lean writes it, and the proof
/// of `0 ≤ e` (`nonneg_proof`).
#[derive(Clone, Debug)]
pub(super) struct NonNegative {
    pub(super) exponent: Printed,
    pub(super) proof: Printed,
}

/// The parts of what a "there is" says of its letters, as Lean states the
/// "there is", `statement`: each letter it binds taken off with its guard,
/// in order, and given the name the obtain gives it, `obtained`, and what is
/// said of them taken apart at `∧`. Empty where `statement` binds no letter.
pub(super) fn lean_body_parts(
    statement: &Printed,
    obtained: &[String],
) -> Vec<Printed> {
    fn unbracketed(t: &Printed) -> &Printed {
        match &t.kind {
            TermKind::Paren(inner) => unbracketed(inner),
            _ => t,
        }
    }
    let mut given = BTreeMap::new();
    let mut at = statement;
    while let TermKind::Quantified {
        quant: Quant::Exists,
        letter,
        letter_ty,
        body,
        ..
    } = &unbracketed(at).kind
    {
        let Some(name) = obtained.get(given.len()) else {
            return Vec::new();
        };
        given.insert(
            letter.clone(),
            Printed::letter(super::super::names::letter(name), letter_ty.clone()),
        );
        at = body;
    }
    if given.is_empty() {
        return Vec::new();
    }
    conjoined_parts(at)
        .iter()
        .map(|p| p.substituted(&given))
        .collect()
}

/// The parts of a statement Lean joins by "and", in order, each without
/// its brackets: `a ∧ (b ∧ c)` as a, b, c; one part where it is no "and".
pub(super) fn conjoined_parts(term: &Printed) -> Vec<Printed> {
    match and_sides(term) {
        Some((lhs, rhs)) => {
            let mut out = conjoined_parts(&lhs);
            out.extend(conjoined_parts(&rhs));
            out
        }
        None => {
            let mut t = term;
            while let super::super::doc::TermKind::Paren(inner) = &t.kind {
                t = inner;
            }
            vec![t.clone()]
        }
    }
}

/// The projection that takes part `k` of `conjoined_parts(term)` from a
/// proof of `term`, read off how its "and"s nest: part 2 of `(A ∧ B) ∧ C`
/// is `.2`, of `A ∧ (B ∧ C)` `.2.2`. None where `term` has no part `k`.
pub(super) fn conjunct_path(term: &Printed, k: usize) -> Option<Vec<&'static str>> {
    match and_sides(term) {
        Some((lhs, rhs)) => {
            let left = conjoined_parts(&lhs).len();
            let (field, inner, at) = match k < left {
                true => ("1", lhs, k),
                false => ("2", rhs, k - left),
            };
            let mut out = vec![field];
            out.extend(conjunct_path(&inner, at)?);
            Some(out)
        }
        None => (k == 0).then(Vec::new),
    }
}

/// A set as Lean writes it, with the proof that it is finite
/// (`finite_proof`).
#[derive(Clone, Debug)]
pub(super) struct ShownFinite {
    pub(super) set: Printed,
    pub(super) proof: Printed,
}

/// A page term with the proof that it is at least 0, from a hypothesis of a
/// cited item the checker found supplied.
#[derive(Clone, Debug)]
pub(super) struct ShownWhole {
    pub(super) term: Node,
    pub(super) proof: Printed,
}

/// The term and the system of a membership of ℕ or ℕ₀, `t ∈ ℕ₀`; None of
/// any other sentence.
pub(super) fn membership_of_whole(sentence: &Node) -> Option<(&Node, System)> {
    let [term, set] = sentence.children.as_slice() else {
        return None;
    };
    if sentence.notation() != MEMBERSHIP || set.notation() != NUMBER_SYSTEMS {
        return None;
    }
    let system = System::of_sign(&set.text)?;
    matches!(system, System::N | System::N0).then_some((term, system))
}

/// Whether a statement, its functions applied (`forms::beta_reduced`), takes
/// a numeral to ℕ, `(0 : ℤ).toNat` of `fun k => y ^ k.toNat` at 0.
pub(super) fn leaves_numeral_to_nat(term: &Printed) -> bool {
    super::super::doc::forms::beta_reduced(term).walk().iter().any(|t| {
        matches!(&t.kind, TermKind::ToNat(inner)
            if super::super::casts::as_natural(inner).is_some()
                && matches!(&super::super::doc::forms::ascriptions_dropped(inner).kind, TermKind::Numeral(_)))
    })
}

/// What a citation's conversion rewrites (`forms_converted`).
pub(super) struct Conversion<'a> {
    /// Each finite set the two count, with why it is finite: its count in
    /// ℕ∞ written as its count in ℕ.
    pub(super) finite: &'a [ShownFinite],
    /// Each exponent at least 0, with why: the integer power written as the
    /// natural power to its `toNat`.
    pub(super) whole: &'a [NonNegative],
    /// Each power under a sum whose exponent names its letter, converted for
    /// each letter in the sum's range.
    pub(super) bound: &'a [super::super::doc::forms::BoundPower],
    /// An integer power of a natural number cast up, `a ^ (k : ℤ)`, written
    /// as the natural power `a ^ k` (`zpow_natCast`).
    pub(super) cast_powers: bool,
    /// The rewrites of the identity elements the checker dropped meeting the
    /// two (`Cited::meetings`), `sub_zero` of x − 0.
    pub(super) identities: &'a [&'static str],
    /// A numeral's `toNat` the reading leaves, `(0 : ℤ).toNat`, worked out
    /// (`Int.reduceToNat`).
    pub(super) numeral_to_nat: bool,
}

/// `Set.Finite.cast_ncard_eq (p : S.Finite)`: a finite set's count as a
/// natural number, cast to ℕ∞, is its count in ℕ∞.
pub(super) fn cast_ncard_eq(ShownFinite { set, proof }: &ShownFinite) -> Printed {
    // Told its type, `({a} : Set α)`, as the count writes it.
    let typed = match &set.ty {
        Some(ty) => Printed::cast(set.clone(), ty.clone()),
        None => t::bracket(set.clone()),
    };
    let says = Printed::of(
        super::super::doc::TermKind::Field {
            inner: Box::new(typed),
            field: "Finite".to_string(),
        },
        super::super::doc::LeanType::Prop,
    );
    Printed::applied(
        "Set.Finite.cast_ncard_eq",
        super::super::doc::Source::Mathlib,
        vec![t::bracket(ascribed(proof.clone(), says))],
        super::super::doc::LeanType::Prop,
    )
}

/// A citation whose item writes a term in one form and the claim in the
/// other, each form one the writer chose under a fact the record gives:
/// `(have h := t; simp only [← Set.Finite.cast_ncard_eq (p : S.Finite),
/// parley_zpow_toNat (n := e) (h := q)] at h ⊢; exact_mod_cast h)`. Each
/// count in ℕ∞ of a finite S is written as its count in ℕ, and each integer
/// power `a ^ e` of an e at least 0 as the natural power `a ^ e.toNat`,
/// after which the two differ only by casts; `h.symm` where the claim is
/// the item's equation turned round (`Conversion` says what is converted).
pub(super) fn forms_converted(
    cited: &Printed,
    c: &Conversion,
    turned: bool,
) -> super::super::doc::Proof {
    let Conversion {
        finite,
        whole,
        bound,
        cast_powers,
        identities,
        numeral_to_nat,
    } = c;
    let powers = whole.iter().map(|w| {
        t::forwards(Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(t::bridge_lemma(
                    "parley_zpow_toNat",
                    BridgeModule::PowerTactics,
                )),
                args: vec![
                    super::super::doc::Arg::Named {
                        name: "n".to_string(),
                        value: w.exponent.clone(),
                    },
                    super::super::doc::Arg::Named {
                        name: "h".to_string(),
                        value: w.proof.clone(),
                    },
                ],
                explicit: false,
            },
            ty: Some(super::super::doc::LeanType::Prop),
        })
    });
    let rules = finite
        .iter()
        .map(|shown| t::backwards(cast_ncard_eq(shown)))
        .chain(powers)
        .chain(cast_powers.then(|| t::forwards(t::lemma("zpow_natCast"))))
        .chain((0..bound.len()).map(|k| t::forwards(t::hyp(&format!("hb{}", k + 1)))))
        .chain(identities.iter().map(|l| t::forwards(t::lemma(l))))
        .chain(numeral_to_nat.then(|| t::forwards(t::lemma("Int.reduceToNat"))))
        .collect();
    let mut steps: Vec<Tactic> = bound
        .iter()
        .enumerate()
        .filter_map(|(k, b)| bound_rewrite(b, &format!("hb{}", k + 1)))
        .collect();
    // A rewrite stated for each letter in a sum's range is taken under the
    // sum, where the letter's membership is in scope: `+contextual`.
    steps.push(t::simp_only(
        !bound.is_empty(),
        None,
        rules,
        Some(t::at_h(true)),
    ));
    steps.push(t::exact_mod_cast(match turned {
        true => t::symm(t::hyp("h")),
        false => t::hyp("h"),
    }));
    super::super::doc::Proof::By(t::on_h(cited, steps))
}

/// The lower end `a` of a range a sum runs over, `Finset.Icc a b`; None of
/// any other set.
pub(super) fn range_lower(over: &Printed) -> Option<&Printed> {
    let super::super::doc::TermKind::App { head, args, .. } = &over.kind else {
        return None;
    };
    let (
        super::super::doc::TermKind::Const(c),
        [super::super::doc::Arg::Explicit(a), _],
    ) = (&head.kind, args.as_slice())
    else {
        return None;
    };
    (c.name == "Finset.Icc").then_some(a)
}

/// `have name : ∀ k ∈ Finset.Icc a b, x ^ e = x ^ e.toNat := fun k hk =>
/// parley_zpow_toNat x e (by linarith [(Finset.mem_Icc.mp hk).1])`: a power
/// under a sum whose exponent names its letter, as the natural power, for
/// each letter in the sum's range, the exponent at least 0 by the range's
/// lower bound. None where the sum runs over no range.
pub(super) fn bound_rewrite(
    b: &super::super::doc::forms::BoundPower,
    name: &str,
) -> Option<Tactic> {
    range_lower(&b.over)?;
    let k = || Printed::letter(&b.letter, b.letter_ty.clone());
    let natural = Printed::infix(
        Op::POWER,
        b.base.clone(),
        Printed::of(
            TermKind::ToNat(Box::new(t::bracket(b.exponent.clone()))),
            LeanType::Num(super::super::templates::Num::Nat),
        ),
        b.power.ty.clone().unwrap_or(LeanType::Prop),
    );
    let says = Printed::of(
        TermKind::Quantified {
            quant: Quant::ForAll,
            letter: b.letter.clone(),
            letter_ty: b.letter_ty.clone(),
            guard: Some(Box::new(Printed::infix(
                Op::of("∈")?,
                k(),
                b.over.clone(),
                LeanType::Prop,
            ))),
            body: Box::new(Printed::infix(
                Op::EQUALS,
                b.power.clone(),
                natural,
                LeanType::Prop,
            )),
            bounded: true,
        },
        LeanType::Prop,
    );
    let lower = Printed {
        kind: TermKind::Field {
            inner: Box::new(t::bracket(Printed::applied(
                "Finset.mem_Icc.mp",
                Source::Mathlib,
                vec![t::hyp("hk")],
                LeanType::Prop,
            ))),
            field: "1".to_string(),
        },
        ty: Some(LeanType::Prop),
    };
    let nonneg = t::by_term(super::super::doc::Proof::By(t::call(
        "linarith",
        vec![t::rules(vec![lower])],
    )));
    let each = Printed::applied(
        "parley_zpow_toNat",
        Source::Bridge(BridgeModule::PowerTactics),
        vec![
            t::bracket(b.base.clone()),
            t::bracket(b.exponent.clone()),
            nonneg,
        ],
        LeanType::Prop,
    );
    Some(Tactic::Have {
        name: name.to_string(),
        says,
        proof: Box::new(super::super::doc::Proof::Term(Printed::of(
            TermKind::Lambda {
                letters: vec![b.letter.clone(), "hk".to_string()],
                body: Box::new(each),
            },
            LeanType::Prop,
        ))),
    })
}

/// The type variables a term's parts are of, or are sets or maps of.
pub(super) fn things_in(term: &Printed) -> BTreeSet<usize> {
    let mut out: BTreeSet<usize> = term.ty.iter().flat_map(things_of_type).collect();
    for child in term.children() {
        out.extend(things_in(child));
    }
    out
}

/// The type variables a type is made of.
pub(super) fn things_of_type(ty: &super::super::doc::LeanType) -> Vec<usize> {
    match ty {
        LeanType::Things(n) => vec![*n],
        LeanType::Set(inner) | LeanType::Sym2(inner) => things_of_type(inner),
        LeanType::Fun { from, to } | LeanType::Prod(from, to) => {
            let mut out = things_of_type(from);
            out.extend(things_of_type(to));
            out
        }
        _ => Vec::new(),
    }
}

/// `show s by t`: a term saying s, proved by t.
pub(super) fn shown(says: Printed, proof: super::super::doc::Proof) -> Printed {
    Printed::of(
        super::super::doc::TermKind::Show {
            says: Box::new(says),
            proof: Box::new(super::super::tactics::by_term(proof)),
        },
        super::super::doc::LeanType::Prop,
    )
}

/// `(proof : says)`: a proof given the statement it is taken as.
pub(super) fn ascribed(proof: Printed, says: Printed) -> Printed {
    Printed::of(
        super::super::doc::TermKind::Ascribed {
            proof: Box::new(proof),
            says: Box::new(says),
        },
        super::super::doc::LeanType::Prop,
    )
}

/// Whether the two sides of an equation a define makes true, met as the
/// checker met them with the define written out, are then the same term,
/// which `simp only [hD]` closes by reflexivity: bound letters may be
/// renamed, which are the same term to Lean, and nothing else taken. An
/// identity element dropped or a respelling is arithmetic left for
/// `norm_num`.
pub(super) fn unfolds_alone(met: &Meeting) -> bool {
    met.renamed_only()
}

/// The equations of the defines `defines` applied, `simp (disch := omega)
/// only [h]`, which closes a claim they make true as it stands; and where
/// `alone` is false, the claim then worked out, `push_cast; norm_num`. Of a
/// claim "for all x ∈ S, A = B", `implies_true` takes the `∀ x ∈ S, True`
/// its body leaves.
pub(super) fn unfolded_by(defines: &[String], alone: bool, for_all: bool) -> Tactic {
    let rules: Vec<super::super::doc::Rule> =
        defines.iter().map(|d| t::forwards(t::hyp(d))).collect();
    simp_unfolded(rules, alone, for_all)
}

/// A step citing a function the header lets, where the record does not
/// decide it: the function's equation put in, which closes the claim.
pub(super) fn header_ways(hyp: &str) -> super::super::doc::Proof {
    super::super::doc::Proof::By(Tactic::Seq(vec![
        t::simp_only(false, None, vec![t::forwards(t::hyp(hyp))], None),
        t::call("done", vec![]),
    ]))
}

/// `unfolded_by` with the rules given: the defines' equations and any
/// rewrite that goes with them, a case's `if_pos h`.
pub(super) fn simp_unfolded(
    mut rules: Vec<super::super::doc::Rule>,
    alone: bool,
    for_all: bool,
) -> Tactic {
    if for_all {
        rules.push(t::forwards(t::lemma("implies_true")));
    }
    let simp = t::simp_only(false, Some(t::call("omega", vec![])), rules, None);
    match alone {
        true => simp,
        false => {
            Tactic::Seq(vec![simp, t::push_cast(None), t::call("norm_num", vec![])])
        }
    }
}

/// `(simp (disch := omega) only [h]; done)` and `(simp (disch := omega)
/// only [h]; push_cast; norm_num; done)`: a claim made true by the
/// equations of the defines cited, as they stand or once worked out.
pub(super) fn unfolded(defines: &[String]) -> Vec<Tactic> {
    let rules: Vec<super::super::doc::Rule> =
        defines.iter().map(|d| t::forwards(t::hyp(d))).collect();
    let simp =
        || t::simp_only(false, Some(t::call("omega", vec![])), rules.clone(), None);
    vec![
        t::steps(vec![simp(), t::call("done", vec![])]),
        t::steps(vec![
            simp(),
            t::push_cast(None),
            t::call("norm_num", vec![]),
            t::call("done", vec![]),
        ]),
    ]
}

/// `qify; push_cast; simp only [specs]; linear_combination line`: a row and
/// the line it cites taken to ℚ, each named number put as its term, and the
/// line used the way the row faces it (`link_facings`), `-line` where
/// turned; declined where the record has no facing. A congruence row is
/// the line itself, which states it in the named numbers' forms already:
/// `exact line`, or `line.symm` where turned.
pub(super) fn in_named_forms(
    specs: &[Printed],
    line: &str,
    facing: Option<Facing>,
    congruence: bool,
) -> Route<Tactic> {
    if let (true, Some(facing)) = (congruence, facing) {
        return Route::Built(Tactic::Exact(faced(t::hyp(line), facing)));
    }
    let rules = specs.iter().cloned().map(t::forwards).collect();
    let used = match facing {
        Some(Facing::Straight) => t::linear_combination(t::hyp(line)),
        Some(Facing::Turned) => t::linear_combination(negated(t::hyp(line))),
        None => return several_ways(ListReason::NamedNumbers),
    };
    Route::Built(t::steps(vec![
        t::call("qify", vec![]),
        t::push_cast(None),
        t::simp_only(false, None, rules, None),
        used,
    ]))
}

/// That a term is at least 0, from the line that puts it in ℕ₀, `h`, or
/// in ℕ, `(le_of_lt h)`.
pub(super) fn nonneg_of(system: System, line: Printed) -> Printed {
    match system {
        System::N => Printed::applied(
            "le_of_lt",
            super::super::doc::Source::Mathlib,
            vec![line],
            super::super::doc::LeanType::Prop,
        ),
        _ => line,
    }
}

/// `by norm_num`, as a term: a fact of numerals alone.
pub(super) fn norm_num_term() -> Printed {
    super::super::tactics::by_term(super::super::doc::Proof::By(
        super::super::tactics::call("norm_num", vec![]),
    ))
}

/// `Int.toNat_of_nonneg h`: an integer at least 0 is its `toNat`.
pub(super) fn to_nat_of(nonneg: Printed) -> Printed {
    Printed::applied(
        "Int.toNat_of_nonneg",
        super::super::doc::Source::Core,
        vec![nonneg],
        super::super::doc::LeanType::Prop,
    )
}

/// `-t`.
pub(super) fn negated(term: Printed) -> Printed {
    Printed {
        ty: term.ty.clone(),
        kind: super::super::doc::TermKind::Neg(Box::new(term)),
    }
}

/// A named number's equation with its term: the one a step proves, by its
/// name, or the line's witness's, `Classical.choose_spec h`.
pub(super) fn spec_of(said: &super::super::expr::SaidInteger) -> Printed {
    let proof = said.proof.clone();
    match said.value {
        Some(_) => proof,
        None => Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(Printed::head(
                    "Classical.choose_spec",
                    super::super::doc::Source::Core,
                )),
                args: vec![super::super::doc::Arg::Explicit(proof)],
                explicit: false,
            },
            ty: None,
        },
    }
}

/// `by push_cast; simp only [specs]`: a witness's equation, the witness
/// built from the named numbers' values as the term is from theirs, so
/// their equations put in leave the two sides one.
pub(super) fn specs_equal(specs: &[Printed]) -> Printed {
    let rules: Vec<super::super::doc::Rule> =
        specs.iter().cloned().map(t::forwards).collect();
    super::super::tactics::by_term(super::super::doc::Proof::By(specs_then(&rules)))
}

/// `specs_equal` of a named number for `term`. Where the term takes a
/// remainder, `(a^(p − 2)) mod p`, the number is Lean's `%` of integers and
/// the term the bridge's `mod` of real numbers, which are one where the
/// divisor is not negative (`LeanBridges.Divisibility.mod_intCast`): each
/// way first puts the one for the other, the divisor's sign by `omega`
/// from the lines in scope.
pub(super) fn specs_equal_of(term: &Node, specs: &[Printed]) -> Printed {
    if !takes_remainder(term) {
        return specs_equal(specs);
    }
    let rules: Vec<super::super::doc::Rule> =
        specs.iter().cloned().map(t::forwards).collect();
    t::by_term(super::super::doc::Proof::By(unmod_then(&rules)))
}

/// One way of `specs_equal_of`: the integers' `%` put as the bridge's
/// `mod` of their casts, then the named numbers' equations.
pub(super) fn unmod_then(rules: &[super::super::doc::Rule]) -> Tactic {
    let unmod = t::call(
        "rw",
        vec![TacticArg::Rules(vec![t::backwards(mod_int_cast())])],
    );
    Tactic::Group(Box::new(Tactic::Seq(vec![unmod, specs_then(rules)])))
}

/// A term where it stands as one whole, bracketed unless it already is:
/// a witness inside `⟨…⟩`, as an argument is.
pub(super) fn whole_term(term: Printed) -> Printed {
    match term.prec() >= super::super::expr::MAX {
        true => term,
        false => super::super::tactics::bracket(term),
    }
}

/// A claim joined by "and" that the checker met with the item's "and" as
/// written, closed part by part: "and" stands in no other order, so part j
/// of the item is part j of the claim. The item named once, `have h :=
/// term`, each part from its projection `h.j`:
/// - a membership of ℕ or ℕ₀ Lean writes as an integer of a wider term,
///   `∃ m : ℤ, 0 < m ∧ ↑m = t` (`Writer::in_system`), beside the item's
///   order `0 < v` of the same order: `⟨_, h.j, rfl⟩`, t being the named
///   number's cast once the proof has put it;
/// - an equation or order whose casts `norm_cast` all moves on both sides:
///   `by exact_mod_cast h.j`.
///
/// None where the two split into different numbers of parts, or a part has
/// neither form.
pub(super) fn parts_closed(
    node: &Node,
    claim: &Printed,
    says: &Printed,
    term: &Printed,
    w: &Writer,
) -> Option<super::super::doc::Proof> {
    let parts = and_parts(node, w);
    if parts.len() < 2 {
        return None;
    }
    // The order of `0 < m` or `0 ≤ m`, a bound of the numeral 0.
    let zero_bound = |p: &Printed| match &p.kind {
        TermKind::Infix { op, lhs, .. }
            if matches!(op.symbol, "<" | "≤")
                && matches!(&lhs.kind, TermKind::Numeral(d) if d == "0") =>
        {
            Some(op.symbol)
        }
        _ => None,
    };
    let mut proofs = Vec::new();
    for (j, part) in parts.iter().enumerate() {
        let path = leaf_path(node, j, w)?;
        let (wanted, given) = (along(claim, &path)?, along(says, &path)?);
        if and_sides(&given).is_some() || and_sides(&wanted).is_some() {
            return None;
        }
        let h = projected(t::hyp("h"), &path);
        let witnessed = match &wanted.kind {
            TermKind::Quantified {
                quant: super::super::doc::Quant::Exists,
                guard: Some(guard),
                ..
            } if part.notation() == MEMBERSHIP => {
                zero_bound(guard).filter(|order| zero_bound(&given) == Some(*order))
            }
            _ => None,
        };
        let proof = match witnessed {
            Some(_) => {
                let rfl = Printed::constant(
                    "rfl",
                    super::super::doc::Source::Core,
                    super::super::doc::LeanType::Prop,
                );
                super::super::expr::anonymous(vec![elided_term(), h, rfl])
            }
            None if matches!(part.notation(), EQUALITY | ORDER)
                && super::super::casts::norm_cast_moves_all(&given)
                && super::super::casts::norm_cast_moves_all(&wanted) =>
            {
                t::by_term(super::super::doc::Proof::By(t::exact_mod_cast(h)))
            }
            None => return None,
        };
        proofs.push(proof);
    }
    Some(super::super::doc::Proof::By(t::on_h(
        term,
        vec![Tactic::Exact(super::super::expr::anonymous(proofs))],
    )))
}

/// `⟨_, equation, member⟩`: a claim of a range member Lean computes wider
/// (`wide_range_member`), made of the integer that is it, its equation with
/// the term, and that integer's membership.
pub(super) fn range_member_made(equation: Printed, member: Printed) -> Printed {
    let elided = Printed::of(
        super::super::doc::TermKind::Elided,
        super::super::doc::LeanType::Prop,
    );
    super::super::expr::anonymous(vec![elided, equation, member])
}

/// Whether a claim says a term Lean computes wider than ℤ is in a range,
/// `f(a) ∈ {0, …, p − 1}` of a real f, which Lean says of the integer that
/// is the term (`Writer::formula`).
pub(super) fn wide_range_member(writer: &Writer, claim: &Node) -> bool {
    let (MEMBERSHIP, [term, set]) = (claim.notation(), claim.children.as_slice())
    else {
        return false;
    };
    set.notation() == INTEGER_RANGE
        && writer
            .carrier(term)
            .built()
            .is_some_and(|c| c > super::super::templates::Num::Int)
}

/// Whether a term takes a remainder, x mod n, which Lean writes as the
/// bridge's `mod` of real numbers where its parts are, and as `%` of
/// integers where a step names them whole.
pub(super) fn takes_remainder(term: &Node) -> bool {
    term.walk().iter().any(|n| n.notation() == MOD)
}

/// `LeanBridges.Divisibility.mod_intCast _ _ (by omega)`: the bridge's `mod`
/// of two integers cast to ℝ is their `%`, where the divisor is not
/// negative, which `omega` reads off the lines in scope.
pub(super) fn mod_int_cast() -> Printed {
    let elided = || Printed::of(TermKind::Elided, super::super::doc::LeanType::Prop);
    let sign = t::bracket(t::by_term(doc::Proof::By(t::call("omega", vec![]))));
    Printed {
        kind: TermKind::App {
            head: Box::new(t::bridge_lemma(
                "LeanBridges.Divisibility.mod_intCast",
                BridgeModule::Divisibility,
            )),
            args: vec![
                Arg::Explicit(elided()),
                Arg::Explicit(elided()),
                Arg::Explicit(sign),
            ],
            explicit: false,
        },
        ty: None,
    }
}

/// An equation of a whole number's line, stated in `from`, carried to the
/// type `to` the goal writes it in: by its casts, or, from ℚ to ℝ, where
/// `exact_mod_cast` does not carry a power to an integer, by casting the
/// equation to ℝ and pushing the cast in, `have h := congrArg (fun x => ((x
/// : ℚ) : ℝ)) e; push_cast at h; exact h`.
pub(super) fn cast_carried(
    equation: Printed,
    from: super::super::templates::Num,
    to: super::super::templates::Num,
) -> super::super::doc::Proof {
    if (from, to) != (Num::Rat, Num::Real) {
        return super::super::doc::Proof::By(t::exact_mod_cast(equation));
    }
    let to_real = untyped_lambda(
        &["x"],
        Printed::cast(
            Printed::cast(t::hyp("x"), LeanType::Num(Num::Rat)),
            LeanType::Num(Num::Real),
        ),
    );
    let carried = Printed {
        kind: TermKind::App {
            head: Box::new(t::lemma("congrArg")),
            args: vec![Arg::Explicit(to_real), Arg::Explicit(equation.clone())],
            explicit: false,
        },
        ty: None,
    };
    let pushed = Tactic::Seq(vec![
        Tactic::Name {
            name: "h".to_string(),
            term: carried,
        },
        t::push_cast(Some(t::at_h(false))),
        Tactic::Exact(t::hyp("h")),
    ]);
    super::super::doc::Proof::By(pushed)
}

/// `fun a h => body`: a function of these letters, whose types Lean finds
/// from where it stands, as the proof part of `⟨…⟩` takes them.
pub(super) fn untyped_lambda(letters: &[&str], body: Printed) -> Printed {
    let ty = body.ty.clone().unwrap_or(super::super::doc::LeanType::Prop);
    Printed::of(
        super::super::doc::TermKind::Lambda {
            letters: letters.iter().map(|l| l.to_string()).collect(),
            body: Box::new(body),
        },
        ty,
    )
}

/// `refine ⟨parts⟩`: the goal's parts, the ones left open proved after.
pub(super) fn refine(parts: Vec<Printed>) -> Tactic {
    super::super::tactics::call(
        "refine",
        vec![TacticArg::Term(super::super::expr::anonymous(parts))],
    )
}

/// `(push_cast; simp only [specs])`.
pub(super) fn specs_then(rules: &[super::super::doc::Rule]) -> Tactic {
    t::steps(vec![
        t::push_cast(None),
        t::simp_only(false, None, rules.to_vec(), None),
    ])
}
