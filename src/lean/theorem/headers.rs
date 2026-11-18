//! A theorem's header, recursions and given things.

use super::*;

/// A statement with the numbers a step names as an integer's `toNat` put
/// back as the integers (`put_back`).
pub(super) struct PutBack {
    /// The statement with each such number written as its integer.
    pub(super) left: Printed,
    /// The rewrites, each a name's own equation, that turn the statement
    /// as asked into `left`.
    pub(super) rules: Vec<super::super::doc::Rule>,
}

impl PutBack {
    /// `by rw [rules]; exact proof`, `proof` proving `left`.
    pub(super) fn then(self, proof: Printed) -> Printed {
        use super::super::tactics as t;
        t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
            t::call("rw", vec![TacticArg::Rules(self.rules)]),
            Tactic::Exact(proof),
        ])))
    }
}

/// Mathlib's lemmas `names`, each a rule used forwards.
pub(super) fn lemma_rules(names: &[&str]) -> Vec<super::super::doc::Rule> {
    names
        .iter()
        .map(|n| super::super::tactics::forwards(super::super::tactics::lemma(n)))
        .collect()
}

/// `tactic`, `simp` or `norm_num`, with `rules` where there are any.
pub(super) fn simp_call(
    tactic: &'static str,
    rules: Vec<super::super::doc::Rule>,
) -> super::super::doc::Proof {
    let args = match rules.is_empty() {
        true => vec![],
        false => vec![TacticArg::Rules(rules)],
    };
    super::super::doc::Proof::By(super::super::tactics::call(tactic, args))
}

/// `0 ≤ v` of a value `v` a row of the closure table (`rules::WHOLE`) puts
/// in ℕ₀, by the row's operation `op`: Lean holds a gcd, lcm or binomial
/// coefficient as a natural number cast up, and a remainder by a divisor
/// not 0 at least 0, the divisor's `0 < n` (`divisor`) turned by
/// `ne_of_gt`. None for any other operation, or a divisor with no bound.
pub(super) fn whole_nonneg(
    op: &str,
    divisor: impl FnOnce() -> Option<Printed>,
) -> Option<Printed> {
    let hole = || {
        Printed::of(
            super::super::doc::TermKind::Elided,
            super::super::doc::LeanType::Prop,
        )
    };
    let mathlib = |name: &str, args: Vec<Printed>| {
        Printed::applied(
            name,
            super::super::doc::Source::Mathlib,
            args,
            super::super::doc::LeanType::Prop,
        )
    };
    match op {
        "cbc" | "cgcd" | "clcm" => Some(mathlib("Nat.cast_nonneg", vec![hole()])),
        "cmo" => {
            let positive = divisor()?;
            Some(mathlib(
                "Int.emod_nonneg",
                vec![
                    hole(),
                    mathlib("ne_of_gt", vec![super::super::tactics::bracket(positive)]),
                ],
            ))
        }
        _ => None,
    }
}

/// The part of `node`, an "and" of the page, that is `written`, with the
/// term that proves it and what Lean states of it: `proof` and `says`
/// taken apart along the "and"s to it, as `conjuncts` takes them. The
/// first such part from the left; None where none is.
pub(super) fn part_written(
    node: &Node,
    proof: Printed,
    says: Option<Printed>,
    written: &Node,
    w: &Writer,
    ctx: &crate::matching::Context,
) -> Option<super::super::algebra::Cited> {
    if read_alike(node, written, ctx) {
        return Some(super::super::algebra::Cited {
            node: node.clone(),
            proof,
            says,
        });
    }
    let (left, right) = w.and_sides(node)?;
    let (said_left, said_right) = match says.as_ref().and_then(and_sides) {
        Some((l, r)) => (Some(l), Some(r)),
        None => (None, None),
    };
    part_written(
        left,
        fields(proof.clone(), &["1"]),
        said_left,
        written,
        w,
        ctx,
    )
    .or_else(|| part_written(right, fields(proof, &["2"]), said_right, written, w, ctx))
}

/// Whether a line's tree and a node the record holds are one, each read in
/// the standard spelling as the checker reads them: `n²` is `n^2`.
pub(super) fn read_alike(
    line: &Node,
    recorded: &Node,
    ctx: &crate::matching::Context,
) -> bool {
    crate::matching::alike_top(
        &crate::matching::standard(line, ctx),
        &crate::matching::standard(recorded, ctx),
        ctx,
    )
}

/// A calculation's row as Lean states it: `a ≡ b [ZMOD n]` of a congruence
/// with its modulus `n`, else `a R b` by the relation. None of a relation
/// Lean has no operator for.
pub(super) fn calc_row(
    relation: &str,
    modulus: Option<&Printed>,
    from: &Printed,
    to: &Printed,
) -> Option<Printed> {
    use super::super::doc::{LeanType, TermKind};
    match modulus {
        Some(n) => Some(Printed::of(
            TermKind::ModEq {
                a: Box::new(from.clone()),
                b: Box::new(to.clone()),
                n: Box::new(n.clone()),
            },
            LeanType::Prop,
        )),
        None => Some(Printed::infix(
            super::super::doc::Op::of(relation)?,
            from.clone(),
            to.clone(),
            LeanType::Prop,
        )),
    }
}

/// What `statement` says under its leading "for all"s, `P` of `∀ x ∈ S, ∀
/// y, P`; the statement itself where it opens with none.
pub(super) fn under_for_alls(statement: &Printed) -> &Printed {
    let bare = bare_term(statement);
    match &bare.kind {
        super::super::doc::TermKind::Quantified {
            quant: super::super::doc::Quant::ForAll,
            body,
            ..
        } => under_for_alls(body),
        _ => bare,
    }
}

/// `t` with each natural number cast back to the integer it was taken
/// from, `((u).toNat : ℤ)`, written as that integer `u`, each such `u`
/// pushed to `found`.
pub(super) fn to_nat_casts_removed(t: &Printed, found: &mut Vec<Printed>) -> Printed {
    use super::super::doc::{LeanType, TermKind};
    use super::super::templates::Num;
    if let TermKind::Cast {
        inner,
        to: LeanType::Num(Num::Int),
    } = &t.kind
    {
        if let TermKind::ToNat(u) = &unparenthesized(inner).kind {
            found.push((**u).clone());
            return (**u).clone();
        }
    }
    let mut out = t.clone();
    for c in out.children_mut() {
        *c = to_nat_casts_removed(c, found);
    }
    out
}

/// The two sets of a subset, `A ⊆ B`; None of anything else.
pub(super) fn subset_sides(says: &Printed) -> Option<(Printed, Printed)> {
    match &unparenthesized(says).kind {
        super::super::doc::TermKind::Infix { op, lhs, rhs } if op.symbol == "⊆" => {
            Some(((**lhs).clone(), (**rhs).clone()))
        }
        _ => None,
    }
}

/// The range a term is, `Finset.Icc` or `Set.Icc`, of the set itself or of
/// a membership of it; None of anything else.
pub(super) fn range_head(t: &Printed) -> Option<&'static str> {
    use super::super::doc::TermKind;
    let set = match &bare_term(t).kind {
        TermKind::Infix { op, rhs, .. } if op.symbol == "∈" => bare_term(rhs),
        _ => bare_term(t),
    };
    let TermKind::App { head, .. } = &set.kind else {
        return None;
    };
    ["Finset.Icc", "Set.Icc"]
        .into_iter()
        .find(|name| is_constant(head, name))
}

/// Whether `t` says a term is in a set listed by its members, `x ∈ {1, 2}`.
pub(super) fn listed_membership(t: &Printed) -> bool {
    use super::super::doc::{Brackets, TermKind};
    matches!(
        &bare_term(t).kind,
        TermKind::Infix { op, rhs, .. } if op.symbol == "∈"
            && matches!(&bare_term(rhs).kind, TermKind::Listed { brackets: Brackets::Brace, .. })
    )
}

/// Whether `t` says two pairs are equal, `((a, b) : ℝ × ℝ) = (c, d)`.
pub(super) fn pair_equation(t: &Printed) -> bool {
    use super::super::doc::{Brackets, TermKind};
    let pair = |side: &Printed| {
        let side = match &bare_term(side).kind {
            TermKind::Cast { inner, .. } => bare_term(inner),
            _ => bare_term(side),
        };
        matches!(
            &side.kind,
            TermKind::Listed {
                brackets: Brackets::Round,
                ..
            }
        )
    };
    matches!(
        &bare_term(t).kind,
        TermKind::Infix { op, lhs, rhs } if op.symbol == "=" && pair(lhs) && pair(rhs)
    )
}

/// Whether `t` is the constant `name`, `(Set.univ : Set ℝ)` of `Set.univ`.
pub(super) fn is_constant(t: &Printed, name: &str) -> bool {
    matches!(&bare_term(t).kind, super::super::doc::TermKind::Const(c) if c.name == name)
}

/// The set a statement `Set.MapsTo f X Y` says the map takes X into, Y;
/// None for any other statement.
pub(super) fn maps_to_codomain(statement: &Printed) -> Option<&Printed> {
    use super::super::doc::{Arg, TermKind};
    let TermKind::App { head, args, .. } = &bare_term(statement).kind else {
        return None;
    };
    let [.., Arg::Explicit(to)] = args.as_slice() else {
        return None;
    };
    is_constant(head, "Set.MapsTo").then_some(to)
}

/// Whether `statement` is `Set.MapsTo f X Y`.
pub(super) fn is_maps_to(statement: &Printed) -> bool {
    maps_to_codomain(statement).is_some()
}

/// Whether `term` writes a set by a condition, `{n : ℤ | 0 < n}`.
pub(super) fn has_set_builder(term: &Printed) -> bool {
    term.walk().iter().any(|t| {
        matches!(
            &t.kind,
            super::super::doc::TermKind::Bound {
                form: super::super::doc::BoundForm::SetOf,
                ..
            }
        )
    })
}

/// Whether an item's statement, as the writer prints it, counts a set: its
/// count stands in the writer's type, ℤ, where Lean takes the item's own,
/// ℕ or ℕ∞, so no line is known to say it from its printed form.
pub(super) fn item_counts(statement: &Printed) -> bool {
    use super::super::doc::CountForm::{Extended, Natural};
    statement.has_count(Natural) || statement.has_count(Extended)
}

/// What a forward reading of an "if and only if" or an "if" reaches, `B` of
/// `A ↔ B` and of `A → B`; None for another statement.
pub(super) fn consequent(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::super::doc::TermKind::Paren(inner) => consequent(inner),
        super::super::doc::TermKind::Infix { op, rhs, .. }
            if matches!(op.symbol, "↔" | "→") =>
        {
            Some((**rhs).clone())
        }
        _ => None,
    }
}

/// The side a backward reading of a definition reaches, `A` of "A if and
/// only if B", as the page's tree has it; None for another sentence.
pub(super) fn node_antecedent(sentence: &Node) -> Option<&Node> {
    match (sentence.notation(), sentence.children.as_slice()) {
        (BICONDITIONAL, [left, _]) => Some(left),
        _ => None,
    }
}

/// The side a forward reading of a sentence reaches, `B` of "A if and only
/// if B" or of "if A then B", as the page's tree has it; None for another
/// sentence.
pub(super) fn node_consequent(sentence: &Node) -> Option<&Node> {
    match (sentence.notation(), sentence.children.as_slice()) {
        (BICONDITIONAL | CONDITIONAL | IMPLICATION, [_, right]) => Some(right),
        _ => None,
    }
}

/// The part of an "and" a projection path takes, `.1.2`, as the page's tree
/// nests the "and" (`leaf_path`); None where the sentence has no such part.
pub(super) fn node_along<'n>(
    sentence: &'n Node,
    path: &[&str],
    w: &Writer,
) -> Option<&'n Node> {
    let mut at = sentence;
    for side in path {
        let (l, r) = w.and_sides(at)?;
        at = match *side {
            "1" => l,
            _ => r,
        };
    }
    Some(at)
}

/// The part of an "and" a projection path takes, `.1.2`, as Lean writes the
/// "and"; None where the statement has no such part.
pub(super) fn along(statement: &Printed, path: &[&str]) -> Option<Printed> {
    let mut at = statement.clone();
    for side in path {
        let (l, r) = and_sides(&at)?;
        at = match *side {
            "1" => l,
            _ => r,
        };
    }
    Some(at)
}

/// The right side of an "if and only if", `B` of `A ↔ B`; None for another
/// statement.
pub(super) fn right_side(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::super::doc::TermKind::Paren(inner) => right_side(inner),
        super::super::doc::TermKind::Infix { op, rhs, .. } if op.symbol == "↔" => {
            Some((**rhs).clone())
        }
        _ => None,
    }
}

/// A "there is" given its witness `value`: what its guard then says, where
/// it has one, and its body at the witness; nothing known of either where
/// `statement` is no "there is" over a type, or is not known.
pub(super) fn exists_at(
    statement: Option<&Printed>,
    value: &Printed,
) -> (Option<Printed>, Option<Printed>) {
    use super::super::doc::{Quant, TermKind};
    let Some(statement) = statement else {
        return (None, None);
    };
    match &statement.kind {
        TermKind::Paren(inner) => exists_at(Some(inner), value),
        TermKind::Quantified {
            quant: Quant::Exists,
            letter,
            guard,
            body,
            ..
        } => {
            let at =
                |t: &Printed| super::super::doc::forms::substituted(t, letter, value);
            (guard.as_deref().map(at), Some(at(body)))
        }
        _ => (None, None),
    }
}

/// The symbol of the relation `statement` states, `<` of `0 < x`; None for
/// a statement that is no relation of two sides.
pub(super) fn relation_symbol(statement: &Printed) -> Option<&'static str> {
    match &unparenthesized(statement).kind {
        super::super::doc::TermKind::Infix { op, .. } => Some(op.symbol),
        _ => None,
    }
}

/// `proof` of an order turned by `lemma`, `gt_iff_lt.mp h` of `h : a > b`
/// saying `b < a`.
pub(super) fn turned_order(lemma: &str, proof: Printed) -> Printed {
    Printed::applied(
        lemma,
        super::super::doc::Source::Core,
        vec![proof],
        super::super::doc::LeanType::Prop,
    )
}

/// `term` with its outer brackets taken off.
pub(super) fn unparenthesized(term: &Printed) -> Printed {
    match &term.kind {
        super::super::doc::TermKind::Paren(inner) => unparenthesized(inner),
        _ => term.clone(),
    }
}

/// How many statements Lean's `statement` joins by "and", each function
/// applied taken as its body at its value: `L k ∈ Set.univ ∧ (fun y => ∃ k,
/// …) (L k)` joins two.
pub(super) fn lean_conjuncts(statement: &Printed) -> usize {
    let at = super::super::doc::forms::beta_reduced(&unparenthesized(statement));
    match &at.kind {
        super::super::doc::TermKind::Infix { op, lhs, rhs } if op.symbol == "∧" => {
            lean_conjuncts(lhs) + lean_conjuncts(rhs)
        }
        _ => 1,
    }
}

/// Whether `part` is a fact that a term is in a number system that is a
/// Lean type, ℤ or ℝ, which Lean states by the term's type and not as a
/// fact.
pub(super) fn type_membership(part: &Unfolded) -> bool {
    let Unfolded::Fact { fact, .. } = part else {
        return false;
    };
    match (fact.notation(), fact.children.as_slice()) {
        (crate::notations::MEMBERSHIP, [_, set]) => matches!(
            super::super::expr::system_of(set),
            Some(super::super::expr::System::Type(_))
        ),
        _ => false,
    }
}

/// The proofs `first`, then `rest`, as one anonymous constructor: `rest`'s
/// own parts where it is one, as Lean's "and" and "there is" nest to the
/// right; `first`'s one proof alone where `rest` adds nothing.
pub(super) fn joined(mut first: Vec<Printed>, rest: Printed) -> Printed {
    match rest.kind {
        super::super::doc::TermKind::Listed {
            brackets: super::super::doc::Brackets::Angle,
            items,
        } => first.extend(items),
        _ => first.push(rest),
    }
    super::super::expr::anonymous(first)
}

/// The side of an "if and only if" or an "if" a forward reading starts
/// from, `A` of `A ↔ B` and of `A → B`; None for another statement.
pub(super) fn left_side(statement: &Printed) -> Option<Printed> {
    match &statement.kind {
        super::super::doc::TermKind::Paren(inner) => left_side(inner),
        super::super::doc::TermKind::Infix { op, lhs, .. }
            if matches!(op.symbol, "↔" | "→") =>
        {
            Some((**lhs).clone())
        }
        _ => None,
    }
}

/// A term taken along a projection path, `(t).1.2`.
pub(super) fn projected(term: Printed, path: &[&str]) -> Printed {
    path.iter()
        .fold(super::super::tactics::bracket(term), |inner, field| {
            Printed {
                kind: super::super::doc::TermKind::Field {
                    inner: Box::new(inner),
                    field: field.to_string(),
                },
                ty: None,
            }
        })
}

/// The fields that take sentence `i` of `n` joined by `∧`, which chains to
/// the right: `["1"]`, `["2", "1"]`, …, and the last `["2", "2", …]`.
pub(super) fn projection_path(i: usize, n: usize) -> Vec<&'static str> {
    if n == 1 {
        return Vec::new();
    }
    let mut out = vec!["2"; i];
    if i + 1 < n {
        out.push("1");
    }
    out
}

/// A term's fields taken in turn, `h.2.1`.
pub(super) fn fields(term: Printed, path: &[&str]) -> Printed {
    path.iter().fold(term, |inner, field| Printed {
        kind: super::super::doc::TermKind::Field {
            inner: Box::new(inner),
            field: field.to_string(),
        },
        ty: None,
    })
}

/// The letters that tell the parts of one line apart, by the part's place
/// from 0: a, …, z, then aa, ab, …, as a graph given in full asserts more
/// than twenty-six facts in one line.
pub(super) fn part_suffix(k: usize) -> String {
    let letter = |i: usize| (b'a' + (i % 26) as u8) as char;
    match k < 26 {
        true => letter(k).to_string(),
        false => format!("{}{}", part_suffix(k / 26 - 1), letter(k)),
    }
}

/// Each `let` and `assume` line of a theorem, by its label, with each of
/// its sentences and the Lean name of the hypothesis it is: the label, or
/// `H3a`, `H3b` for a line of several sentences.
pub(super) fn hypothesis_sentences(
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Vec<(String, Vec<LineSentence>)> {
    let mut out = Vec::new();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
        let mut nodes: Vec<(usize, Node)> = h
            .body(&thm.path)
            .sentences()
            .iter()
            .enumerate()
            .filter_map(|(at, s)| rec.page.get(s).map(|n| (at, n.clone())))
            .collect();
        // A `let` the page does not read as a formula, `f : A → B be
        // one-to-one`, says what the checker reads it to assert.
        if nodes.is_empty() {
            nodes = rec
                .asserted
                .get(i)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .enumerate()
                .collect();
        }
        let base = line_name(&label);
        let n = nodes.len();
        let said = nodes
            .into_iter()
            .enumerate()
            .map(|(k, (at, node))| {
                let name = if n == 1 {
                    base.clone()
                } else {
                    format!("{base}{}", part_suffix(k))
                };
                LineSentence::named(at, node, name)
            })
            .collect();
        out.push((label, said));
    }
    out
}

/// A tree of the statement with each name a define of it, or of its file,
/// gives written out as the term it names, as the checker reads the
/// statement (`CheckedTheorem::statement_definitions`).
pub(super) fn defined_out(node: &Node, rec: &CheckedTheorem, writer: &Writer) -> Node {
    let put: crate::matching::Binding = rec
        .statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => {
                Some((crate::formula::symbol::Symbol::of(name), t.clone()))
            }
            crate::matching::Defined::Rule(_) => None,
        })
        .collect();
    if put.is_empty() {
        return node.clone();
    }
    // A define's term may name one defined before it, E = {c ∈ O : …} of an
    // O defined above: put again while a define's name is left in the
    // tree, once for each define at most.
    let binders = writer.grammar.binders();
    let named = |n: &Node| {
        crate::matching::free_names(n, &binders)
            .iter()
            .any(|name| put.contains_key(&crate::formula::symbol::Symbol::of(name)))
    };
    let mut out = node.clone();
    for _ in 0..put.len() {
        if !named(&out) {
            break;
        }
        out = crate::matching::substitute_apart_by(&out, &put, &binders);
    }
    out
}

/// The defines a theorem's statement is read with, each a name and the term
/// it stands for, in the order defined.
pub(super) fn statement_terms(rec: &CheckedTheorem) -> Vec<(String, Node)> {
    rec.statement_definitions
        .iter()
        .filter_map(|(name, d)| match d {
            crate::matching::Defined::Term(t) => Some((name.clone(), t.clone())),
            crate::matching::Defined::Rule(_) => None,
        })
        .collect()
}

/// What a citation gives an item's things (`Proof::things_given`).
#[derive(Default)]
pub(super) struct ThingsGiven {
    /// The least type that holds the numbers given each type variable's
    /// things, by the variable.
    pub(super) at: std::collections::BTreeMap<usize, super::super::templates::Num>,
    /// The type variables whose sets are given sets of numbers, X := {2n :
    /// n ∈ ℤ}.
    pub(super) numbers: std::collections::BTreeSet<usize>,
    /// What the members are of a set given for each type variable's set
    /// where they are not numbers, sets of integers of X := {e ⊆ {1, …, m}
    /// : |e| = m}.
    pub(super) others: std::collections::BTreeMap<usize, super::super::expr::Members>,
}

impl ThingsGiven {
    /// What an item's members are here, its things given numbers or sets
    /// put for them at any depth: a property of sets of α, given sets of
    /// integers, is one of `Set ℤ`. `at` is the type each variable's
    /// numbers are taken at.
    pub(super) fn put(
        &self,
        members: &super::super::expr::Members,
        at: &dyn Fn(&usize) -> super::super::templates::Num,
    ) -> super::super::expr::Members {
        use super::super::expr::Members;
        match members {
            Members::Things(var) if self.numbers.contains(var) => {
                Members::Numbers(at(var))
            }
            Members::Things(var) if self.others.contains_key(var) => {
                self.others[var].clone()
            }
            Members::Sets(inner) => Members::Sets(Box::new(self.put(inner, at))),
            other => other.clone(),
        }
    }

    pub(super) fn raise(&mut self, var: usize, n: super::super::templates::Num) {
        let at = self.at.entry(var).or_insert(n);
        *at = (*at).max(n);
    }
}

/// What a theorem states, in Lean.
pub(super) struct Statement {
    /// Its binders, from its `let` and `assume` lines.
    pub(super) binders: Vec<Binder>,
    /// Each sentence of its `then` line.
    pub(super) conclusion: Vec<Concluded>,
}

/// One sentence a theorem concludes: its tree, and its Lean text.
pub(super) struct Concluded {
    pub(super) says: Node,
    pub(super) prop: Printed,
}

/// The number type of `let A be an element` where later lines say A is in
/// sets of numbers, A ∈ ℝ ∖ ℚ: the widest of those sets' types, as the
/// checker records it (`CheckedTheorem::element_systems`). None where no
/// line puts A in a set of numbers.
pub(super) fn element_number_type(
    name: &str,
    rec: &CheckedTheorem,
) -> Option<LetterType> {
    let system = rec.element_systems.get(name)?;
    Some(LetterType::Number(super::super::expr::recorded_set_type(
        *system,
    )))
}

/// The type of `let T be a set` where T is a set of numbers the checker
/// records the system of, T of {1, …, i} ∩ T or D of D ⊆ ℝ
/// (`CheckedTheorem::set_systems`): a set of those. None where it records
/// none.
pub(super) fn recorded_number_set_type(
    name: &str,
    rec: &CheckedTheorem,
) -> Option<LetterType> {
    let system = rec.set_systems.get(name)?;
    Some(LetterType::Set(super::super::expr::Members::Numbers(
        super::super::expr::recorded_set_type(*system),
    )))
}

/// A theorem's binders, from its `let` and `assume` lines, and each
/// sentence of its `then` line with its Lean text.
/// A function the header lets by its value, `let f(x) = 2x + 1, for x ∈ ℝ`:
/// as the page reads a let, a letter of the type the value computes in,
/// taking the domain's numbers (integers for ℕ, ℕ₀ or a range, as the
/// writer's sequences do), and the equation for every x as one hypothesis
/// named by the label.
/// A function the header lets by its value, as read: the set its argument
/// is in, its value, what the argument is among, and the argument's
/// membership in the set, where the value is read.
pub(super) struct HeaderReading {
    pub(super) domain: Node,
    pub(super) body: Node,
    pub(super) takes: super::super::expr::Members,
    pub(super) member: Node,
}

/// What `header_function` reads of a function the header lets, and the
/// read-back counts the arithmetic of alike.
pub(super) fn header_reading(
    writer: &Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<HeaderReading> {
    use super::super::templates::Num;
    let sets = set_valued(rec, &def.name);
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let read: Vec<&Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == d.line)
        .map(|(_, node)| node)
        .collect();
    // The domain: a number system or range written in the line, or a set,
    // a letter or a set the header itself defines, written out.
    let domain = match read.iter().copied().find(|n| system_or_range(n)) {
        Some(n) => n.clone(),
        None => {
            let sets: Vec<&Node> = read
                .iter()
                .copied()
                .filter(|n| !(n.is_name() && *n.text == *param.name))
                .filter(|n| {
                    let out = defined_out(n, rec, writer);
                    writer.set_members(&out).is_some()
                })
                .collect();
            match sets.as_slice() {
                [one] => defined_out(one, rec, writer),
                _ => {
                    return Route::no(
                        "a function the header lets on no set Lean has a type for",
                    )
                }
            }
        }
    };
    let bodies: Vec<&Node> = read
        .iter()
        .copied()
        .filter(|n| !system_or_range(n))
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        // A value that is a set, V(k) = {S ⊆ {1, …, k} : k ∈ S}, is the set
        // that names the argument; any other value is no set.
        .filter(|n| match sets {
            true => n.names().iter().any(|m| *m == *param.name),
            false => writer.set_members(&defined_out(n, rec, writer)).is_none(),
        })
        .collect();
    // A value that is the argument itself, f(n) = n, is read once with it.
    let identity = read
        .iter()
        .copied()
        .find(|n| n.is_name() && *n.text == *param.name);
    let body = match (bodies.as_slice(), identity) {
        ([body], _) => *body,
        ([], Some(arg)) => arg,
        _ => {
            return Route::no(
                "a function the header lets whose value did not read as one term",
            )
        }
    };
    // What it takes: the domain's numbers, integers for ℕ, ℕ₀ or a range
    // as the writer's sequences take; or the things of a set of things.
    let takes = match super::super::expr::system_of(&domain) {
        Some(system) => super::super::expr::Members::Numbers(
            super::super::expr::letter_type(system).max(Num::Int),
        ),
        None if domain.notation() == crate::notations::INTEGER_RANGE => {
            super::super::expr::Members::Numbers(Num::Int)
        }
        None => match writer.set_members(&domain) {
            Some(m) => m,
            None => {
                return Route::no(
                    "a function the header lets on no set Lean has a type for",
                )
            }
        },
    };
    let x = Node::name(crate::formula::Sort::none(), &param.name);
    let member = Node::of(
        crate::notations::IN,
        crate::formula::Sort::none(),
        vec![x, domain.clone()],
    );
    Route::Built(HeaderReading {
        domain,
        body: body.clone(),
        takes,
        member,
    })
}

impl HeaderReading {
    /// The writer the value is read with: the argument of what it takes,
    /// knowing it is in the set, √x of x ∈ {y ∈ ℝ : y > 0} the real square
    /// root.
    pub(super) fn inside<'a>(&self, writer: &Writer<'a>, param: &str) -> Writer<'a> {
        let mut w = writer.with_letters(writer.letters.clone());
        w.letters.insert(param.to_string(), self.takes.letter());
        w.knowing(std::slice::from_ref(&self.member))
    }
}

pub(super) fn header_function(
    writer: &mut Writer,
    d: &crate::corpus::DefineLine,
    def: &crate::corpus::Define,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::super::templates::Num;
    let HeaderReading {
        domain,
        body,
        takes,
        member,
    } = match header_reading(writer, d, def, rec) {
        Route::Built(r) => r,
        Route::Declined(d) => return Route::Declined(d),
    };
    let [param] = def.params.as_slice() else {
        return Route::no("a function the header lets of more than one argument");
    };
    let body = &body;
    let before = writer.letters.insert(param.name.clone(), takes.letter());
    // Said for every x of the domain: all of a type, or each member of a
    // set, x ∈ D, as the writer writes that membership.
    let whole_type = matches!(
        super::super::expr::system_of(&domain),
        Some(super::super::expr::System::Type(_))
    );
    let guard = match whole_type {
        true => Route::Built(None),
        false => writer.formula(&member).map(Some),
    };
    // The value is read where x is in the domain: √x of x ∈ {y ∈ ℝ : y >
    // 0} the real square root.
    let inside = writer.knowing(std::slice::from_ref(&member));
    // A function of a real or complex argument gives values of at least
    // that type, as continuity and derivatives read it: a step of 0 and 1
    // on [0, 1] is a function into ℝ.
    let value = match &takes {
        // Values that are sets: a map to sets of the value's members.
        m if set_valued(rec, &def.name) => match inside.members_of(body) {
            Some(members) => inside.set_term(body).map(|v| {
                (
                    LetterType::Map {
                        from: m.clone(),
                        to: super::super::expr::Members::Sets(Box::new(members)),
                    },
                    v,
                )
            }),
            None => {
                Route::no("a function the header lets whose value has no Lean type")
            }
        },
        super::super::expr::Members::Numbers(from) => match inside.carrier(body) {
            Route::Built(to) => {
                let to = match *from >= Num::Real {
                    true => to.max(*from),
                    false => to,
                };
                inside
                    .number_fixed(body, to)
                    .map(|v| (LetterType::Function { from: *from, to }, v))
            }
            Route::Declined(why) => Route::Declined(why),
        },
        m => match writer.member_kind(body) {
            Some(to) => writer.set_term(body).map(|v| {
                (
                    LetterType::Map {
                        from: m.clone(),
                        to,
                    },
                    v,
                )
            }),
            None => {
                Route::no("a function the header lets whose value has no Lean type")
            }
        },
    };
    match before {
        Some(ty) => writer.letters.insert(param.name.clone(), ty),
        None => writer.letters.shift_remove(&param.name),
    };
    let ((ty, value), guard) = match (value, guard) {
        (Route::Built(v), Route::Built(g)) => (v, g),
        (Route::Declined(why), _) | (_, Route::Declined(why)) => {
            return Route::Declined(why)
        }
    };
    writer.letters.insert(def.name.clone(), ty.clone());
    // On a set, D ∖ {c}: that set is its domain, within which its images,
    // preimages and limits are taken (`domain_of`).
    if !whole_type {
        let written = match &takes {
            super::super::expr::Members::Numbers(n) => writer.numbers_at(&domain, *n),
            _ => writer.set_term(&domain),
        };
        match written {
            Route::Built(p) => {
                writer.domains.insert(def.name.clone(), p);
            }
            Route::Declined(why) => return Route::Declined(why),
        }
    }
    let f = super::super::names::letter(&def.name);
    let x = super::super::names::letter(&param.name);
    // ∀ x : T, guard → f x = value.
    let takes_ty = takes.letter().lean_type();
    let applied = Printed {
        kind: super::super::doc::TermKind::App {
            head: Box::new(Printed::letter(f.clone(), ty.lean_type())),
            args: vec![super::super::doc::Arg::Explicit(Printed::letter(
                x.clone(),
                takes_ty.clone(),
            ))],
            explicit: false,
        },
        ty: value.ty.clone(),
    };
    let says = Printed::of(
        super::super::doc::TermKind::Quantified {
            quant: super::super::doc::Quant::ForAll,
            letter: x,
            letter_ty: takes_ty,
            guard: guard.map(Box::new),
            body: Box::new(Printed::infix(
                super::super::doc::Op::EQUALS,
                applied,
                value,
                super::super::doc::LeanType::Prop,
            )),
            bounded: false,
        },
        super::super::doc::LeanType::Prop,
    );
    Route::Built(vec![
        Binder::Letter {
            name: f.clone(),
            page: def.name.clone(),
            general: false,
            ty,
        },
        Binder::Fact {
            name: line_name(&d.label),
            says,
            at: None,
        },
    ])
}

/// One function's rules of a recursion, as the checker read them: its name,
/// its value at 0, and its value at k + 1.
pub(super) struct RecursionRule<'r> {
    pub(super) name: &'r String,
    pub(super) start: Node,
    pub(super) step: Node,
}

/// Each function's rules of a recursion, as the checker read them.
pub(super) fn recursion_rules<'r>(
    r: &'r crate::corpus::Recursion,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Route<Vec<RecursionRule<'r>>> {
    let mut out = Vec::new();
    for name in &r.names {
        let (Some(start), Some(step)) = (
            r.start.get(name).and_then(|rule| rule_tree(rule, d, rec)),
            r.step.get(name).and_then(|rule| rule_tree(rule, d, rec)),
        ) else {
            return Route::no(format!(
                "a recursion whose rules for {name} did not read"
            ));
        };
        out.push(RecursionRule { name, start, step });
    }
    Route::Built(out)
}

/// A rule of a recursion as the checker read it; None where it read none.
pub(super) fn rule_tree(
    rule: &crate::corpus::RuleText,
    d: &crate::corpus::DefineLine,
    rec: &CheckedTheorem,
) -> Option<Node> {
    match rule.written(&d.path, d.line).sentences().as_slice() {
        [one] => rec.page.get(one).cloned(),
        _ => None,
    }
}

/// The arithmetic the page writes in the recursions a theorem's header
/// lets, as their hypothesis states them (`header_recursions`): each rule's
/// value, and the k + 1 each function is applied to in its step.
pub(super) fn recursion_arithmetic(
    writer: &Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> std::collections::BTreeMap<String, usize> {
    let mut out = std::collections::BTreeMap::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function the header lets by its value: the value, which its
            // hypothesis states (`header_function`). One of several
            // arguments is written out, and has no hypothesis.
            Route::Built(crate::corpus::DefineParts::One(one))
                if one.params.len() == 1 =>
            {
                let values: Vec<Node> = rec
                    .page
                    .entries()
                    .filter(|(key, _)| key.line == d.line)
                    .map(|(_, n)| n.clone())
                    .filter(|n| {
                        !matches!(
                            n.notation(),
                            crate::notations::NUMBER_SYSTEMS
                                | crate::notations::INTEGER_RANGE
                        )
                    })
                    .filter(|n| !n.is_name())
                    .collect();
                // The value as `header_function` reads it, knowing its
                // argument is in the set; the rest as it stands.
                let reading = header_reading(writer, d, &one, rec).built();
                let (inside, rest): (Vec<Node>, Vec<Node>) =
                    values.into_iter().partition(|n| {
                        reading.as_ref().is_some_and(|r| {
                            writer.grammar.print(&r.body) == writer.grammar.print(n)
                        })
                    });
                let mut counts = super::super::readback::page_arithmetic(writer, &rest);
                if let (Some(r), [param]) = (&reading, one.params.as_slice()) {
                    let w = r.inside(writer, &param.name);
                    for (op, n) in super::super::readback::page_arithmetic(&w, &inside)
                    {
                        *counts.entry(op).or_insert(0) += n;
                    }
                }
                for (op, n) in counts {
                    *out.entry(op).or_insert(0) += n;
                }
                continue;
            }
            _ => continue,
        };
        let Route::Built(rules) = recursion_rules(&r, d, rec) else {
            continue;
        };
        let values: Vec<Node> = rules
            .iter()
            .flat_map(|rule| [rule.start.clone(), rule.step.clone()])
            .collect();
        for (op, n) in super::super::readback::page_arithmetic(writer, &values) {
            *out.entry(op).or_insert(0) += n;
        }
        *out.entry("addition".to_string()).or_insert(0) += rules.len();
    }
    out
}

/// The recursions a theorem's header lets,
/// `let F(0) = 0, G(0) = 1, F(k + 1) = G(k), G(k + 1) = F(k) + G(k), for k ∈ ℕ₀`:
/// as the page reads a let,
/// letters for its functions, of ℤ into the type its rules compute in, and
/// its rules one hypothesis named by its label, its step for k ≥ 0. Of
/// every pair F, G the rules hold of, which agree from 0 on, the theorem
/// says what it says of the Fibonacci numbers. A recursion from 1, over ℕ,
/// is declined.
pub(super) fn header_recursions(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Vec<Binder>> {
    use super::super::templates::Num;
    let mut out = Vec::new();
    for d in thm.defines.iter().filter(|d| d.line < thm.conclusion_line) {
        let r = match crate::corpus::define_parts(&d.text) {
            Route::Built(crate::corpus::DefineParts::Recursion(r)) => r,
            // A function of more than one argument is written out where it is
            // applied (`checker::written`), and has no binder.
            Route::Built(crate::corpus::DefineParts::One(one))
                if one.params.len() > 1 =>
            {
                continue
            }
            // A function the header lets by its value, f(x) = 2x + 1, for x
            // ∈ ℝ: a function letter, and that equation for every x.
            Route::Built(crate::corpus::DefineParts::One(one))
                if !one.params.is_empty() =>
            {
                match header_function(writer, d, &one, rec) {
                    Route::Built(b) => {
                        out.extend(b);
                        continue;
                    }
                    Route::Declined(why) => return Route::Declined(why),
                }
            }
            _ => continue,
        };
        if r.domain.trim() != "ℕ₀" {
            return Route::no("a recursion over other than ℕ₀");
        }
        let rules = match recursion_rules(&r, d, rec) {
            Route::Built(rules) => rules,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The functions take integers, as the writer's sequences do, so
        // that F(k) of a sum's index is written as it stands; the rules say
        // what they are from 0. What they give is the type their rules
        // compute in, an integer at least.
        let index = r.index.clone();
        let before = writer
            .letters
            .insert(index.clone(), LetterType::Number(Num::Int));
        let mut to = Num::Int;
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        for rule in &rules {
            for n in [&rule.start, &rule.step] {
                match writer.carrier(n) {
                    Route::Built(c) => to = to.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        for name in &r.names {
            writer
                .letters
                .insert(name.clone(), LetterType::Function { from: Num::Int, to });
        }
        use super::super::doc::{LeanType, Op};
        let int = LeanType::Num(Num::Int);
        let k = super::super::names::letter(&index);
        let mut starts = Vec::new();
        let mut steps = Vec::new();
        for rule in &rules {
            let f = super::super::names::letter(rule.name);
            let (s, t) = match (
                writer.number_fixed(&rule.start, to),
                writer.number_fixed(&rule.step, to),
            ) {
                (Route::Built(s), Route::Built(t)) => (s, t),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
            let at = |arg: Printed| applied_to(super::super::tactics::hyp(&f), arg);
            let next = Printed::infix(
                Op::PLUS,
                super::super::tactics::hyp(&k),
                Printed::numeral("1", int.clone()),
                int.clone(),
            );
            starts.push(Printed::infix(
                Op::EQUALS,
                at(Printed::numeral("0", int.clone())),
                s,
                LeanType::Prop,
            ));
            steps.push(Printed::infix(Op::EQUALS, at(next), t, LeanType::Prop));
        }
        match before {
            Some(ty) => writer.letters.insert(index.clone(), ty),
            None => writer.letters.shift_remove(&index),
        };
        for name in &r.names {
            out.push(Binder::Letter {
                name: super::super::names::letter(name),
                page: name.clone(),
                general: false,
                ty: LetterType::Function { from: Num::Int, to },
            });
        }
        out.push(Binder::Fact {
            name: line_name(&d.label),
            says: rules_said(&k, starts, steps),
            at: Some(StatedAt::Recursion(d.label.clone())),
        });
    }
    Route::Built(out)
}

/// Hypothesis sentences, each its tree and its Lean name, as `binders`
/// takes them.
/// A hypothesis sentence of a theorem as its statement states it.
pub(super) struct StatedHypothesis {
    /// The sentence with the defines written out (`defined_out`).
    pub(super) node: Node,
    /// Its Lean name.
    pub(super) name: String,
    pub(super) at: crate::citing::HypothesisAt,
}

pub(super) fn asked_of(written: &[StatedHypothesis]) -> Vec<Asked<'_>> {
    written
        .iter()
        .map(|h| Asked {
            node: &h.node,
            name: h.name.clone(),
            at: h.at,
        })
        .collect()
}
