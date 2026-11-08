//! Whether two statements write one term in one form: what a citation's
//! item says once its letters are given, and the line it proves.
//!
//! The two are compared node by node. Where they part, the place is
//! reported if it is one of the forms the writer chooses: a count taken in
//! ℕ or in ℕ∞, a whole number taken to ℕ or not, a term cast to one type or
//! another. Any other parting, a sentence the item says otherwise than the
//! line, is no question of form and is not reported.

use super::term::{Arg, CountForm, LeanType, Piece, Term, TermKind};
use crate::lean::templates::Num;

/// One place two statements write a term in different forms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormDifference {
    /// A count, `ncard` in one and `encard` in the other, of one set as each
    /// writes it, which may differ inside in form.
    Count {
        item: CountForm,
        line: CountForm,
        item_set: Term,
        line_set: Term,
    },
    /// A whole number taken to ℕ, `n.toNat`, in one and not the other.
    ToNat { in_item: bool },
    /// A term cast to a type in one and not, or to another, in the other.
    Cast {
        item: Option<LeanType>,
        line: Option<LeanType>,
    },
}

impl FormDifference {
    /// What differs, in words.
    pub fn describe(&self) -> String {
        let count = |f: &CountForm| match f {
            CountForm::Natural => "a natural number (ncard)",
            CountForm::Extended => "in ℕ∞ (encard)",
        };
        let cast = |t: &Option<LeanType>| match t {
            Some(t) => format!("cast to {}", t.text()),
            None => "not cast".to_string(),
        };
        match self {
            FormDifference::Count { item, line, .. } => format!(
                "a count the item writes {} and the line {}",
                count(item),
                count(line)
            ),
            FormDifference::ToNat { in_item: true } => {
                "a whole number the item takes to ℕ (.toNat) and the line does not"
                    .to_string()
            }
            FormDifference::ToNat { in_item: false } => {
                "a whole number the line takes to ℕ (.toNat) and the item does not"
                    .to_string()
            }
            FormDifference::Cast { item, line } => format!(
                "a term the item writes {} and the line {}",
                cast(item),
                cast(line)
            ),
        }
    }
}

/// Every place the item's statement and the line write one term in
/// different forms; none where they agree. A cast is first taken down onto
/// the parts of what it casts on both sides, as `push_cast` takes it:
/// `((a - b : ℤ) : ℚ)` and `(a : ℚ) - (b : ℚ)` are one form, which Lean
/// moves between by that one tactic, and only a difference it leaves is a
/// form the writer chose. A relation one side states in a narrower type
/// than the other, sin(a + b) = … over ℂ cited by a line in ℝ, or an item
/// in ℤ cited by a row of a calculation in ℚ, is compared cast up to the
/// wider, as `exact_mod_cast` takes the one to the other.
///
/// `widen` gives the constant that is a library function at another type,
/// `Complex.cos` of `Real.cos` at ℂ (`Templates::same_function_at`): a
/// cast of the function's value is the function of the cast argument.
pub fn differences(item: &Term, line: &Term, widen: &Widen) -> Vec<FormDifference> {
    let mut out = Vec::new();
    let (item, line) = (pushed(item, widen), pushed(line, widen));
    let (item, line) = (in_naturals(&item), in_naturals(&line));
    let line = lifted(&line, &item, widen).unwrap_or(line);
    let item = lifted(&item, &line, widen).unwrap_or(item);
    compare(&item, &line, &mut out);
    out
}

/// A relation between natural numbers cast to one type, `(a : ℤ) ≤ (b :
/// ℤ)` or `(a : ℕ∞) = (1 : ℕ∞)`, as the relation in ℕ itself, `a ≤ b`,
/// which `norm_cast` takes it to (`Nat.cast_le`, `Nat.cast_inj`); any
/// other term as it is.
fn in_naturals(term: &Term) -> Term {
    let natural = |t: &Term| -> Option<Term> {
        match &bare(t).kind {
            TermKind::Cast { inner, .. }
                if inner.ty == Some(LeanType::Num(Num::Nat)) =>
            {
                Some((**inner).clone())
            }
            TermKind::Numeral(d) => Some(Term::of(
                TermKind::Numeral(d.clone()),
                LeanType::Num(Num::Nat),
            )),
            _ => None,
        }
    };
    if let TermKind::Infix { op, lhs, rhs } = &bare(term).kind {
        if term.ty == Some(LeanType::Prop) {
            if let (Some(l), Some(r)) = (natural(lhs), natural(rhs)) {
                return Term::of(
                    TermKind::Infix {
                        op: *op,
                        lhs: Box::new(l),
                        rhs: Box::new(r),
                    },
                    LeanType::Prop,
                );
            }
        }
    }
    term.clone()
}

/// Whether the line is the item's equation turned round: its left side
/// alike the item's right and not its left, but for forms.
pub fn turned_round(item: &Term, line: &Term) -> bool {
    use super::term::Op;
    match (&bare(item).kind, &bare(line).kind) {
        (
            TermKind::Infix {
                op: a,
                lhs: il,
                rhs: ir,
            },
            TermKind::Infix {
                op: b,
                lhs: ll,
                rhs: lr,
            },
        ) => {
            *a == Op::EQUALS
                && a == b
                && alike(il, lr)
                && alike(ir, ll)
                && !alike(il, ll)
        }
        _ => false,
    }
}

/// An equation with its sides swapped; any other term as it is.
pub fn turned(term: &Term) -> Term {
    match &bare(term).kind {
        TermKind::Infix { op, lhs, rhs } => Term {
            kind: TermKind::Infix {
                op: *op,
                lhs: rhs.clone(),
                rhs: lhs.clone(),
            },
            ty: term.ty.clone(),
        },
        _ => term.clone(),
    }
}

/// The term with each count in ℕ∞ of one of the sets, `S.encard`, written
/// as its count in ℕ cast up, `(S.ncard : ℕ∞)`: what rewriting by
/// `Set.Finite.cast_ncard_eq` backwards makes of it.
pub fn with_natural_counts(term: &Term, sets: &[Term]) -> Term {
    let mut out = term.clone();
    if let TermKind::Count {
        set,
        form: CountForm::Extended,
    } = &term.kind
    {
        if sets.iter().any(|s| alike(s, set)) {
            let natural = Term::of(
                TermKind::Count {
                    set: set.clone(),
                    form: CountForm::Natural,
                },
                LeanType::Num(Num::Nat),
            );
            return Term::of(
                TermKind::Cast {
                    inner: Box::new(natural),
                    to: LeanType::ENat,
                },
                LeanType::ENat,
            );
        }
    }
    for child in out.children_mut() {
        *child = with_natural_counts(child, sets);
    }
    out
}

/// The constant that is a library function at another type.
pub type Widen<'a> = dyn Fn(&str, Num) -> Option<super::term::ConstRef> + 'a;

/// The relation with its sides cast up to the type the other's are in,
/// where both are one relation and the other's is wider; None where they
/// are not.
fn lifted(narrow: &Term, other: &Term, widen: &Widen) -> Option<Term> {
    let (
        TermKind::Infix { op: b, lhs, rhs },
        TermKind::Infix {
            op: a,
            lhs: other_lhs,
            ..
        },
    ) = (&bare(narrow).kind, &bare(other).kind)
    else {
        return None;
    };
    let (Some(LeanType::Num(wide)), Some(LeanType::Num(own))) =
        (&other_lhs.ty, &lhs.ty)
    else {
        return None;
    };
    if a != b || own >= wide {
        return None;
    }
    let to = LeanType::Num(*wide);
    Some(Term {
        kind: TermKind::Infix {
            op: *b,
            lhs: Box::new(pushed(&cast_down(lhs, &to, widen), widen)),
            rhs: Box::new(pushed(&cast_down(rhs, &to, widen), widen)),
        },
        ty: narrow.ty.clone(),
    })
}

/// The term with every cast taken down as far as `push_cast` takes it.
fn pushed(term: &Term, widen: &Widen) -> Term {
    let mut out = match &term.kind {
        TermKind::Cast { inner, to } => cast_down(inner, to, widen),
        // A map given by its values applied, `(fun x => t) a`, is t at a,
        // as Lean reads it.
        TermKind::App { head, args, .. } => match (&bare(head).kind, args.as_slice()) {
            (
                TermKind::Quantified {
                    quant: super::term::Quant::Fun,
                    letter,
                    body,
                    ..
                },
                [Arg::Explicit(a)],
            ) => {
                let given =
                    std::collections::BTreeMap::from([(letter.clone(), a.clone())]);
                return pushed(&body.substituted(&given), widen);
            }
            _ => term.clone(),
        },
        // A numeral taken to ℕ is the numeral, `(3 : ℤ).toNat` 3, and a
        // natural number cast to ℤ and taken back is itself.
        TermKind::ToNat(inner) => match &bare(inner).kind {
            TermKind::Numeral(digits) => Term {
                kind: TermKind::Numeral(digits.clone()),
                ty: Some(LeanType::Num(Num::Nat)),
            },
            TermKind::Cast { inner: x, .. }
                if x.ty == Some(LeanType::Num(Num::Nat)) =>
            {
                (**x).clone()
            }
            _ => term.clone(),
        },
        _ => term.clone(),
    };
    for child in out.children_mut() {
        *child = pushed(child, widen);
    }
    out
}

/// `(x : to)` with the cast taken onto x's parts: a numeral is written at
/// `to`; a cast of a cast is one cast; through + · and ^ (onto the base),
/// through − and negation outside ℕ, whose subtraction stops at 0, through
/// / in a field, whose division is exact, and through a library function
/// that has a form at `to`.
fn cast_down(inner: &Term, to: &LeanType, widen: &Widen) -> Term {
    use super::term::Op;
    let at = |kind: TermKind| Term {
        kind,
        ty: Some(to.clone()),
    };
    let cast = |x: &Term| match x.ty.as_ref() == Some(to) {
        true => x.clone(),
        false => at(TermKind::Cast {
            inner: Box::new(x.clone()),
            to: to.clone(),
        }),
    };
    let from = inner.ty.as_ref();
    let natural = matches!(from, Some(LeanType::Num(Num::Nat)));
    let field = matches!(
        from,
        Some(LeanType::Num(Num::Rat | Num::Real | Num::Complex))
    );
    match &inner.kind {
        TermKind::Paren(x) | TermKind::Cast { inner: x, .. } => cast_down(x, to, widen),
        // A sum or product over a Finset, onto its body (`Nat.cast_sum`,
        // `Int.cast_prod`): the last of its terms.
        // An integer power, `x ^ m` with m in ℤ, onto its base
        // (`Rat.cast_zpow`).
        TermKind::Notation { pieces, prec } if matches!(pieces.as_slice(), [Piece::Term { .. }, Piece::Text(t), Piece::Term { .. }] if t == " ^ ") =>
        {
            let mut pieces = pieces.clone();
            if let Some(Piece::Term { term, .. }) = pieces.first_mut() {
                **term = cast(term);
            }
            at(TermKind::Notation {
                pieces,
                prec: *prec,
            })
        }
        TermKind::Notation { pieces, prec } if over_finset(pieces) => {
            let mut pieces = pieces.clone();
            if let Some(Piece::Term { term, .. }) = pieces.last_mut() {
                **term = cast(term);
            }
            at(TermKind::Notation {
                pieces,
                prec: *prec,
            })
        }
        TermKind::App {
            head,
            args,
            explicit,
        } => {
            // `abs` is one function at every ordered type, ↑|a| = |↑a|
            // (`Int.cast_abs`, `Rat.cast_abs`).
            let wider = match (&head.kind, to) {
                (TermKind::Const(c), LeanType::Num(_)) if c.name == "abs" => {
                    Some(c.clone())
                }
                (TermKind::Const(c), LeanType::Num(n)) => widen(&c.name, *n),
                _ => None,
            };
            match wider {
                Some(c) => at(TermKind::App {
                    head: Box::new(Term {
                        kind: TermKind::Const(c),
                        ty: head.ty.clone(),
                    }),
                    args: args
                        .iter()
                        .map(|a| match a {
                            Arg::Explicit(t) => Arg::Explicit(cast(t)),
                            named => named.clone(),
                        })
                        .collect(),
                    explicit: *explicit,
                }),
                None => cast(inner),
            }
        }
        TermKind::Numeral(digits) => at(TermKind::Numeral(digits.clone())),
        TermKind::Infix { op, lhs, rhs }
            if *op == Op::PLUS
                || *op == Op::TIMES
                || (*op == Op::MINUS && !natural)
                || (*op == Op::DIVIDE && field) =>
        {
            at(TermKind::Infix {
                op: *op,
                lhs: Box::new(cast(lhs)),
                rhs: Box::new(cast(rhs)),
            })
        }
        // A real power, x ^ y of a real y, which the writer writes only of
        // an x the lines show at least 0, onto both (`Complex.ofReal_cpow`);
        // any other power onto its base.
        TermKind::Infix { op, lhs, rhs } if *op == Op::POWER => {
            let real_exponent = rhs.ty == Some(LeanType::Num(Num::Real));
            at(TermKind::Infix {
                op: *op,
                lhs: Box::new(cast(lhs)),
                rhs: Box::new(match real_exponent {
                    true => cast(rhs),
                    false => (**rhs).clone(),
                }),
            })
        }
        TermKind::Neg(x) if !natural => at(TermKind::Neg(Box::new(cast(x)))),
        _ => cast(inner),
    }
}

/// Whether a notation is a sum or product over a Finset, `∑ k ∈ s, t`,
/// which a cast passes into; `∑ᶠ` over a set is not.
fn over_finset(pieces: &[Piece]) -> bool {
    matches!(pieces.first(), Some(Piece::Text(t)) if t.starts_with("∑ ") || t.starts_with("∏ "))
}

/// The term with brackets no precedence asks for taken off, and a type
/// given a term that has it already, `(2 : ℤ)` of an integer 2, which is
/// that term at its own type and no cast.
/// How a statement Lean has, what a tactic gives a hypothesis or a line
/// proves, stands to the statement a line writes for it, where the two
/// differ at most in a way one term moves between.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Meets {
    /// Written alike.
    Same,
    /// Alike once each is read as Lean reads it: `a ≠ b` as `¬ a = b`,
    /// `x ∉ A` as `¬ x ∈ A`, `a ≥ b` as `b ≤ a` and `a > b` as `b < a`, and
    /// each letter a `set` names as its value. Lean takes the two as one
    /// statement, and the one stands for the other as it is.
    Unfolded,
    /// The one's equation or congruence turned round, or its negation's:
    /// `.symm` of it, or `Ne.symm` where `negated`.
    Turned { negated: bool },
    /// Alike once the identity elements are dropped, `x + 0` as `x`, by the
    /// rewrites named: `simpa only [..] using` it.
    Identities(Vec<&'static str>),
    /// Alike once casts are pushed down onto the parts they cast, as
    /// `push_cast` takes them, the letters whose `set` equations `through`
    /// names put as their values first, which `push_cast` does not look
    /// through. `lift` where the two state their relation in different
    /// types, a line in ℤ for a statement in ℚ, which `exact_mod_cast`
    /// takes up.
    Casts { through: Vec<String>, lift: bool },
}

/// The type a statement's relation is stated in, `ℚ` of `(a : ℚ) ≤ b`, its
/// negation's included; None for a statement of another shape, or one whose
/// sides carry no type.
fn relation_type(term: &Term) -> Option<LeanType> {
    match &term.kind {
        TermKind::Paren(inner) | TermKind::Not(inner) => relation_type(inner),
        TermKind::Infix { op, lhs, rhs }
            if matches!(op.symbol, "=" | "≠" | "<" | ">" | "≤" | "≥" | "∣") =>
        {
            lhs.ty.clone().or_else(|| rhs.ty.clone())
        }
        // A membership or a subset is stated of the type of its member or
        // of its sets.
        TermKind::Infix { op, lhs, .. }
            if matches!(op.symbol, "∈" | "∉" | "⊆" | "⊂") =>
        {
            lhs.ty.clone()
        }
        _ => None,
    }
}

/// Whether the two state their relation in one type as far as their trees
/// say: both in the same type, or neither giving one. A statement whose
/// type is known on one side alone, as an item's printed with its letters'
/// types left to Lean, is not known to be in the other's.
pub fn relation_types_agree(a: &Term, b: &Term) -> bool {
    match (relation_type(a), relation_type(b)) {
        (Some(x), Some(y)) => x == y,
        (None, None) => true,
        _ => false,
    }
}

/// How `given` stands to `line` (`Meets`), each letter of `values` read as
/// its value; None where they differ in more.
pub fn meets(given: &Term, line: &Term, values: &Values) -> Option<Meets> {
    let (given_written, line_written) = (given, line);
    let lift = match (relation_type(given), relation_type(line)) {
        (Some(a), Some(b)) => a != b,
        _ => false,
    };
    if lift {
        // A fact of numerals alone in another type, (1 : ℚ)/4 > 0 for one in
        // ℝ, is worked out where it is asked: `norm_cast` does not take
        // every such fact across, ℚ's order to ℝ's among them.
        let lettered = |t: &Term| {
            t.walk()
                .iter()
                .any(|n| matches!(n.kind, TermKind::Letter(_)))
        };
        if !lettered(given_written) && !lettered(line_written) {
            return None;
        }
        return casts_alike(given_written, line_written, values, true);
    }
    let (given, line) = (given.untyped(), line.untyped());
    if given == line
        || ascriptions_dropped(given_written) == ascriptions_dropped(line_written)
    {
        return Some(Meets::Same);
    }
    let read = |t: &Term| {
        let unfolded = unfolded(&reduced(&with_values(t, values, 8)));
        renamed_bound(&unfolded, &mut 0).untyped()
    };
    let (given, line) = (read(given_written), read(line_written));
    if given == line {
        return Some(Meets::Unfolded);
    }
    match (&given.kind, &line.kind) {
        (TermKind::Not(a), TermKind::Not(b)) if turned_pair(a, b) => {
            return Some(Meets::Turned { negated: true })
        }
        _ if turned_pair(&given, &line) => {
            return Some(Meets::Turned { negated: false })
        }
        _ => {}
    }
    let mut used = std::collections::BTreeSet::new();
    let (dropped_given, dropped_line) = (
        identities_dropped(&given, &mut used),
        identities_dropped(&line, &mut used),
    );
    if dropped_given == dropped_line {
        return Some(Meets::Identities(used.into_iter().collect()));
    }
    casts_alike(given_written, line_written, values, false)
}

/// `Meets::Casts` where the two are alike once their casts are pushed
/// down, as written or with the letters of `values` put as their values;
/// None where they are not.
fn casts_alike(
    given: &Term,
    line: &Term,
    values: &Values,
    lift: bool,
) -> Option<Meets> {
    let none = |_: &str, _: Num| None;
    let cast = |t: &Term| {
        let pushed = pushed(&unfolded(&reduced(t)), &none);
        renamed_bound(&pushed, &mut 0).untyped()
    };
    if cast(given) == cast(line) {
        return Some(Meets::Casts {
            through: Vec::new(),
            lift,
        });
    }
    let valued = |t: &Term| cast(&with_values(t, values, 8));
    if valued(given) != valued(line) {
        return None;
    }
    let named: std::collections::BTreeSet<&str> = [given, line]
        .iter()
        .flat_map(|t| t.walk())
        .filter_map(|t| match &t.kind {
            TermKind::Letter(l) => Some(l.as_str()),
            _ => None,
        })
        .collect();
    let through = values
        .iter()
        .filter(|(name, _)| named.contains(name.as_str()))
        .map(|(_, v)| v.equation.clone())
        .collect();
    Some(Meets::Casts { through, lift })
}

/// The term with each function written by its rule applied, `(fun k => b) t`,
/// as its body at `t`, and each application of an application taken as
/// one, `(f a) b` as `f a b`: as Lean reduces both.
fn reduced(term: &Term) -> Term {
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = reduced(c);
    }
    let TermKind::App {
        head,
        args,
        explicit,
    } = &out.kind
    else {
        return out;
    };
    let mut head = (**head).clone();
    while let TermKind::Paren(inner) = head.kind {
        head = *inner;
    }
    match head.kind {
        TermKind::App {
            head: inner,
            args: first,
            ..
        } => {
            let mut all = first;
            all.extend(args.iter().cloned());
            reduced(&Term {
                kind: TermKind::App {
                    head: inner,
                    args: all,
                    explicit: *explicit,
                },
                ty: out.ty.clone(),
            })
        }
        TermKind::Quantified {
            quant: super::term::Quant::Fun,
            letter,
            body,
            ..
        } => {
            let Some(Arg::Explicit(value)) = args.first() else {
                return out;
            };
            let applied = substituted(&body, &letter, value);
            match args.len() {
                1 => applied,
                _ => reduced(&Term {
                    kind: TermKind::App {
                        head: Box::new(applied),
                        args: args[1..].to_vec(),
                        explicit: *explicit,
                    },
                    ty: out.ty.clone(),
                }),
            }
        }
        _ => out,
    }
}

/// The term with each letter a binder binds renamed in the order the
/// binders stand, `∑ j ∈ s, f j` and `∑ k ∈ s, f k` alike: a quantifier's
/// letter, and the letter a notation binds after its mark, `∑`, `∏`, `∫`,
/// `∀`, `∃` or a set-builder's `{`.
fn renamed_bound(term: &Term, next: &mut usize) -> Term {
    let fresh = |next: &mut usize| {
        *next += 1;
        format!("·{next}")
    };
    match &term.kind {
        TermKind::Quantified {
            quant,
            letter,
            letter_ty,
            guard,
            body,
        } => {
            let new = fresh(next);
            let as_new = Term {
                kind: TermKind::Letter(new.clone()),
                ty: None,
            };
            let guard = guard.as_ref().map(|g| {
                Box::new(renamed_bound(&substituted(g, letter, &as_new), next))
            });
            let body =
                Box::new(renamed_bound(&substituted(body, letter, &as_new), next));
            Term {
                kind: TermKind::Quantified {
                    quant: *quant,
                    letter: new,
                    letter_ty: letter_ty.clone(),
                    guard,
                    body,
                },
                ty: term.ty.clone(),
            }
        }
        TermKind::Notation { pieces, prec } => {
            let bound = match pieces.first() {
                Some(Piece::Text(t)) => notation_binder(t),
                _ => None,
            };
            let Some(letter) = bound else {
                let mut out = term.clone();
                for c in out.children_mut() {
                    *c = renamed_bound(c, next);
                }
                return out;
            };
            let new = fresh(next);
            let as_new = Term {
                kind: TermKind::Letter(new.clone()),
                ty: None,
            };
            // The letter is bound in what follows the text that opens the
            // body, `, ` of a sum or `|` of a set-builder: the range before
            // it, `Finset.Icc 1 (k + 1)`, is outside its scope.
            let mut in_scope = false;
            let mut out = Vec::new();
            for (i, p) in pieces.iter().enumerate() {
                out.push(match p {
                    Piece::Text(t) => {
                        in_scope = in_scope || t.contains(',') || t.contains('|');
                        match i {
                            0 => Piece::Text(t.replacen(&letter, &new, 1)),
                            _ => Piece::Text(t.clone()),
                        }
                    }
                    Piece::Term { term, need } => {
                        let term = match in_scope {
                            true => substituted(term, &letter, &as_new),
                            false => (**term).clone(),
                        };
                        Piece::Term {
                            term: Box::new(renamed_bound(&term, next)),
                            need: *need,
                        }
                    }
                });
            }
            let pieces = out;
            Term {
                kind: TermKind::Notation {
                    pieces,
                    prec: *prec,
                },
                ty: term.ty.clone(),
            }
        }
        _ => {
            let mut out = term.clone();
            for c in out.children_mut() {
                *c = renamed_bound(c, next);
            }
            out
        }
    }
}

/// The letter a notation binds where its text opens with a binder's mark
/// and the letter, `∑ j ∈ `, `∫ t in `, `{n : ℤ | `; None for another.
fn notation_binder(text: &str) -> Option<String> {
    let text = text.trim_start();
    let rest = match text.strip_prefix('{') {
        Some(rest) => rest,
        None => {
            let (mark, rest) = text.split_once(' ')?;
            if !matches!(mark, "∑" | "∏" | "∑ᶠ" | "∏ᶠ" | "∫" | "∀" | "∃" | "∃!")
            {
                return None;
            }
            rest
        }
    };
    let letter: String = rest
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_' || *c == '\'')
        .collect();
    let after = rest[letter.len()..].trim_start();
    let binds =
        after.starts_with('∈') || after.starts_with(':') || after.starts_with("in ");
    (!letter.is_empty() && binds).then_some(letter)
}

/// The term untyped, with no bracket the writer kept and no ascription of
/// a term to its own type, `(2 : ℝ)` of a real 2: what Lean reads alike.
fn ascriptions_dropped(term: &Term) -> Term {
    match &term.kind {
        TermKind::Paren(inner) => return ascriptions_dropped(inner),
        TermKind::Cast { inner, to } if inner.ty.as_ref() == Some(to) => {
            return ascriptions_dropped(inner)
        }
        _ => {}
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = ascriptions_dropped(c);
    }
    out.untyped()
}

/// A letter a proof names by `set`: its value, and the name of the
/// equation `set … with` gives.
#[derive(Clone, Debug)]
pub struct Value {
    pub value: Term,
    pub equation: String,
}

/// The letters a proof names by `set`, by their Lean names.
pub type Values = indexmap::IndexMap<String, Value>;

/// The term with each letter of `values` put as its value, to `depth`
/// levels of values naming other letters.
fn with_values(term: &Term, values: &Values, depth: usize) -> Term {
    if let TermKind::Letter(name) = &term.kind {
        if let (Some(v), true) = (values.get(name), depth > 0) {
            return with_values(&v.value, values, depth - 1);
        }
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = with_values(c, values, depth);
    }
    out
}

/// The term with each identity element dropped where Lean's rewrite of that
/// name drops it, `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x`, `x ^ 1`, and
/// each numeral taken to ℕ as the numeral, the rewrites used put in `used`.
/// What `simp only` must be told to work out the numerals the writer takes
/// to ℕ in `term`, `(0 + 1).toNat`: `Int.reduceToNat` and each operation's
/// own procedure, which it uses only where named.
pub fn to_nat_rules(term: &Term) -> std::collections::BTreeSet<&'static str> {
    let mut used = std::collections::BTreeSet::new();
    for t in term.walk() {
        let TermKind::ToNat(inner) = &t.kind else {
            continue;
        };
        let closed = !inner
            .walk()
            .iter()
            .any(|n| matches!(n.kind, TermKind::Letter(_) | TermKind::Const(_)));
        if !closed {
            continue;
        }
        used.insert("Int.reduceToNat");
        for n in inner.walk() {
            if let TermKind::Infix { op, .. } = &n.kind {
                used.extend(arithmetic_rules(op.symbol).iter().copied());
            }
        }
    }
    used
}

/// The procedures `simp only` works an operation on numerals out by, in ℤ
/// and in ℕ.
fn arithmetic_rules(symbol: &str) -> &'static [&'static str] {
    match symbol {
        "+" => &["Int.reduceAdd", "Nat.reduceAdd"],
        "-" => &["Int.reduceSub", "Nat.reduceSub"],
        "*" => &["Int.reduceMul", "Nat.reduceMul"],
        "^" => &["Int.reducePow", "Nat.reducePow"],
        _ => &[],
    }
}

/// Where the two differ only in how the writer placed their casts: the
/// `set` equations to rewrite by first, and whether the one is in a
/// narrower type than the other. None where they are written alike, or
/// differ in more than casts.
pub fn casts_differ(given: &Term, line: &Term, values: &Values) -> Option<CastsApart> {
    if ascriptions_dropped(given) == ascriptions_dropped(line) {
        return None;
    }
    // Alike once each letter a `set` names is read as its value, bound
    // letters renamed: Lean takes the one for the other as it is.
    let valued = |t: &Term| {
        renamed_bound(&unfolded(&reduced(&with_values(t, values, 8))), &mut 0).untyped()
    };
    if valued(given) == valued(line) {
        return None;
    }
    let lift = match (relation_type(given), relation_type(line)) {
        (Some(a), Some(b)) => a != b,
        _ => false,
    };
    let Meets::Casts { through, lift } = casts_alike(given, line, values, lift)? else {
        return None;
    };
    let named_in = |t: &Term| -> Vec<String> {
        let names: std::collections::BTreeSet<String> = t
            .walk()
            .into_iter()
            .filter_map(|n| match &n.kind {
                TermKind::Letter(l) => Some(l.clone()),
                _ => None,
            })
            .collect();
        values
            .iter()
            .filter(|(name, v)| names.contains(*name) && through.contains(&v.equation))
            .map(|(_, v)| v.equation.clone())
            .collect()
    };
    Some(CastsApart {
        at_given: named_in(given),
        at_line: named_in(line),
        lift,
    })
}

/// How two statements that differ only in casts are taken the one to the
/// other (`casts_differ`): the `set` equations to rewrite the first by and
/// the second by, each where one of its letters stands, and whether the
/// first is in a narrower type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CastsApart {
    pub at_given: Vec<String>,
    pub at_line: Vec<String>,
    pub lift: bool,
}

/// A statement turned round: an equation's sides swapped, a congruence's,
/// or those of the equation a negation denies.
pub fn turned_statement(term: &Term) -> Term {
    match &term.kind {
        TermKind::Paren(inner) => turned_statement(inner),
        TermKind::Not(inner) => negation(&turned_statement(inner)),
        TermKind::ModEq { a, b, n } => Term {
            kind: TermKind::ModEq {
                a: b.clone(),
                b: a.clone(),
                n: n.clone(),
            },
            ty: term.ty.clone(),
        },
        _ => turned(term),
    }
}

/// Whether Lean writes the two alike once each letter a `set` names is read
/// as its value, applied where it is a function, and bound letters renamed.
pub fn alike_once_set(a: &Term, b: &Term, values: &Values) -> bool {
    let valued = |t: &Term| {
        renamed_bound(&unfolded(&reduced(&with_values(t, values, 8))), &mut 0).untyped()
    };
    valued(a) == valued(b)
}

/// Whether Lean casts a letter a `set` names, or a term with one in it, to
/// another type somewhere in `term`, `(S 1 : ℚ)`.
pub fn casts_set_letter(term: &Term, values: &Values) -> bool {
    term.walk().iter().any(|t| match &t.kind {
        TermKind::Cast { inner, to } if inner.ty.as_ref() != Some(to) => inner
            .walk()
            .iter()
            .any(|n| matches!(&n.kind, TermKind::Letter(l) if values.contains_key(l))),
        _ => false,
    })
}

/// Whether Lean writes the two alike, an ascription of a term to its own
/// type and the writer's brackets aside.
pub fn written_alike(a: &Term, b: &Term) -> bool {
    ascriptions_dropped(a) == ascriptions_dropped(b)
}

/// Whether the statement denies an equation, `a ≠ b` or `¬ a = b`: one
/// turned round by `Ne.symm`.
pub fn denies_equation(term: &Term) -> bool {
    matches!(&unfolded(term).kind, TermKind::Not(inner)
        if matches!(&inner.kind, TermKind::Infix { op, .. } if op.symbol == "="))
}

fn identities_dropped(
    term: &Term,
    used: &mut std::collections::BTreeSet<&'static str>,
) -> Term {
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = identities_dropped(c, used);
    }
    let numeral =
        |t: &Term, n: &str| matches!(&bare(t).kind, TermKind::Numeral(x) if x == n);
    // Numerals taken to ℕ, `(2 * 0).toNat`, are what they work out to in ℕ,
    // as simp's arithmetic on numerals works them out.
    if let TermKind::ToNat(inner) = &out.kind {
        let closed = !inner
            .walk()
            .iter()
            .any(|t| matches!(t.kind, TermKind::Letter(_) | TermKind::Const(_)));
        if closed {
            // `simp only` works the arithmetic out only by the procedures
            // named: each operation's, in ℤ under the `toNat` and in ℕ where
            // the other side writes it so.
            used.insert("Int.reduceToNat");
            for t in inner.walk() {
                if let TermKind::Infix { op, .. } = &t.kind {
                    used.extend(arithmetic_rules(op.symbol).iter().copied());
                }
            }
            return (**inner).clone();
        }
    }
    if let TermKind::Infix { op, lhs, rhs } = &out.kind {
        let kept = match op.symbol {
            "+" if numeral(rhs, "0") => Some((lhs, "add_zero")),
            "+" if numeral(lhs, "0") => Some((rhs, "zero_add")),
            "-" if numeral(rhs, "0") => Some((lhs, "sub_zero")),
            "*" if numeral(rhs, "1") => Some((lhs, "mul_one")),
            "*" if numeral(lhs, "1") => Some((rhs, "one_mul")),
            "^" if numeral(rhs, "1") => Some((lhs, "pow_one")),
            _ => None,
        };
        if let Some((kept, rule)) = kept {
            used.insert(rule);
            return (**kept).clone();
        }
    }
    if let TermKind::Paren(inner) = &out.kind {
        return (**inner).clone();
    }
    out
}

/// The term with `value` put for the letter `letter` wherever it is free,
/// as Lean puts an induction's value into its motive: a cast of the letter
/// stays a cast of the value, `↑(k + 1)`.
pub fn substituted(term: &Term, letter: &str, value: &Term) -> Term {
    match &term.kind {
        TermKind::Letter(l) if l == letter => return value.clone(),
        TermKind::Quantified { letter: bound, .. } if bound == letter => {
            return term.clone()
        }
        _ => {}
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = substituted(c, letter, value);
    }
    out
}

/// The term with each letter of `values` put as its value at once, as Lean
/// puts a citation's arguments into the cited statement: a value is not
/// itself put into again.
pub fn substituted_all(
    term: &Term,
    values: &std::collections::BTreeMap<String, Term>,
) -> Term {
    match &term.kind {
        TermKind::Letter(l) => {
            if let Some(v) = values.get(l) {
                return v.clone();
            }
        }
        TermKind::Quantified { letter, .. } if values.contains_key(letter) => {
            let mut inner = values.clone();
            inner.remove(letter);
            let mut out = term.clone();
            for c in out.children_mut() {
                *c = substituted_all(c, &inner);
            }
            return out;
        }
        _ => {}
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = substituted_all(c, values);
    }
    out
}

/// `¬ p`.
pub fn negation(term: &Term) -> Term {
    Term {
        kind: TermKind::Not(Box::new(term.clone())),
        ty: Some(LeanType::Prop),
    }
}

/// What a negation denies: `p` of `¬ p`, `a = b` of `a ≠ b`, `x ∈ A` of
/// `x ∉ A`; None for a statement that is no negation.
pub fn denied(term: &Term) -> Option<Term> {
    match &unfolded(term).kind {
        TermKind::Not(inner) => Some((**inner).clone()),
        _ => None,
    }
}

/// The term with no bracket the writer kept, each `a ≠ b` written
/// `¬ a = b`, each `x ∉ A` written `¬ x ∈ A`, and each `a ≥ b` and `a > b`
/// written `b ≤ a` and `b < a`, as Lean's notations unfold.
fn unfolded(term: &Term) -> Term {
    use super::term::Op;
    match &term.kind {
        TermKind::Paren(inner) => return unfolded(inner),
        // `(t : T)` of a t already in T says only what t is.
        TermKind::Cast { inner, to } if inner.ty.as_ref() == Some(to) => {
            return unfolded(inner)
        }
        _ => {}
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = unfolded(c);
    }
    if let TermKind::Infix { op, lhs, rhs } = &out.kind {
        let flipped = match op.symbol {
            "≥" => Some(Op::AT_MOST),
            ">" => Op::of("<"),
            _ => None,
        };
        if let Some(op) = flipped {
            return Term {
                kind: TermKind::Infix {
                    op,
                    lhs: rhs.clone(),
                    rhs: lhs.clone(),
                },
                ty: out.ty.clone(),
            };
        }
    }
    let positive = match &out.kind {
        TermKind::Infix { op, .. } if op.symbol == "≠" => Op::EQUALS,
        TermKind::Infix { op, .. } if op.symbol == "∉" => match Op::of("∈") {
            Some(member) => member,
            None => return out,
        },
        _ => return out,
    };
    let TermKind::Infix { lhs, rhs, .. } = out.kind else {
        return out;
    };
    negation(&Term {
        kind: TermKind::Infix {
            op: positive,
            lhs,
            rhs,
        },
        ty: Some(LeanType::Prop),
    })
}

/// Whether `b` is the equation or the congruence `a` with its sides
/// swapped, and not the same one.
fn turned_pair(a: &Term, b: &Term) -> bool {
    use super::term::Op;
    match (&a.kind, &b.kind) {
        (
            TermKind::ModEq {
                a: al,
                b: ar,
                n: an,
            },
            TermKind::ModEq {
                a: bl,
                b: br,
                n: bn,
            },
        ) => an == bn && al == br && ar == bl && al != bl,
        (
            TermKind::Infix {
                op: x,
                lhs: al,
                rhs: ar,
            },
            TermKind::Infix {
                op: y,
                lhs: bl,
                rhs: br,
            },
        ) => *x == Op::EQUALS && x == y && al == br && ar == bl && al != bl,
        _ => false,
    }
}

fn bare(term: &Term) -> &Term {
    match &term.kind {
        TermKind::Paren(inner) => bare(inner),
        TermKind::Cast { inner, to } if inner.ty.as_ref() == Some(to) => bare(inner),
        _ => term,
    }
}

/// Whether a natural number is the integer `x` taken to ℕ, written as it
/// stands: `natural` cast to ℤ, with the cast pushed down, is `x` in one
/// form.
fn is_to_nat_of(x: &Term, natural: &Term) -> bool {
    if natural.ty != Some(LeanType::Num(Num::Nat)) {
        return false;
    }
    let none = |_: &str, _: Num| None;
    let up = pushed(&cast_down(natural, &LeanType::Num(Num::Int), &none), &none);
    let mut parts = Vec::new();
    compare(&pushed(x, &none), &up, &mut parts);
    parts.is_empty() && alike(x, &up)
}

fn compare(item: &Term, line: &Term, out: &mut Vec<FormDifference>) {
    let (item, line) = (bare(item), bare(line));
    match (&item.kind, &line.kind) {
        (TermKind::Count { set: a, form: f }, TermKind::Count { set: b, form: g }) => {
            if f != g {
                out.push(FormDifference::Count {
                    item: *f,
                    line: *g,
                    item_set: (**a).clone(),
                    line_set: (**b).clone(),
                });
            }
            compare(a, b, out);
        }
        (TermKind::ToNat(a), TermKind::ToNat(b)) => compare(a, b, out),
        // A cast or `toNat` on one side only is a form where taking it off
        // leaves one term on both; where it leaves two, the item says
        // something else there, which is no question of form.
        (TermKind::ToNat(a) | TermKind::Cast { inner: a, .. }, _)
            if !alike(a, line) => {}
        (_, TermKind::ToNat(b) | TermKind::Cast { inner: b, .. })
            if !alike(item, b) => {}
        // x.toNat beside a natural number y that cast to ℤ is x, as
        // `push_cast` writes it: ((2 : ℤ) ^ n).toNat beside 2 ^ n.
        (TermKind::ToNat(a), _) if is_to_nat_of(a, line) => {}
        (_, TermKind::ToNat(b)) if is_to_nat_of(b, item) => {}
        (TermKind::ToNat(a), _) => {
            out.push(FormDifference::ToNat { in_item: true });
            compare(a, line, out);
        }
        (_, TermKind::ToNat(b)) => {
            out.push(FormDifference::ToNat { in_item: false });
            compare(item, b, out);
        }
        (TermKind::Cast { inner: a, to: s }, TermKind::Cast { inner: b, to: t }) => {
            if s != t {
                out.push(FormDifference::Cast {
                    item: Some(s.clone()),
                    line: Some(t.clone()),
                });
            }
            compare(a, b, out);
        }
        (TermKind::Cast { inner: a, to }, _) => {
            out.push(FormDifference::Cast {
                item: Some(to.clone()),
                line: None,
            });
            compare(a, line, out);
        }
        (_, TermKind::Cast { inner: b, to }) => {
            out.push(FormDifference::Cast {
                item: None,
                line: Some(to.clone()),
            });
            compare(item, b, out);
        }
        _ => {
            if std::mem::discriminant(&item.kind) != std::mem::discriminant(&line.kind)
            {
                return;
            }
            let (a, b) = (children(item), children(line));
            if a.len() == b.len() {
                for (x, y) in a.into_iter().zip(b) {
                    compare(x, y, out);
                }
            }
        }
    }
}

/// Whether two terms are one term but for their forms: alike once every
/// cast, `toNat` and spare bracket is taken off, with a count alike in
/// either form.
pub fn alike(a: &Term, b: &Term) -> bool {
    let strip = |t: &Term| -> Term {
        let mut t = t.clone();
        while let TermKind::Paren(x)
        | TermKind::Cast { inner: x, .. }
        | TermKind::ToNat(x) = t.kind
        {
            t = *x;
        }
        t
    };
    let (a, b) = (strip(a), strip(b));
    let leaves_agree = match (&a.kind, &b.kind) {
        (TermKind::Letter(x), TermKind::Letter(y)) => x == y,
        (TermKind::Numeral(x), TermKind::Numeral(y)) => x == y,
        (TermKind::Const(x), TermKind::Const(y)) => x == y,
        (TermKind::Infix { op: x, .. }, TermKind::Infix { op: y, .. }) => x == y,
        (TermKind::Count { .. }, TermKind::Count { .. }) => true,
        (x, y) => std::mem::discriminant(x) == std::mem::discriminant(y),
    };
    let (xs, ys) = (children(&a), children(&b));
    leaves_agree
        && xs.len() == ys.len()
        && xs.into_iter().zip(ys).all(|(x, y)| alike(x, y))
}

/// The terms directly inside a node, in order, as both sides are walked.
fn children(term: &Term) -> Vec<&Term> {
    match &term.kind {
        TermKind::App { args, .. } => args
            .iter()
            .map(|a| match a {
                Arg::Explicit(t) => t,
                Arg::Named { value, .. } => value,
            })
            .collect(),
        TermKind::Notation { pieces, .. } => pieces
            .iter()
            .filter_map(|p| match p {
                Piece::Term { term, .. } => Some(&**term),
                Piece::Text(_) => None,
            })
            .collect(),
        _ => term.children(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `(2 : ℤ) ∣ N` and `2 ∣ N`: an ascription to the numeral's own type
    /// says nothing, and the two are written alike.
    #[test]
    fn an_ascription_to_its_own_type_meets_the_bare_term() {
        let int = LeanType::Num(Num::Int);
        let two = Term::of(TermKind::Numeral("2".to_string()), int.clone());
        let n = Term::letter("N", int.clone());
        let divides = super::super::term::Op::of("∣").expect("divides");
        let ascribed = Term::infix(
            divides,
            Term::cast(two.clone(), int.clone()),
            n.clone(),
            LeanType::Prop,
        );
        let bare = Term::infix(divides, two, n, LeanType::Prop);
        assert_eq!(meets(&bare, &ascribed, &Values::new()), Some(Meets::Same));
    }

    fn count(form: CountForm) -> Term {
        let set = Term::letter("d", LeanType::Set(Box::new(LeanType::Num(Num::Int))));
        Term::of(
            TermKind::Count {
                set: Box::new(set),
                form,
            },
            LeanType::ENat,
        )
    }

    #[test]
    fn one_count_in_two_forms_is_reported() {
        let found = differences(
            &count(CountForm::Extended),
            &count(CountForm::Natural),
            &none,
        );
        assert_eq!(
            found,
            [FormDifference::Count {
                item: CountForm::Extended,
                line: CountForm::Natural,
                item_set: Term::letter(
                    "d",
                    LeanType::Set(Box::new(LeanType::Num(Num::Int)))
                ),
                line_set: Term::letter(
                    "d",
                    LeanType::Set(Box::new(LeanType::Num(Num::Int)))
                ),
            }]
        );
    }

    /// No library functions.
    fn none(_: &str, _: Num) -> Option<super::super::term::ConstRef> {
        None
    }

    fn int_letter(name: &str) -> Term {
        Term::letter(name, LeanType::Num(Num::Int))
    }

    fn infix(op: super::super::term::Op, lhs: Term, rhs: Term, ty: Num) -> Term {
        Term::of(
            TermKind::Infix {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            LeanType::Num(ty),
        )
    }

    fn to_rat(x: Term) -> Term {
        Term::of(
            TermKind::Cast {
                inner: Box::new(x),
                to: LeanType::Num(Num::Rat),
            },
            LeanType::Num(Num::Rat),
        )
    }

    #[test]
    fn a_cast_over_a_difference_is_the_difference_of_casts() {
        use super::super::term::Op;
        let whole =
            to_rat(infix(Op::MINUS, int_letter("a"), int_letter("b"), Num::Int));
        let parts = infix(
            Op::MINUS,
            to_rat(int_letter("a")),
            to_rat(int_letter("b")),
            Num::Rat,
        );
        assert!(differences(&whole, &parts, &none).is_empty());
    }

    #[test]
    fn a_cast_over_a_natural_difference_stays() {
        use super::super::term::Op;
        let nat = |n: &str| Term::letter(n, LeanType::Num(Num::Nat));
        let whole = to_rat(infix(Op::MINUS, nat("a"), nat("b"), Num::Nat));
        let parts = infix(Op::MINUS, to_rat(nat("a")), to_rat(nat("b")), Num::Rat);
        assert!(!differences(&whole, &parts, &none).is_empty());
    }

    #[test]
    fn a_term_in_one_form_on_both_sides_is_not() {
        assert!(differences(
            &count(CountForm::Natural),
            &count(CountForm::Natural),
            &none
        )
        .is_empty());
    }
}
