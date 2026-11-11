//! Which operations Lean moves a cast through: the facts the writer's
//! closers rest on where a statement it writes and the goal differ only in
//! where casts stand (`docs/LEAN.md`, how a line proves a statement).
//!
//! Each entry says, of one operation and one pair of number types, whether
//! `push_cast` takes `((a ∘ b : {S}) : {T})` to `(a : {T}) ∘ (b : {T})`, and whether
//! `norm_cast` does, which is what `exact_mod_cast` moves casts by. The two
//! differ: `norm_cast` takes `‖(a : ℂ)‖` to `|a|` and `push_cast` does not.
//! A closer chooses `exact_mod_cast` only where every operation between a
//! cast and the top of the statement is one `norm_cast` moves through.
//!
//! The table is checked by Lean: `parley build lean` writes
//! `lean/Parley/Tests/CastTable.lean` from it (`lean_test`), an `example` for
//! each fact, proved by the tactic where the fact says it moves and by
//! `fail_if_success` where it says it does not, so `lake build` fails when
//! an entry is wrong or a Mathlib upgrade changes one.

use super::doc::Term;
use super::templates::Num;

/// An operation the writer writes, as the cast table knows it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CastOp {
    Add,
    Sub,
    Mul,
    Div,
    Neg,
    /// A power to a natural exponent, `a ^ n`.
    NatPow,
    /// A power to an integer exponent, `a ^ k` in a field.
    IntPow,
    Abs,
    /// The norm of a complex number, `‖z‖`.
    Norm,
    /// A real power, `a ^ b` with a real or complex exponent.
    RealPow,
    Sqrt,
    Exp,
    Log,
    Sin,
    Cos,
    Floor,
    /// An integer taken to ℕ, `n.toNat`, of a natural number cast up:
    /// `((a : ℕ) : ℤ).toNat` is a.
    ToNat,
    Sum,
    Prod,
    /// An equation, `a = b`.
    Eq,
    /// An order, `a < b`.
    Lt,
    /// An order, `a ≤ b`.
    Le,
    /// A quotient of numerals, `1 / 3`, in a statement a line says and a
    /// goal asks with its casts set otherwise: `norm_cast` takes a cast
    /// numeral under it to `NNRat.divNat 1 3`, which the goal's `1 / 3` is
    /// not, and `push_cast` takes the cast to the numeral.
    NumeralQuotient,
}

/// A type the table casts between: a number type, or ℕ∞, where a count of
/// any set is, and a calculation's rows over counts are taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Carrier {
    Num(Num),
    ENat,
}

impl Carrier {
    /// The type, as the writer names Lean's types.
    pub fn lean_type(self) -> super::doc::LeanType {
        match self {
            Carrier::Num(n) => super::doc::LeanType::Num(n),
            Carrier::ENat => super::doc::LeanType::ENat,
        }
    }

    /// The type a term is in, where the table knows it.
    fn of(ty: &super::doc::LeanType) -> Option<Carrier> {
        match ty {
            super::doc::LeanType::Num(n) => Some(Carrier::Num(*n)),
            super::doc::LeanType::ENat => Some(Carrier::ENat),
            _ => None,
        }
    }
}

/// What `push_cast` and `norm_cast` do with a cast from one type to another
/// around one operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CastFacts {
    pub from: Carrier,
    pub to: Carrier,
    pub push_cast: bool,
    pub norm_cast: bool,
}

/// One operation's facts, and the statement each is checked by: `lhs` the
/// operation in `{S}` cast to `{T}`, `rhs` it on the casts, joined by `=`,
/// or by `↔` for a relation, whose cast sides say what it says uncast; over
/// the letters `binders` declares, each with the two types put for `{S}` and
/// `{T}`.
struct OpTable {
    op: CastOp,
    binders: &'static str,
    lhs: &'static str,
    rhs: &'static str,
    facts: &'static [CastFacts],
}

impl OpTable {
    /// What joins the two sides of its check.
    fn joined_by(&self) -> &'static str {
        match self.op {
            CastOp::Eq | CastOp::Lt | CastOp::Le => "↔",
            CastOp::NumeralQuotient => "→",
            _ => "=",
        }
    }

    /// The tactics each fact is checked by. A statement taken from a line
    /// to a goal, `→`, is checked as a closer takes it, the line `h` to the
    /// goal: `norm_cast` on an `↔` or `=` would bring both sides to one form
    /// alike and say nothing of a line against a goal.
    fn tactics(&self) -> (&'static str, &'static str) {
        match self.op {
            CastOp::NumeralQuotient => (
                "intro h; push_cast at h ⊢; exact h",
                "intro h; exact_mod_cast h",
            ),
            _ => ("push_cast; try rfl", "norm_cast"),
        }
    }
}

const fn moves_both(from: Carrier, to: Carrier) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: true,
        norm_cast: true,
    }
}

const fn moves_by_norm_cast(from: Carrier, to: Carrier) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: false,
        norm_cast: true,
    }
}

const fn stops(from: Carrier, to: Carrier) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: false,
        norm_cast: false,
    }
}

const N: Carrier = Carrier::Num(Num::Nat);
const Z: Carrier = Carrier::Num(Num::Int);
const Q: Carrier = Carrier::Num(Num::Rat);
const R: Carrier = Carrier::Num(Num::Real);
const C: Carrier = Carrier::Num(Num::Complex);
/// ℕ∞, where a count of any set is.
const E: Carrier = Carrier::ENat;

/// The lemma that takes a numeral of one type cast up to the numeral in the
/// wider type: `Nat.cast_zero` of `((0 : ℕ) : ℤ)`, `Nat.cast_ofNat` of any
/// other numeral, by the type cast from and the numeral, `n` standing for
/// any but 0 and 1.
pub const NUMERAL_CASTS: &[(Num, &str, &str)] = &[
    (Num::Nat, "n", "Nat.cast_ofNat"),
    (Num::Nat, "0", "Nat.cast_zero"),
    (Num::Nat, "1", "Nat.cast_one"),
    (Num::Int, "n", "Int.cast_ofNat"),
    (Num::Int, "0", "Int.cast_zero"),
    (Num::Int, "1", "Int.cast_one"),
    (Num::Rat, "0", "Rat.cast_zero"),
    (Num::Rat, "1", "Rat.cast_one"),
];

/// Every widening between the number types the writer casts between, and
/// the further ones given after them.
macro_rules! widenings {
    ($($more:expr),*) => {
        &[
            moves_both(N, Z),
            moves_both(N, Q),
            moves_both(N, R),
            moves_both(N, C),
            moves_both(Z, Q),
            moves_both(Z, R),
            moves_both(Z, C),
            moves_both(Q, R),
            moves_both(Q, C),
            moves_both(R, C),
            $($more),*
        ]
    };
}

/// Every widening between the number types the writer casts between.
const WIDENINGS: &[CastFacts] = widenings!();

/// The widenings from a type that has subtraction and negation.
const FROM_RINGS: &[CastFacts] = &[
    moves_both(Z, Q),
    moves_both(Z, R),
    moves_both(Z, C),
    moves_both(Q, R),
    moves_both(Q, C),
    moves_both(R, C),
];

/// The widenings from a field.
const FROM_FIELDS: &[CastFacts] =
    &[moves_both(Q, R), moves_both(Q, C), moves_both(R, C)];

/// The widenings between ordered types, for an order: `push_cast` leaves a
/// cast on each side of it, and `norm_cast` takes the order to the uncast
/// one (`Nat.cast_lt`, `Int.cast_le`, …).
const ORDERED: &[CastFacts] = &[
    moves_by_norm_cast(N, Z),
    moves_by_norm_cast(N, Q),
    moves_by_norm_cast(N, R),
    moves_by_norm_cast(Z, Q),
    moves_by_norm_cast(Z, R),
    moves_by_norm_cast(Q, R),
    moves_by_norm_cast(N, E),
];

/// The widenings a sum is taken through: every one between number types,
/// and a count's from ℕ to ℕ∞, where a calculation adds counts.
const ADDED: &[CastFacts] = widenings!(moves_both(N, E));

const TABLES: &[OpTable] = &[
    OpTable {
        op: CastOp::Add,
        binders: "(a b : {S})",
        lhs: "((a + b : {S}) : {T})",
        rhs: "(a : {T}) + (b : {T})",
        facts: ADDED,
    },
    OpTable {
        op: CastOp::Sub,
        binders: "(a b : {S})",
        lhs: "((a - b : {S}) : {T})",
        rhs: "(a : {T}) - (b : {T})",
        facts: FROM_RINGS,
    },
    OpTable {
        op: CastOp::Mul,
        binders: "(a b : {S})",
        lhs: "((a * b : {S}) : {T})",
        rhs: "(a : {T}) * (b : {T})",
        facts: WIDENINGS,
    },
    OpTable {
        op: CastOp::Div,
        binders: "(a b : {S})",
        lhs: "((a / b : {S}) : {T})",
        rhs: "(a : {T}) / (b : {T})",
        facts: FROM_FIELDS,
    },
    OpTable {
        op: CastOp::Neg,
        binders: "(a : {S})",
        lhs: "((-a : {S}) : {T})",
        rhs: "-(a : {T})",
        facts: FROM_RINGS,
    },
    OpTable {
        op: CastOp::NatPow,
        binders: "(a : {S}) (n : ℕ)",
        lhs: "((a ^ n : {S}) : {T})",
        rhs: "(a : {T}) ^ n",
        facts: WIDENINGS,
    },
    OpTable {
        op: CastOp::IntPow,
        binders: "(a : {S}) (k : ℤ)",
        lhs: "((a ^ k : {S}) : {T})",
        rhs: "(a : {T}) ^ k",
        facts: FROM_FIELDS,
    },
    OpTable {
        op: CastOp::Abs,
        binders: "(a : {S})",
        lhs: "((|a| : {S}) : {T})",
        rhs: "|(a : {T})|",
        facts: &[moves_both(Z, Q), moves_both(Z, R), moves_both(Q, R)],
    },
    OpTable {
        op: CastOp::Norm,
        binders: "(a : {S})",
        lhs: "((|a| : {S}) : ℝ)",
        rhs: "‖(a : {T})‖",
        facts: &[moves_by_norm_cast(R, C)],
    },
    OpTable {
        op: CastOp::RealPow,
        binders: "(a b : {S})",
        lhs: "((a ^ b : {S}) : {T})",
        rhs: "(a : {T}) ^ (b : {T})",
        facts: &[stops(R, C)],
    },
    OpTable {
        op: CastOp::Sqrt,
        binders: "(a : {S})",
        lhs: "((Real.sqrt a : {S}) : {T})",
        rhs: "(a : {T}) ^ ((1 : {T}) / 2)",
        facts: &[stops(R, C)],
    },
    OpTable {
        op: CastOp::Exp,
        binders: "(a : {S})",
        lhs: "((Real.exp a : {S}) : {T})",
        rhs: "Complex.exp (a : {T})",
        facts: &[moves_both(R, C)],
    },
    OpTable {
        op: CastOp::Log,
        binders: "(a : {S})",
        lhs: "((Real.log a : {S}) : {T})",
        rhs: "Complex.log (a : {T})",
        facts: &[stops(R, C)],
    },
    OpTable {
        op: CastOp::Sin,
        binders: "(a : {S})",
        lhs: "((Real.sin a : {S}) : {T})",
        rhs: "Complex.sin (a : {T})",
        facts: &[moves_both(R, C)],
    },
    OpTable {
        op: CastOp::Cos,
        binders: "(a : {S})",
        lhs: "((Real.cos a : {S}) : {T})",
        rhs: "Complex.cos (a : {T})",
        facts: &[moves_both(R, C)],
    },
    OpTable {
        op: CastOp::Floor,
        binders: "(a : {S})",
        lhs: "(⌊a⌋ : ℤ)",
        rhs: "⌊(a : {T})⌋",
        facts: &[moves_by_norm_cast(Q, R)],
    },
    OpTable {
        op: CastOp::ToNat,
        binders: "(a : {S})",
        lhs: "((a : {S}) : {T}).toNat",
        rhs: "a",
        facts: &[moves_both(N, Z)],
    },
    OpTable {
        op: CastOp::Sum,
        binders: "(s : Finset ℕ) (f : ℕ → {S})",
        lhs: "((∑ i ∈ s, f i : {S}) : {T})",
        rhs: "∑ i ∈ s, (f i : {T})",
        facts: WIDENINGS,
    },
    OpTable {
        op: CastOp::NumeralQuotient,
        binders: "(x : {S})",
        lhs: "((1 : {S}) : {T}) / 3 ≤ (x : {T})",
        rhs: "(1 : {T}) / 3 ≤ (x : {T})",
        facts: &[
            CastFacts {
                from: Z,
                to: Q,
                push_cast: true,
                norm_cast: false,
            },
            CastFacts {
                from: Z,
                to: R,
                push_cast: true,
                norm_cast: false,
            },
            CastFacts {
                from: Q,
                to: R,
                push_cast: true,
                norm_cast: false,
            },
        ],
    },
    OpTable {
        op: CastOp::Eq,
        binders: "(a b : {S})",
        lhs: "((a : {S}) : {T}) = ((b : {S}) : {T})",
        rhs: "a = b",
        facts: &[
            moves_by_norm_cast(N, Z),
            moves_by_norm_cast(N, Q),
            moves_by_norm_cast(N, R),
            moves_by_norm_cast(N, C),
            moves_by_norm_cast(Z, Q),
            moves_by_norm_cast(Z, R),
            moves_by_norm_cast(Z, C),
            moves_by_norm_cast(Q, R),
            moves_by_norm_cast(Q, C),
            moves_by_norm_cast(R, C),
            moves_by_norm_cast(N, E),
        ],
    },
    OpTable {
        op: CastOp::Lt,
        binders: "(a b : {S})",
        lhs: "((a : {S}) : {T}) < ((b : {S}) : {T})",
        rhs: "a < b",
        facts: ORDERED,
    },
    OpTable {
        op: CastOp::Le,
        binders: "(a b : {S})",
        lhs: "((a : {S}) : {T}) ≤ ((b : {S}) : {T})",
        rhs: "a ≤ b",
        facts: ORDERED,
    },
    OpTable {
        op: CastOp::Prod,
        binders: "(s : Finset ℕ) (f : ℕ → {S})",
        lhs: "((∏ i ∈ s, f i : {S}) : {T})",
        rhs: "∏ i ∈ s, (f i : {T})",
        facts: WIDENINGS,
    },
];

/// What `push_cast` and `norm_cast` do with a cast from `from` to `to`
/// around `op`; None where the table has no entry, which a closer takes as
/// moving by neither.
pub fn facts(op: CastOp, from: Carrier, to: Carrier) -> Option<CastFacts> {
    TABLES
        .iter()
        .filter(|t| t.op == op)
        .flat_map(|t| t.facts)
        .find(|f| f.from == from && f.to == to)
        .copied()
}

/// The Lean file that checks every entry: for each operation and pair, its
/// equation proved by each tactic the entry says moves the cast, and the
/// tactic shown to fail where it says it does not.
pub fn lean_test(module: &str) -> String {
    let mut out = String::from(
        "module\n\npublic import Mathlib\n\n/-! Written from the cast table (`src/lean/casts.rs`) by parley build lean. -/\n\npublic section\n\nset_option linter.unusedTactic false\n\n",
    );
    out.push_str(&format!("namespace {module}\n\n"));
    for table in TABLES {
        for f in table.facts {
            let (s, t) = (f.from.lean_type().text(), f.to.lean_type().text());
            let put = |text: &str| text.replace("{S}", &s).replace("{T}", &t);
            let equation = format!(
                "{} {} {}",
                put(table.lhs),
                table.joined_by(),
                put(table.rhs)
            );
            let binders = put(table.binders);
            // A fact that the tactic moves the cast is the equation proved
            // by it; one that it does not, the tactic failing on it, with
            // nothing left unproved.
            // The letters the binders give, which the failing check takes by
            // name, as the proving one has them.
            let names: Vec<&str> = binders
                .split(['(', ')'])
                .filter_map(|group| group.split(':').next())
                .flat_map(str::split_whitespace)
                .collect();
            let names = names.join(" ");
            let checked = |tactic: &str, moves: bool| {
                match moves {
                true => format!("example {binders} : {equation} := by {tactic}\n"),
                false => format!(
                    "example : True := by\n  fail_if_success (have : ∀ {binders}, {equation} := by intro {names}; {tactic})\n  trivial\n"
                ),
            }
            };
            out.push_str(&format!(
                "-- {:?} {s} to {t}: push_cast {}, norm_cast {}\n",
                table.op,
                if f.push_cast { "moves" } else { "stops" },
                if f.norm_cast { "moves" } else { "stops" },
            ));
            let (push_cast, norm_cast) = table.tactics();
            out.push_str(&checked(push_cast, f.push_cast));
            out.push_str(&checked(norm_cast, f.norm_cast));
            out.push('\n');
        }
    }
    out.push_str(&format!("end {module}\n"));
    out
}

/// Whether `norm_cast` moves every cast in `term`, a statement as the writer
/// writes it, to where it stands nowhere but on letters and numerals: each
/// operation between a cast and the top is one the table says `norm_cast`
/// moves a cast of that pair of types through. `exact_mod_cast` closes a
/// goal from a term whose statement differs from it only in casts where
/// this holds of both, as `norm_cast` brings both to the same form. A cast
/// of a term to its own type is no cast.
pub fn norm_cast_moves_all(term: &Term) -> bool {
    moves_all(term, &[], Mover::NormCast)
}

/// Whether `push_cast` moves every cast in `term` to the letters and
/// numerals, as `norm_cast_moves_all` asks of `norm_cast`: the casts of two
/// statements alike but for them are then pushed in alike, and what is left
/// between them is the ring's, which `parley_norm`'s `push_cast; ring1`
/// checks. Of a relation, within each side: `push_cast` moves the casts
/// inside each side and never through the relation, which the table says it
/// does not, and the closers it serves compare the sides so pushed:
/// `linear_combination` takes their difference, `a - b - (c - d) = 0`, and
/// `push_cast at h ⊢; exact h` the two relations side by side.
pub fn push_cast_moves_all_in_sides(term: &Term) -> bool {
    use super::doc::TermKind;
    match &term.kind {
        TermKind::Paren(inner) => push_cast_moves_all_in_sides(inner),
        TermKind::Infix { op, lhs, rhs }
            if matches!(op.symbol, "=" | "≠" | "<" | ">" | "≤" | "≥") =>
        {
            push_cast_moves_all(lhs) && push_cast_moves_all(rhs)
        }
        _ => push_cast_moves_all(term),
    }
}

/// Whether `push_cast` moves every cast of `term` to its letters and
/// numerals, by the cast table, through every operation above each.
pub fn push_cast_moves_all(term: &Term) -> bool {
    moves_all(term, &[], Mover::PushCast)
}

/// A statement as `norm_cast` leaves it where it moves every cast
/// (`norm_cast_moves_all`), for comparing two such: its casts gone and
/// brackets with them, and the norm of a cast real its absolute value,
/// `‖(a : ℂ)‖` as `|a|`, which the table says `norm_cast` takes it to.
/// Two statements in one type whose forms are alike `norm_cast` brings to
/// one, and `exact_mod_cast` closes the one by the other.
pub fn norm_cast_form(term: &Term) -> Term {
    use super::doc::TermKind;
    match &term.kind {
        TermKind::Cast { inner, .. } | TermKind::Paren(inner) => {
            return norm_cast_form(inner)
        }
        // A natural number written in ℤ and taken back to ℕ is that number
        // (the table's `ToNat`).
        TermKind::ToNat(inner) => {
            if let Some(natural) = as_natural(inner) {
                return norm_cast_form(&natural);
            }
        }
        TermKind::Enclosed {
            open: "‖", inner, ..
        } if matches!(inner.kind, TermKind::Cast { .. }) => {
            return absolute(norm_cast_form(inner));
        }
        // `abs x` and `|x|` are one function written two ways.
        TermKind::App { head, args, .. } => {
            if let (TermKind::Const(c), [super::doc::Arg::Explicit(x)]) =
                (&head.kind, args.as_slice())
            {
                if c.name == "abs" {
                    return absolute(norm_cast_form(x));
                }
            }
        }
        _ => {}
    }
    let mut out = term.clone();
    for c in out.children_mut() {
        *c = norm_cast_form(c);
    }
    out.untyped()
}

/// A term written in ℤ that is a natural number as `norm_cast` reads it,
/// as that natural number: a natural number cast up, an integer's `toNat`,
/// a numeral, and a sum, product or power to a natural exponent of such,
/// `(2 : ℤ) ^ k.toNat` as `2 ^ k.toNat`. None of any other term, a
/// difference among them, which ℕ does not compute as ℤ does.
pub fn as_natural(term: &Term) -> Option<Term> {
    use super::doc::{LeanType, Op, TermKind};
    let nat = LeanType::Num(Num::Nat);
    if term.ty == Some(nat.clone()) {
        return Some(term.clone());
    }
    match &term.kind {
        TermKind::Paren(inner) => as_natural(inner),
        TermKind::Cast { inner, .. } => as_natural(inner),
        TermKind::ToNat(_) => Some(term.clone()),
        TermKind::Numeral(_) => Some(Term {
            kind: term.kind.clone(),
            ty: Some(nat),
        }),
        TermKind::Infix { op, lhs, rhs } if *op == Op::PLUS || *op == Op::TIMES => {
            Some(Term::infix(*op, as_natural(lhs)?, as_natural(rhs)?, nat))
        }
        TermKind::Infix { op, lhs, rhs }
            if *op == Op::POWER && rhs.ty == Some(nat.clone()) =>
        {
            Some(Term::infix(*op, as_natural(lhs)?, (**rhs).clone(), nat))
        }
        _ => None,
    }
}

/// `|x|`.
fn absolute(x: Term) -> Term {
    Term {
        kind: super::doc::TermKind::Enclosed {
            open: "|",
            close: "|",
            inner: Box::new(x),
        },
        ty: None,
    }
}

/// The tactic a walk asks of the table.
#[derive(Clone, Copy)]
enum Mover {
    PushCast,
    NormCast,
}

impl Mover {
    fn moves(self, f: CastFacts) -> bool {
        match self {
            Mover::PushCast => f.push_cast,
            Mover::NormCast => f.norm_cast,
        }
    }
}

/// Whether `term` is a numeral, cast or not, `3` or `((1 : ℤ) : ℚ)`.
fn numeral(term: &Term) -> bool {
    use super::doc::TermKind;
    match &term.kind {
        TermKind::Numeral(_) => true,
        TermKind::Cast { inner, .. } | TermKind::Paren(inner) => numeral(inner),
        _ => false,
    }
}

/// `norm_cast_moves_all` of `term`, which stands under the operations
/// `over`, outermost first; an operation the table does not know stops a
/// cast below it.
fn moves_all(term: &Term, over: &[Option<CastOp>], by: Mover) -> bool {
    use super::doc::{Arg, LeanType, TermKind};
    let num = |t: &Term| match &t.ty {
        Some(LeanType::Num(n)) => Some(*n),
        _ => None,
    };
    let under = |op: Option<CastOp>| {
        let mut more = over.to_vec();
        more.push(op);
        more
    };
    match &term.kind {
        // A numeral given its type, `(1 : ℚ)`, is that numeral of the type,
        // which Lean elaborates as one: no cast. A numeral of another type
        // cast to it, `((1 : ℤ) : ℚ)`, is a cast.
        TermKind::Cast { inner, to }
            if matches!(inner.kind, TermKind::Numeral(_))
                && inner.ty.as_ref().is_none_or(|t| t == to) =>
        {
            true
        }
        // A letter of a general item's type α ascribed the type the item
        // is taken at, `(x : ℤ)`: Lean has x in ℤ already, and no cast.
        TermKind::Cast { inner, .. }
            if matches!(inner.ty, Some(LeanType::Things(_))) =>
        {
            moves_all(inner, over, by)
        }
        TermKind::Cast { inner, to } => {
            let (Some(from), Some(to)) =
                (inner.ty.as_ref().and_then(Carrier::of), Carrier::of(to))
            else {
                return inner.ty.as_ref() == Some(to) && moves_all(inner, over, by);
            };
            if from == to {
                return moves_all(inner, over, by);
            }
            let through = over.iter().all(|op| {
                op.is_some_and(|op| facts(op, from, to).is_some_and(|f| by.moves(f)))
            });
            through && moves_all(inner, &[], by)
        }
        TermKind::Paren(inner) => moves_all(inner, over, by),
        // The logic around statements passes a cast through to them.
        TermKind::Not(inner) => moves_all(inner, over, by),
        TermKind::Quantified { guard, body, .. } => {
            guard.as_ref().is_none_or(|g| moves_all(g, over, by))
                && moves_all(body, over, by)
        }
        // A quotient of numerals, cast or not, which the table says
        // `norm_cast` takes otherwise than the goal has it.
        TermKind::Infix { op, lhs, rhs }
            if op.symbol == "/" && numeral(lhs) && numeral(rhs) =>
        {
            let quotient = |f: CastFacts| by.moves(f);
            [(Z, Q), (Z, R), (Q, R)].iter().all(|(from, to)| {
                facts(CastOp::NumeralQuotient, *from, *to).is_some_and(quotient)
            })
        }
        TermKind::Infix { op, lhs, rhs } => {
            let at = match op.symbol {
                "∧" | "∨" | "→" | "↔" => {
                    return moves_all(lhs, over, by) && moves_all(rhs, over, by)
                }
                "+" => Some(CastOp::Add),
                "-" => Some(CastOp::Sub),
                "*" => Some(CastOp::Mul),
                "/" => Some(CastOp::Div),
                "^" => match num(rhs) {
                    Some(Num::Nat) => Some(CastOp::NatPow),
                    Some(Num::Int) => Some(CastOp::IntPow),
                    Some(Num::Real | Num::Complex) => Some(CastOp::RealPow),
                    _ if matches!(
                        rhs.kind,
                        TermKind::ToNat(_) | TermKind::Numeral(_)
                    ) =>
                    {
                        Some(CastOp::NatPow)
                    }
                    _ => None,
                },
                "=" | "≠" => Some(CastOp::Eq),
                "<" | ">" => Some(CastOp::Lt),
                "≤" | "≥" => Some(CastOp::Le),
                _ => None,
            };
            moves_all(lhs, &under(at), by) && moves_all(rhs, &under(at), by)
        }
        TermKind::Neg(inner) => moves_all(inner, &under(Some(CastOp::Neg)), by),
        // An integer taken to ℕ is a natural number whatever it is of: a
        // cast inside it stands under it alone, as under a norm.
        TermKind::ToNat(inner) => moves_all(inner, &[Some(CastOp::ToNat)], by),
        TermKind::Enclosed { open, inner, .. } => {
            match *open {
                "|" => moves_all(inner, &under(Some(CastOp::Abs)), by),
                // A norm is real and a floor an integer, whatever they are
                // of: a cast inside one stands under it alone, and what is
                // above it is in another type than the cast's.
                "‖" => moves_all(inner, &[Some(CastOp::Norm)], by),
                "⌊" => moves_all(inner, &[Some(CastOp::Floor)], by),
                _ => moves_all(inner, &under(None), by),
            }
        }
        TermKind::App { head, args, .. } => {
            let at = match &head.kind {
                TermKind::Const(c) => match c.name.as_str() {
                    "abs" => Some(CastOp::Abs),
                    "Real.sqrt" => Some(CastOp::Sqrt),
                    "Real.exp" | "Complex.exp" => Some(CastOp::Exp),
                    "Real.log" | "Complex.log" => Some(CastOp::Log),
                    "Real.sin" | "Complex.sin" => Some(CastOp::Sin),
                    "Real.cos" | "Complex.cos" => Some(CastOp::Cos),
                    _ => None,
                },
                _ => None,
            };
            // A function the table does not know, `Polynomial.aeval x p`:
            // a cast inside an argument stands under it alone, as under a
            // norm, since `push_cast` and `norm_cast` rewrite inside the
            // argument and take no cast across the function.
            let below = match at {
                Some(_) => under(at),
                None => Vec::new(),
            };
            moves_all(head, &below, by)
                && args.iter().all(|a| match a {
                    Arg::Explicit(t) | Arg::Named { value: t, .. } => {
                        moves_all(t, &below, by)
                    }
                })
        }
        TermKind::Bound { form, .. } => {
            let at = match form {
                super::doc::BoundForm::BigOp { product: false, .. } => {
                    Some(CastOp::Sum)
                }
                super::doc::BoundForm::BigOp { product: true, .. } => {
                    Some(CastOp::Prod)
                }
                _ => None,
            };
            let below = under(at);
            term.children().iter().all(|c| moves_all(c, &below, by))
        }
        _ => term
            .children()
            .iter()
            .all(|c| moves_all(c, &under(None), by)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A sum is taken through every widening between number types, and a
    /// count's from ℕ to ℕ∞ besides.
    #[test]
    fn a_sum_takes_every_widening_and_counts_into_extended_naturals() {
        for w in WIDENINGS {
            assert!(
                ADDED.contains(w),
                "{:?} → {:?} missing from ADDED",
                w.from,
                w.to
            );
        }
        assert!(ADDED.contains(&moves_both(N, E)));
        assert_eq!(ADDED.len(), WIDENINGS.len() + 1);
    }

    /// The type the table casts between prints as Lean writes it.
    #[test]
    fn a_carrier_prints_as_lean_writes_its_type() {
        assert_eq!(E.lean_type().text(), "ℕ∞");
        assert_eq!(Q.lean_type().text(), "ℚ");
    }
}
