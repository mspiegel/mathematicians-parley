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
    Sum,
    Prod,
}

/// What `push_cast` and `norm_cast` do with a cast from one number type to
/// another around one operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CastFacts {
    pub from: Num,
    pub to: Num,
    pub push_cast: bool,
    pub norm_cast: bool,
}

/// One operation's facts, and the equation each is checked by: `lhs` the
/// operation in `{S}` cast to `{T}`, `rhs` it on the casts, over the letters
/// `binders` declares, each with the two types put for `{S}` and `{T}`.
struct OpTable {
    op: CastOp,
    binders: &'static str,
    lhs: &'static str,
    rhs: &'static str,
    facts: &'static [CastFacts],
}

const fn moves_both(from: Num, to: Num) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: true,
        norm_cast: true,
    }
}

const fn moves_by_norm_cast(from: Num, to: Num) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: false,
        norm_cast: true,
    }
}

const fn stops(from: Num, to: Num) -> CastFacts {
    CastFacts {
        from,
        to,
        push_cast: false,
        norm_cast: false,
    }
}

use Num::{Complex as C, Int as Z, Nat as N, Rat as Q, Real as R};

/// Every widening between the number types the writer casts between.
const WIDENINGS: &[CastFacts] = &[
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
];

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

const TABLES: &[OpTable] = &[
    OpTable {
        op: CastOp::Add,
        binders: "(a b : {S})",
        lhs: "((a + b : {S}) : {T})",
        rhs: "(a : {T}) + (b : {T})",
        facts: WIDENINGS,
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
        op: CastOp::Sum,
        binders: "(s : Finset ℕ) (f : ℕ → {S})",
        lhs: "((∑ i ∈ s, f i : {S}) : {T})",
        rhs: "∑ i ∈ s, (f i : {T})",
        facts: WIDENINGS,
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
pub fn facts(op: CastOp, from: Num, to: Num) -> Option<CastFacts> {
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
            let (s, t) = (f.from.lean(), f.to.lean());
            let put = |text: &str| text.replace("{S}", s).replace("{T}", t);
            let equation = format!("{} = {}", put(table.lhs), put(table.rhs));
            let binders = put(table.binders);
            // A fact that the tactic moves the cast is the equation proved
            // by it; one that it does not, the tactic failing on it, with
            // nothing left unproved.
            let checked = |tactic: &str, moves: bool| {
                match moves {
                true => format!("example {binders} : {equation} := by {tactic}\n"),
                false => format!(
                    "example : True := by\n  fail_if_success (have : ∀ {binders}, {equation} := by intros; {tactic})\n  trivial\n"
                ),
            }
            };
            out.push_str(&format!(
                "-- {:?} {s} to {t}: push_cast {}, norm_cast {}\n",
                table.op,
                if f.push_cast { "moves" } else { "stops" },
                if f.norm_cast { "moves" } else { "stops" },
            ));
            out.push_str(&checked("push_cast; try rfl", f.push_cast));
            out.push_str(&checked("norm_cast", f.norm_cast));
            out.push('\n');
        }
    }
    out.push_str(&format!("end {module}\n"));
    out
}
