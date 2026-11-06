//! Lean terms and propositions as trees.

use crate::lean::templates::Num;

/// A Lean type a term has.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LeanType {
    /// A number type.
    Num(Num),
    /// The number type an item's general letters range over, `K`.
    General,
    /// The natural numbers with ∞, a count of any set: `ℕ∞`.
    ENat,
    /// A proposition.
    Prop,
    /// Sets of members of a type.
    Set(Box<LeanType>),
    /// The type variable numbered, α, β, ….
    Things(usize),
    /// The elements of the group of that page name.
    Elements(String),
    /// Functions from one type to another.
    Fun {
        from: Box<LeanType>,
        to: Box<LeanType>,
    },
}

/// Where a constant a term names comes from, which is what a file that
/// names it imports.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Source {
    /// Lean itself.
    Core,
    /// Mathlib.
    Mathlib,
    /// A bridge module of `corpus/lean-bridges/`, by its name.
    Bridge(String),
    /// A module of the generated library, by its full name.
    Item(String),
}

/// A constant, by its full Lean name, and where it comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstRef {
    pub name: String,
    pub source: Source,
}

/// Which side of an infix operator chains without brackets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Assoc {
    Left,
    Right,
    Neither,
}

/// An infix operator: its symbol, how tightly it binds, and which side
/// chains.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Op {
    pub symbol: &'static str,
    pub prec: u32,
    pub assoc: Assoc,
}

impl Op {
    /// Lean's infix operator of that symbol; None for any other text.
    pub fn of(symbol: &str) -> Option<Op> {
        let (symbol, prec, assoc): (&'static str, u32, Assoc) = match symbol {
            "↔" => ("↔", 20, Assoc::Neither),
            "→" => ("→", 25, Assoc::Right),
            "∨" => ("∨", 30, Assoc::Right),
            "∧" => ("∧", 35, Assoc::Right),
            "=" => ("=", 50, Assoc::Neither),
            "≠" => ("≠", 50, Assoc::Neither),
            "<" => ("<", 50, Assoc::Neither),
            ">" => (">", 50, Assoc::Neither),
            "≤" => ("≤", 50, Assoc::Neither),
            "≥" => ("≥", 50, Assoc::Neither),
            "∣" => ("∣", 50, Assoc::Neither),
            "∈" => ("∈", 50, Assoc::Neither),
            "∉" => ("∉", 50, Assoc::Neither),
            "⊆" => ("⊆", 50, Assoc::Neither),
            "⊂" => ("⊂", 50, Assoc::Neither),
            "≡" => ("≡", 50, Assoc::Neither),
            "+" => ("+", 65, Assoc::Left),
            "-" => ("-", 65, Assoc::Left),
            "∪" => ("∪", 65, Assoc::Left),
            "*" => ("*", 70, Assoc::Left),
            "/" => ("/", 70, Assoc::Left),
            "%" => ("%", 70, Assoc::Left),
            "∩" => ("∩", 70, Assoc::Left),
            "\\" => ("\\", 70, Assoc::Left),
            "^" => ("^", 75, Assoc::Right),
            "∘" => ("∘", 90, Assoc::Right),
            _ => return None,
        };
        Some(Op {
            symbol,
            prec,
            assoc,
        })
    }

    /// The least precedence each side needs to stand unbracketed.
    pub fn needs(self) -> (u32, u32) {
        match self.assoc {
            Assoc::Left => (self.prec, self.prec + 1),
            Assoc::Right => (self.prec + 1, self.prec),
            Assoc::Neither => (self.prec + 1, self.prec + 1),
        }
    }
}

/// How a count of a set is written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CountForm {
    /// A natural number, of a set known finite: `A.ncard`.
    Natural,
    /// In ℕ∞, as set.mm's ♯ counts: `A.encard`.
    Extended,
}

/// A quantifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quant {
    ForAll,
    Exists,
}

/// An argument a function or a declaration is applied to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// By its place.
    Explicit(Term),
    /// By the binder's name, `(x := v)`.
    Named { name: String, value: Term },
}

/// A Lean term or proposition, with its type. Every node has one but text
/// the writer made without a tree (`TermKind::Raw`), whose type went into
/// the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term {
    pub kind: TermKind,
    pub ty: Option<LeanType>,
}

/// What a term is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermKind {
    /// Lean text the writer made without a tree, with the precedence of its
    /// outermost operator. It stands only while the writer's functions move
    /// to trees one at a time, and goes when the last does.
    Raw { text: String, prec: u32 },
    /// A letter, as Lean names it.
    Letter(String),
    /// A constant.
    Const(ConstRef),
    /// A numeral, as written.
    Numeral(String),
    /// A function or constant applied to arguments.
    App { head: Box<Term>, args: Vec<Arg> },
    /// Two terms joined by an infix operator.
    Infix {
        op: Op,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
    /// `¬ p`.
    Not(Box<Term>),
    /// `-x`.
    Neg(Box<Term>),
    /// `(x : T)`: the term at a type, its own or one it is cast to.
    Cast { inner: Box<Term>, to: LeanType },
    /// A count of a set, in the form it is written.
    Count { set: Box<Term>, form: CountForm },
    /// `n.toNat`.
    ToNat(Box<Term>),
    /// `x.f`: a field or projection, `.Finite`, `.mp`, `.2`.
    Field { inner: Box<Term>, field: String },
    /// `∃ x : T, body`, `∀ x : T, g → body`: a quantifier over a letter of
    /// a type, with a condition on it where there is one.
    Quantified {
        quant: Quant,
        letter: String,
        letter_ty: LeanType,
        guard: Option<Box<Term>>,
        body: Box<Term>,
    },
    /// A bracket no precedence asks for, kept where the writer writes one.
    Paren(Box<Term>),
}

impl Term {
    /// Lean text with its precedence, kept as text.
    pub fn raw(text: impl Into<String>, prec: u32) -> Term {
        Term {
            kind: TermKind::Raw {
                text: text.into(),
                prec,
            },
            ty: None,
        }
    }

    /// A node of this kind and type.
    pub fn of(kind: TermKind, ty: LeanType) -> Term {
        Term { kind, ty: Some(ty) }
    }

    /// The term at a type: `(x : T)`.
    pub fn cast(inner: Term, to: LeanType) -> Term {
        Term::of(
            TermKind::Cast {
                inner: Box::new(inner),
                to: to.clone(),
            },
            to,
        )
    }

    /// Every node of the tree, this one first.
    pub fn walk(&self) -> Vec<&Term> {
        let mut out = vec![self];
        let mut i = 0;
        while i < out.len() {
            let node = out[i];
            out.extend(node.children());
            i += 1;
        }
        out
    }

    /// The terms directly inside this one.
    pub fn children(&self) -> Vec<&Term> {
        match &self.kind {
            TermKind::Raw { .. }
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_) => Vec::new(),
            TermKind::App { head, args } => {
                let mut out = vec![&**head];
                out.extend(args.iter().map(|a| match a {
                    Arg::Explicit(t) => t,
                    Arg::Named { value, .. } => value,
                }));
                out
            }
            TermKind::Infix { lhs, rhs, .. } => vec![&**lhs, &**rhs],
            TermKind::Not(t)
            | TermKind::Neg(t)
            | TermKind::ToNat(t)
            | TermKind::Paren(t) => {
                vec![&**t]
            }
            TermKind::Cast { inner, .. } => vec![&**inner],
            TermKind::Count { set, .. } => vec![&**set],
            TermKind::Field { inner, .. } => vec![&**inner],
            TermKind::Quantified { guard, body, .. } => {
                let mut out: Vec<&Term> = guard.iter().map(|g| &**g).collect();
                out.push(body);
                out
            }
        }
    }

    /// The constants the tree names.
    pub fn constants(&self) -> Vec<&ConstRef> {
        self.walk()
            .into_iter()
            .filter_map(|t| match &t.kind {
                TermKind::Const(c) => Some(c),
                _ => None,
            })
            .collect()
    }
}
