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
    /// A type of any universe, what a group's carrier is: `Type*`.
    Universe,
    /// The subgroups of the group of that page name.
    Subgroup(String),
}

impl LeanType {
    /// Whether it is `ty`, or is made of it, as `Set (Set α)` is of `Set
    /// α`.
    pub fn contains(&self, ty: &LeanType) -> bool {
        self == ty
            || match self {
                LeanType::Set(inner) => inner.contains(ty),
                LeanType::Fun { from, to } => from.contains(ty) || to.contains(ty),
                _ => false,
            }
    }

    /// Whether Lean reads it alike wherever it is written: no item's
    /// general type, type variable, or group named by the page.
    pub fn fixed(&self) -> bool {
        match self {
            LeanType::Num(_) | LeanType::ENat | LeanType::Prop => true,
            LeanType::Set(inner) => inner.fixed(),
            LeanType::Fun { from, to } => from.fixed() && to.fixed(),
            LeanType::General
            | LeanType::Things(_)
            | LeanType::Elements(_)
            | LeanType::Universe
            | LeanType::Subgroup(_) => false,
        }
    }

    /// Whether it is a type of sets, or is made of one, `ℤ → Set ℕ`.
    pub fn has_set(&self) -> bool {
        match self {
            LeanType::Set(_) => true,
            LeanType::Fun { from, to } => from.has_set() || to.has_set(),
            _ => false,
        }
    }
}

/// Where a constant a term names comes from, which is what a file that
/// names it imports.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Source {
    /// Lean itself.
    Core,
    /// Mathlib.
    Mathlib,
    /// A bridge module of `corpus/lean-bridges/`.
    Bridge(super::bridges::BridgeModule),
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
    /// Composition of functions, `g ∘ f`.
    pub const COMPOSE: Op = Op {
        symbol: "∘",
        prec: 90,
        assoc: Assoc::Right,
    };

    /// Equality, `a = b`.
    pub const EQUALS: Op = Op {
        symbol: "=",
        prec: 50,
        assoc: Assoc::Neither,
    };

    /// Conjunction, `a ∧ b`.
    pub const AND: Op = Op {
        symbol: "∧",
        prec: 35,
        assoc: Assoc::Right,
    };

    /// An order, `a ≤ b`.
    pub const AT_MOST: Op = Op {
        symbol: "≤",
        prec: 50,
        assoc: Assoc::Neither,
    };

    /// Addition, `a + b`.
    pub const PLUS: Op = Op {
        symbol: "+",
        prec: 65,
        assoc: Assoc::Left,
    };

    /// Division, `a / b`.
    pub const DIVIDE: Op = Op {
        symbol: "/",
        prec: 70,
        assoc: Assoc::Left,
    };

    /// Subtraction, `a - b`.
    pub const MINUS: Op = Op {
        symbol: "-",
        prec: 65,
        assoc: Assoc::Left,
    };

    /// A power, `a ^ b`.
    pub const POWER: Op = Op {
        symbol: "^",
        prec: 75,
        assoc: Assoc::Right,
    };

    /// Multiplication, `a * b`, a group's operation too.
    pub const TIMES: Op = Op {
        symbol: "*",
        prec: 70,
        assoc: Assoc::Left,
    };

    /// Lean's infix operator of that symbol; None for any other text.
    pub fn of(symbol: &str) -> Option<Op> {
        let (symbol, prec, assoc): (&'static str, u32, Assoc) = match symbol {
            "↔" => ("↔", 20, Assoc::Neither),
            "→" => ("→", 25, Assoc::Right),
            "∨" => ("∨", 30, Assoc::Right),
            "∧" => return Some(Op::AND),
            "=" => return Some(Op::EQUALS),
            "≠" => ("≠", 50, Assoc::Neither),
            "<" => ("<", 50, Assoc::Neither),
            ">" => (">", 50, Assoc::Neither),
            "≤" => return Some(Op::AT_MOST),
            "≥" => ("≥", 50, Assoc::Neither),
            "∣" => ("∣", 50, Assoc::Neither),
            "∈" => ("∈", 50, Assoc::Neither),
            "∉" => ("∉", 50, Assoc::Neither),
            "⊆" => ("⊆", 50, Assoc::Neither),
            "⊂" => ("⊂", 50, Assoc::Neither),
            "≡" => ("≡", 50, Assoc::Neither),
            "+" => return Some(Op::PLUS),
            "-" => return Some(Op::MINUS),
            "∪" => ("∪", 65, Assoc::Left),
            "*" => return Some(Op::TIMES),
            "/" => return Some(Op::DIVIDE),
            "%" => ("%", 70, Assoc::Left),
            "∩" => ("∩", 70, Assoc::Left),
            // Lean declares `\` `infix:70`: `A \ B \ C` does not parse.
            "\\" => ("\\", 70, Assoc::Neither),
            "^" => ("^", 75, Assoc::Right),
            // `f '' s` and `f ⁻¹' s`, Mathlib's image and preimage of a set.
            "''" => ("''", 80, Assoc::Left),
            "⁻¹'" => ("⁻¹'", 80, Assoc::Left),
            "∘" => return Some(Op::COMPOSE),
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

/// A binder of one letter: a quantifier, or `fun`, which makes a function
/// of its body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Quant {
    ForAll,
    Exists,
    Fun,
}

/// A notation that binds one letter over a body (`TermKind::Bound`), with
/// what the letter runs over, which stands outside its scope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundForm {
    /// `∑ k ∈ set, body` or `∏ k ∈ set, body`, and over a finite set `∑ᶠ`,
    /// `∏ᶠ`; `need` is the precedence `set` stands at.
    BigOp {
        product: bool,
        finite: bool,
        set: Box<Term>,
        need: u32,
    },
    /// `∫ x in from..to, body`.
    Integral { from: Box<Term>, to: Box<Term> },
    /// `{x : T | body}`.
    SetOf,
    /// `{x ∈ set | body}`.
    SetOfMember { set: Box<Term> },
    /// `⋃ x ∈ set, body`.
    Union { set: Box<Term> },
}

impl BoundForm {
    /// What the letter runs over.
    pub fn over(&self) -> Vec<&Term> {
        match self {
            BoundForm::BigOp { set, .. }
            | BoundForm::SetOfMember { set }
            | BoundForm::Union { set } => vec![&**set],
            BoundForm::Integral { from, to } => vec![&**from, &**to],
            BoundForm::SetOf => Vec::new(),
        }
    }

    /// What the letter runs over, to change in place.
    pub fn over_mut(&mut self) -> Vec<&mut Term> {
        match self {
            BoundForm::BigOp { set, .. }
            | BoundForm::SetOfMember { set }
            | BoundForm::Union { set } => vec![&mut **set],
            BoundForm::Integral { from, to } => vec![&mut **from, &mut **to],
            BoundForm::SetOf => Vec::new(),
        }
    }
}

/// The brackets a list of terms stands between (`TermKind::Listed`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Brackets {
    /// `⟨a, b⟩`.
    Angle,
    /// `{a, b}`.
    Brace,
}

/// A mark Lean writes before a term (`TermKind::Prefix`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrefixMark {
    /// `𝒫 X`, the subsets of X.
    Powerset,
}

/// A mark Lean writes after a term (`TermKind::Postfix`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PostfixMark {
    /// `g⁻¹`, the inverse.
    Inverse,
}

/// An argument a function or a declaration is applied to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// By its place.
    Explicit(Term),
    /// By the binder's name, `(x := v)`.
    Named { name: String, value: Term },
}

impl Arg {
    /// The argument with a template's holes filled (`Term::instantiate`).
    fn instantiate(&self, args: &[Term]) -> Option<Arg> {
        Some(match self {
            Arg::Explicit(t) => Arg::Explicit(t.instantiate(args)?),
            Arg::Named { name, value } => Arg::Named {
                name: name.clone(),
                value: value.instantiate(args)?,
            },
        })
    }
}

/// A Lean term or proposition, with its type where the writer knows it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Term {
    pub kind: TermKind,
    pub ty: Option<LeanType>,
}

/// What a term is.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TermKind {
    /// A letter, as Lean names it.
    Letter(String),
    /// A constant.
    Const(ConstRef),
    /// A numeral, as written.
    Numeral(String),
    /// A function or constant applied to arguments; `explicit` where every
    /// argument is given, `@ite _ c …`.
    App {
        head: Box<Term>,
        args: Vec<Arg>,
        explicit: bool,
    },
    /// A hole of a template, numbered from 1, which `Term::instantiate`
    /// fills; none stands in a term the writer finishes.
    Hole(usize),
    /// `_`: an argument Lean finds itself.
    Elided,
    /// `?_`: a goal left for the tactics after, as in `refine ⟨w, ?_⟩`.
    Open,
    /// A term between two marks, `⌊x⌋` or `‖x‖`.
    Enclosed {
        open: &'static str,
        close: &'static str,
        inner: Box<Term>,
    },
    /// `a ≡ b [ZMOD n]`.
    ModEq {
        a: Box<Term>,
        b: Box<Term>,
        n: Box<Term>,
    },
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
        /// Written `∀ x ∈ S, body` and `∃ x ∈ S, body`: the guard is
        /// `x ∈ S`, which Lean reads as `∀ x, x ∈ S → body` and
        /// `∃ x, x ∈ S ∧ body`, one term either way.
        bounded: bool,
    },
    /// A notation binding one letter over a body (`BoundForm`): a sum or
    /// product, an integral, a set-builder. What the letter runs over, a
    /// range, a set or an integral's two ends, is the form's and stands
    /// outside its scope; the body inside.
    Bound {
        form: BoundForm,
        letter: String,
        letter_ty: LeanType,
        body: Box<Term>,
    },
    /// Terms listed between brackets: an anonymous constructor `⟨a, b⟩`, or
    /// a set listed by its members `{a, b}`.
    Listed {
        brackets: Brackets,
        items: Vec<Term>,
    },
    /// `show says proof`: a term saying `says`, proved by `proof`.
    Show { says: Box<Term>, proof: Box<Term> },
    /// `(proof : says)`: a proof given the statement it is taken as.
    Ascribed { proof: Box<Term>, says: Box<Term> },
    /// A mark before a term, `𝒫 X`.
    Prefix { mark: PrefixMark, inner: Box<Term> },
    /// A mark after a term, `g⁻¹`.
    Postfix { mark: PostfixMark, inner: Box<Term> },
    /// `(g * ·)`: the function the operator makes of its left side.
    Section { op: Op, left: Box<Term> },
    /// `fun a h => body`: a function of these letters, whose types Lean
    /// finds from where it stands, as the proof part of `⟨…⟩` takes them.
    Lambda {
        letters: Vec<String>,
        body: Box<Term>,
    },
    /// `if h : cond then yes else no`: `proof` names the proof of `cond` in
    /// `yes` and `no`.
    DependentIf {
        proof: String,
        cond: Box<Term>,
        yes: Box<Term>,
        no: Box<Term>,
    },
    /// A bracket no precedence asks for, kept where the writer writes one.
    Paren(Box<Term>),
    /// A proof standing as a term, `by t`, as the proof part of `⟨w, by t⟩`
    /// or an argument `(by parley_side)`.
    By(Box<super::tactic::Proof>),
}

impl Term {
    /// A node of this kind and type.
    pub fn of(kind: TermKind, ty: LeanType) -> Term {
        Term { kind, ty: Some(ty) }
    }

    /// A letter of a type, as Lean names it.
    pub fn letter(name: impl Into<String>, ty: LeanType) -> Term {
        Term::of(TermKind::Letter(name.into()), ty)
    }

    /// A numeral of a type, as written.
    pub fn numeral(digits: impl Into<String>, ty: LeanType) -> Term {
        Term::of(TermKind::Numeral(digits.into()), ty)
    }

    /// `True`.
    pub fn truth() -> Term {
        Term::of(
            TermKind::Const(ConstRef {
                name: "True".to_string(),
                source: Source::Core,
            }),
            LeanType::Prop,
        )
    }

    /// Whether the term is `True`.
    pub fn is_truth(&self) -> bool {
        matches!(&self.kind, TermKind::Const(c) if c.name == "True")
    }

    /// A constant, standing alone.
    pub fn constant(name: &str, source: Source, ty: LeanType) -> Term {
        Term::of(
            TermKind::Const(ConstRef {
                name: name.to_string(),
                source,
            }),
            ty,
        )
    }

    /// A constant as a function some notation applies, whose own type no
    /// part of the writer reads.
    pub fn head(name: &str, source: Source) -> Term {
        Term {
            kind: TermKind::Const(ConstRef {
                name: name.to_string(),
                source,
            }),
            ty: None,
        }
    }

    /// A constant applied to arguments by place.
    pub fn applied(name: &str, source: Source, args: Vec<Term>, ty: LeanType) -> Term {
        let head = Term::head(name, source);
        Term::of(
            TermKind::App {
                head: Box::new(head),
                args: args.into_iter().map(Arg::Explicit).collect(),
                explicit: false,
            },
            ty,
        )
    }

    /// Two terms joined by an infix operator.
    pub fn infix(op: Op, lhs: Term, rhs: Term, ty: LeanType) -> Term {
        Term::of(
            TermKind::Infix {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            ty,
        )
    }

    /// The term with the type the writer knows it has, where the node it
    /// was made as did not say one: a template filled, whose type is the
    /// one its notation yields there.
    pub fn typed(mut self, ty: LeanType) -> Term {
        if self.ty.is_none() {
            self.ty = Some(ty);
        }
        self
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
            TermKind::By(_)
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Open => Vec::new(),
            TermKind::Enclosed { inner, .. } => vec![&**inner],
            TermKind::ModEq { a, b, n } => vec![&**a, &**b, &**n],
            TermKind::App { head, args, .. } => {
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
            TermKind::Bound { form, body, .. } => {
                let mut out = form.over();
                out.push(body);
                out
            }
            TermKind::Lambda { body, .. } => vec![&**body],
            TermKind::Listed { items, .. } => items.iter().collect(),
            TermKind::Show { says, proof } => vec![&**says, &**proof],
            TermKind::Ascribed { proof, says } => vec![&**proof, &**says],
            TermKind::Prefix { inner, .. } | TermKind::Postfix { inner, .. } => {
                vec![&**inner]
            }
            TermKind::Section { left, .. } => vec![&**left],
            TermKind::DependentIf { cond, yes, no, .. } => vec![&**cond, &**yes, &**no],
        }
    }

    /// The terms directly inside this one, to change in place.
    pub fn children_mut(&mut self) -> Vec<&mut Term> {
        match &mut self.kind {
            TermKind::By(_)
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Open => Vec::new(),
            TermKind::Enclosed { inner, .. }
            | TermKind::Cast { inner, .. }
            | TermKind::Field { inner, .. } => vec![&mut **inner],
            TermKind::ModEq { a, b, n } => vec![&mut **a, &mut **b, &mut **n],
            TermKind::App { head, args, .. } => {
                let mut out = vec![&mut **head];
                out.extend(args.iter_mut().map(|a| match a {
                    Arg::Explicit(t) => t,
                    Arg::Named { value, .. } => value,
                }));
                out
            }
            TermKind::Infix { lhs, rhs, .. } => vec![&mut **lhs, &mut **rhs],
            TermKind::Not(t)
            | TermKind::Neg(t)
            | TermKind::ToNat(t)
            | TermKind::Paren(t) => {
                vec![&mut **t]
            }
            TermKind::Count { set, .. } => vec![&mut **set],
            TermKind::Quantified { guard, body, .. } => {
                let mut out: Vec<&mut Term> =
                    guard.iter_mut().map(|g| &mut **g).collect();
                out.push(body);
                out
            }
            TermKind::Bound { form, body, .. } => {
                let mut out = form.over_mut();
                out.push(body);
                out
            }
            TermKind::Lambda { body, .. } => vec![&mut **body],
            TermKind::Listed { items, .. } => items.iter_mut().collect(),
            TermKind::Show { says, proof } => vec![&mut **says, &mut **proof],
            TermKind::Ascribed { proof, says } => vec![&mut **proof, &mut **says],
            TermKind::Prefix { inner, .. } | TermKind::Postfix { inner, .. } => {
                vec![&mut **inner]
            }
            TermKind::Section { left, .. } => vec![&mut **left],
            TermKind::DependentIf { cond, yes, no, .. } => {
                vec![&mut **cond, &mut **yes, &mut **no]
            }
        }
    }

    /// The side tactic of sets wherever the side tactic stands in a proof
    /// inside the term.
    pub fn set_side(&mut self) {
        if let TermKind::By(p) = &mut self.kind {
            p.set_side();
        }
        for c in self.children_mut() {
            c.set_side();
        }
    }

    /// The constants of Lean's or Mathlib's this node names: its own, and
    /// those its printed form names through Lean's resolution of a field,
    /// `A.ncard` for `Set.ncard`.
    pub fn named(&self) -> Vec<super::file::Lookup> {
        use super::file::Lookup;
        let name = match &self.kind {
            TermKind::Const(c) => match c.source {
                Source::Core | Source::Mathlib => c.name.as_str(),
                Source::Bridge(_) | Source::Item(_) => return Vec::new(),
            },
            TermKind::Count { form, .. } => match form {
                CountForm::Natural => "Set.ncard",
                CountForm::Extended => "Set.encard",
            },
            TermKind::Field { field, .. } if field == "Finite" => "Set.Finite",
            _ => return Vec::new(),
        };
        vec![Lookup::Const(name.to_string())]
    }

    /// The node's own syntax with each term inside it a letter, `a ≡ a
    /// [ZMOD a]` of a congruence: what Lean is asked the modules of. None
    /// for a node whose syntax is Lean's own, or that only names (`named`).
    pub fn sample(&self) -> Option<String> {
        match &self.kind {
            TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Open
            | TermKind::By(_)
            | TermKind::Paren(_)
            | TermKind::Count { .. }
            | TermKind::Field { .. }
            | TermKind::ToNat(_) => None,
            // An application is its function's syntax, Lean's own: a sample
            // of it asks only the instances its arguments' types take, where
            // the function is Lean's or Mathlib's.
            TermKind::App {
                head,
                args,
                explicit,
            } => {
                let TermKind::Const(c) = &head.kind else {
                    return None;
                };
                if !matches!(c.source, Source::Core | Source::Mathlib) {
                    return None;
                }
                let sample = Term {
                    kind: TermKind::App {
                        head: head.clone(),
                        args: args
                            .iter()
                            .map(|a| match a {
                                Arg::Explicit(t) => Arg::Explicit(Term::placeholder(t)),
                                Arg::Named { name, value } => Arg::Named {
                                    name: name.clone(),
                                    value: Term::placeholder(value),
                                },
                            })
                            .collect(),
                        explicit: *explicit,
                    },
                    ty: self.ty.clone(),
                };
                Some(sample.text())
            }
            _ => {
                let mut sample = self.clone();
                for c in sample.children_mut() {
                    *c = Term::placeholder(c);
                }
                Some(sample.text())
            }
        }
    }

    /// What stands for a term inside a sample: `(sorry : T)` of its type,
    /// so that Lean elaborates the sample as the file does, with the
    /// instances its types take; `by skip` for a proof; a letter where the
    /// type is not one a sample can write.
    fn placeholder(term: &Term) -> Term {
        use super::tactic::{Proof, Tactic, TacticRef};
        match (&term.kind, &term.ty) {
            (TermKind::By(_), _) => Term {
                kind: TermKind::By(Box::new(Proof::By(Tactic::Call {
                    tactic: TacticRef::Mathlib("skip"),
                    args: Vec::new(),
                }))),
                ty: None,
            },
            (_, Some(ty)) if ty.fixed() => {
                Term::cast(Term::letter("sorry", ty.clone()), ty.clone())
            }
            _ => Term::letter("a", LeanType::Prop),
        }
    }

    /// Whether the tree writes the type `ty` somewhere, in a cast or as a
    /// bound letter's type.
    pub fn writes_type(&self, ty: &LeanType) -> bool {
        self.has(|k| match k {
            TermKind::Cast { to, .. } => to.contains(ty),
            TermKind::Quantified { letter_ty, .. } => letter_ty.contains(ty),
            _ => false,
        })
    }

    /// Whether this node writes something of Lean's sets: a constant of
    /// `Set`'s namespace, a set counted in ℕ∞, a cast to or a letter of a
    /// type of sets, or a notation whose text names `Set`.
    pub fn about_sets(&self) -> bool {
        match &self.kind {
            TermKind::Const(c) => c.name.starts_with("Set."),
            TermKind::Count { form, .. } => *form == CountForm::Extended,
            TermKind::Cast { to, .. } => to.has_set(),
            TermKind::Quantified { letter_ty, .. } => letter_ty.has_set(),
            TermKind::Bound { letter_ty, .. } => letter_ty.has_set(),
            _ => false,
        }
    }

    /// The term with each letter `given` names put for by the term it
    /// gives, as a citation gives an item's letters values. A letter bound
    /// inside the term is left as it is where a quantifier binds it, and a
    /// binder whose letter a value names is renamed first
    /// (`binders_clear_of`).
    pub fn substituted(
        &self,
        given: &std::collections::BTreeMap<String, Term>,
    ) -> Term {
        let mut out = self.binders_clear_of(given.values());
        out.substitute(given);
        out
    }

    /// The term with each binder whose letter one of `values` names given
    /// a fresh letter, as Lean renames a bound variable a value would
    /// otherwise be captured by: `∃ m, 0 ≤ m ∧ m = n` with `m` put for `n`
    /// is `∃ m', 0 ≤ m' ∧ m' = m`, not `∃ m, 0 ≤ m ∧ m = m`.
    pub fn binders_clear_of<'a>(
        &self,
        values: impl IntoIterator<Item = &'a Term>,
    ) -> Term {
        let mut named = std::collections::BTreeSet::new();
        for v in values {
            v.letters_into(&mut named);
        }
        let mut out = self.clone();
        if named.is_empty() {
            return out;
        }
        let mut used = named.clone();
        self.letters_into(&mut used);
        out.clear_binders(&named, &mut used);
        out
    }

    /// Every letter the term names, free or bound.
    fn letters_into(&self, out: &mut std::collections::BTreeSet<String>) {
        for t in self.walk() {
            match &t.kind {
                TermKind::Letter(l)
                | TermKind::Quantified { letter: l, .. }
                | TermKind::Bound { letter: l, .. }
                | TermKind::DependentIf { proof: l, .. } => {
                    out.insert(l.clone());
                }
                TermKind::Lambda { letters, .. } => out.extend(letters.iter().cloned()),
                _ => {}
            }
        }
    }

    fn clear_binders(
        &mut self,
        named: &std::collections::BTreeSet<String>,
        used: &mut std::collections::BTreeSet<String>,
    ) {
        match &mut self.kind {
            TermKind::Quantified {
                letter,
                guard,
                body,
                ..
            } if named.contains(letter.as_str()) => {
                let new = fresh_letter(letter, used);
                if let Some(g) = guard {
                    g.rename_free(letter, &new);
                }
                body.rename_free(letter, &new);
                *letter = new;
            }
            TermKind::Bound { letter, body, .. } if named.contains(letter.as_str()) => {
                let new = fresh_letter(letter, used);
                body.rename_free(letter, &new);
                *letter = new;
            }
            TermKind::Lambda { letters, body } => {
                for l in letters.iter_mut() {
                    if named.contains(l.as_str()) {
                        let new = fresh_letter(l, used);
                        body.rename_free(l, &new);
                        *l = new;
                    }
                }
            }
            TermKind::DependentIf { proof, yes, no, .. }
                if named.contains(proof.as_str()) =>
            {
                let new = fresh_letter(proof, used);
                yes.rename_free(proof, &new);
                no.rename_free(proof, &new);
                *proof = new;
            }
            _ => {}
        }
        for c in self.children_mut() {
            c.clear_binders(named, used);
        }
    }

    /// The term with the letter `from` written `to` wherever it is free.
    fn rename_free(&mut self, from: &str, to: &str) {
        match &mut self.kind {
            TermKind::Letter(l) if l == from => {
                *l = to.to_string();
                return;
            }
            TermKind::Quantified { letter, .. } if letter == from => return,
            TermKind::Lambda { letters, .. } if letters.iter().any(|l| l == from) => {
                return
            }
            TermKind::Bound { letter, form, .. } if letter == from => {
                for o in form.over_mut() {
                    o.rename_free(from, to);
                }
                return;
            }
            TermKind::DependentIf { proof, cond, .. } if proof == from => {
                cond.rename_free(from, to);
                return;
            }
            _ => {}
        }
        for c in self.children_mut() {
            c.rename_free(from, to);
        }
    }

    fn substitute(&mut self, given: &std::collections::BTreeMap<String, Term>) {
        if let TermKind::Letter(name) = &self.kind {
            if let Some(value) = given.get(name) {
                *self = value.clone();
            }
            return;
        }
        if let TermKind::Quantified { letter, .. } = &self.kind {
            if given.contains_key(letter) {
                let mut inner = given.clone();
                inner.remove(letter);
                self.substitute_children(&inner);
                return;
            }
        }
        // A function's letters are its own in its body.
        if let TermKind::Lambda { letters, body } = &mut self.kind {
            let mut inner = given.clone();
            for l in letters.iter() {
                inner.remove(l.as_str());
            }
            body.substitute(&inner);
            return;
        }
        // The proof an `if` names is its own in its branches.
        if let TermKind::DependentIf {
            proof,
            cond,
            yes,
            no,
        } = &mut self.kind
        {
            cond.substitute(given);
            let mut inner = given.clone();
            inner.remove(proof.as_str());
            yes.substitute(&inner);
            no.substitute(&inner);
            return;
        }
        // What a bound letter runs over is outside its scope, its body
        // inside.
        if let TermKind::Bound {
            letter, form, body, ..
        } = &mut self.kind
        {
            for o in form.over_mut() {
                o.substitute(given);
            }
            let mut inner = given.clone();
            inner.remove(letter.as_str());
            body.substitute(&inner);
            return;
        }
        self.substitute_children(given);
    }

    fn substitute_children(
        &mut self,
        given: &std::collections::BTreeMap<String, Term>,
    ) {
        match &mut self.kind {
            TermKind::By(_)
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Open => {}
            TermKind::App { head, args, .. } => {
                head.substitute(given);
                for a in args {
                    match a {
                        Arg::Explicit(t) => t.substitute(given),
                        Arg::Named { value, .. } => value.substitute(given),
                    }
                }
            }
            TermKind::Infix { lhs, rhs, .. } => {
                lhs.substitute(given);
                rhs.substitute(given);
            }
            TermKind::Not(t)
            | TermKind::Neg(t)
            | TermKind::ToNat(t)
            | TermKind::Paren(t) => t.substitute(given),
            TermKind::Cast { inner, .. }
            | TermKind::Field { inner, .. }
            | TermKind::Enclosed { inner, .. } => inner.substitute(given),
            TermKind::Count { set, .. } => set.substitute(given),
            TermKind::ModEq { a, b, n } => {
                a.substitute(given);
                b.substitute(given);
                n.substitute(given);
            }
            TermKind::Quantified { guard, body, .. } => {
                if let Some(g) = guard {
                    g.substitute(given);
                }
                body.substitute(given);
            }
            TermKind::Bound { form, body, .. } => {
                for o in form.over_mut() {
                    o.substitute(given);
                }
                body.substitute(given);
            }
            TermKind::Lambda { body, .. } => body.substitute(given),
            TermKind::Listed { .. }
            | TermKind::Show { .. }
            | TermKind::Ascribed { .. }
            | TermKind::Prefix { .. }
            | TermKind::Postfix { .. }
            | TermKind::Section { .. } => {
                for c in self.children_mut() {
                    c.substitute(given);
                }
            }
            TermKind::DependentIf { cond, yes, no, .. } => {
                cond.substitute(given);
                yes.substitute(given);
                no.substitute(given);
            }
        }
    }

    /// A template's tree with hole i filled by `args[i − 1]`; None where a
    /// hole has no argument.
    pub fn instantiate(&self, args: &[Term]) -> Option<Term> {
        let kind = match &self.kind {
            TermKind::Hole(i) => return args.get(i.checked_sub(1)?).cloned(),
            TermKind::By(_)
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Elided
            | TermKind::Open => self.kind.clone(),
            TermKind::App {
                head,
                args: given,
                explicit,
            } => TermKind::App {
                head: Box::new(head.instantiate(args)?),
                args: given
                    .iter()
                    .map(|a| a.instantiate(args))
                    .collect::<Option<Vec<Arg>>>()?,
                explicit: *explicit,
            },
            TermKind::Infix { op, lhs, rhs } => TermKind::Infix {
                op: *op,
                lhs: Box::new(lhs.instantiate(args)?),
                rhs: Box::new(rhs.instantiate(args)?),
            },
            TermKind::Not(t) => TermKind::Not(Box::new(t.instantiate(args)?)),
            TermKind::Neg(t) => TermKind::Neg(Box::new(t.instantiate(args)?)),
            TermKind::ToNat(t) => TermKind::ToNat(Box::new(t.instantiate(args)?)),
            TermKind::Paren(t) => TermKind::Paren(Box::new(t.instantiate(args)?)),
            TermKind::Cast { inner, to } => TermKind::Cast {
                inner: Box::new(inner.instantiate(args)?),
                to: to.clone(),
            },
            TermKind::Count { set, form } => TermKind::Count {
                set: Box::new(set.instantiate(args)?),
                form: *form,
            },
            TermKind::Field { inner, field } => TermKind::Field {
                inner: Box::new(inner.instantiate(args)?),
                field: field.clone(),
            },
            TermKind::Enclosed { open, close, inner } => TermKind::Enclosed {
                open,
                close,
                inner: Box::new(inner.instantiate(args)?),
            },
            TermKind::ModEq { a, b, n } => TermKind::ModEq {
                a: Box::new(a.instantiate(args)?),
                b: Box::new(b.instantiate(args)?),
                n: Box::new(n.instantiate(args)?),
            },
            TermKind::Quantified {
                quant,
                letter,
                letter_ty,
                guard,
                body,
                bounded,
            } => TermKind::Quantified {
                quant: *quant,
                letter: letter.clone(),
                letter_ty: letter_ty.clone(),
                guard: match guard {
                    Some(g) => Some(Box::new(g.instantiate(args)?)),
                    None => None,
                },
                body: Box::new(body.instantiate(args)?),
                bounded: *bounded,
            },
            TermKind::Bound {
                form,
                letter,
                letter_ty,
                body,
            } => {
                let filled = |t: &Term| t.instantiate(args).map(Box::new);
                let form = match form {
                    BoundForm::BigOp {
                        product,
                        finite,
                        set,
                        need,
                    } => BoundForm::BigOp {
                        product: *product,
                        finite: *finite,
                        set: filled(set)?,
                        need: *need,
                    },
                    BoundForm::Integral { from, to } => BoundForm::Integral {
                        from: filled(from)?,
                        to: filled(to)?,
                    },
                    BoundForm::SetOf => BoundForm::SetOf,
                    BoundForm::SetOfMember { set } => {
                        BoundForm::SetOfMember { set: filled(set)? }
                    }
                    BoundForm::Union { set } => BoundForm::Union { set: filled(set)? },
                };
                TermKind::Bound {
                    form,
                    letter: letter.clone(),
                    letter_ty: letter_ty.clone(),
                    body: Box::new(body.instantiate(args)?),
                }
            }
            TermKind::Lambda { letters, body } => TermKind::Lambda {
                letters: letters.clone(),
                body: Box::new(body.instantiate(args)?),
            },
            TermKind::Listed { brackets, items } => TermKind::Listed {
                brackets: *brackets,
                items: items
                    .iter()
                    .map(|i| i.instantiate(args))
                    .collect::<Option<Vec<Term>>>()?,
            },
            TermKind::Show { says, proof } => TermKind::Show {
                says: Box::new(says.instantiate(args)?),
                proof: Box::new(proof.instantiate(args)?),
            },
            TermKind::Ascribed { proof, says } => TermKind::Ascribed {
                proof: Box::new(proof.instantiate(args)?),
                says: Box::new(says.instantiate(args)?),
            },
            TermKind::Prefix { mark, inner } => TermKind::Prefix {
                mark: *mark,
                inner: Box::new(inner.instantiate(args)?),
            },
            TermKind::Postfix { mark, inner } => TermKind::Postfix {
                mark: *mark,
                inner: Box::new(inner.instantiate(args)?),
            },
            TermKind::Section { op, left } => TermKind::Section {
                op: *op,
                left: Box::new(left.instantiate(args)?),
            },
            TermKind::DependentIf {
                proof,
                cond,
                yes,
                no,
            } => TermKind::DependentIf {
                proof: proof.clone(),
                cond: Box::new(cond.instantiate(args)?),
                yes: Box::new(yes.instantiate(args)?),
                no: Box::new(no.instantiate(args)?),
            },
        };
        Some(Term {
            kind,
            ty: self.ty.clone(),
        })
    }

    /// The term with an item's general number type, `K`, made the type a
    /// citation gives it.
    pub fn with_general(&self, at: LeanType) -> Term {
        let mut out = self.clone();
        out.set_general(&at);
        out
    }

    fn set_general(&mut self, at: &LeanType) {
        if self.ty == Some(LeanType::General) {
            self.ty = Some(at.clone());
        }
        if let TermKind::Cast { to, .. } = &mut self.kind {
            if *to == LeanType::General {
                *to = at.clone();
            }
        }
        match &mut self.kind {
            TermKind::App { head, args, .. } => {
                head.set_general(at);
                for a in args {
                    match a {
                        Arg::Explicit(t) => t.set_general(at),
                        Arg::Named { value, .. } => value.set_general(at),
                    }
                }
            }
            TermKind::Infix { lhs, rhs, .. } => {
                lhs.set_general(at);
                rhs.set_general(at);
            }
            TermKind::Not(t)
            | TermKind::Neg(t)
            | TermKind::ToNat(t)
            | TermKind::Paren(t) => t.set_general(at),
            TermKind::Cast { inner, .. }
            | TermKind::Field { inner, .. }
            | TermKind::Enclosed { inner, .. } => inner.set_general(at),
            TermKind::Count { set, .. } => set.set_general(at),
            TermKind::ModEq { a, b, n } => {
                a.set_general(at);
                b.set_general(at);
                n.set_general(at);
            }
            TermKind::Quantified { guard, body, .. } => {
                if let Some(g) = guard {
                    g.set_general(at);
                }
                body.set_general(at);
            }
            TermKind::Bound { form, body, .. } => {
                for o in form.over_mut() {
                    o.set_general(at);
                }
                body.set_general(at);
            }
            TermKind::Lambda { body, .. } => body.set_general(at),
            TermKind::Listed { .. }
            | TermKind::Show { .. }
            | TermKind::Ascribed { .. }
            | TermKind::Prefix { .. }
            | TermKind::Postfix { .. }
            | TermKind::Section { .. } => {
                for c in self.children_mut() {
                    c.set_general(at);
                }
            }
            TermKind::DependentIf { cond, yes, no, .. } => {
                cond.set_general(at);
                yes.set_general(at);
                no.set_general(at);
            }
            TermKind::By(_)
            | TermKind::Letter(_)
            | TermKind::Const(_)
            | TermKind::Numeral(_)
            | TermKind::Hole(_)
            | TermKind::Elided
            | TermKind::Open => {}
        }
    }

    /// Whether some node of the tree is of a kind `of` holds of.
    pub fn has(&self, of: impl Fn(&TermKind) -> bool) -> bool {
        self.walk().into_iter().any(|t| of(&t.kind))
    }

    /// Whether the tree takes a whole number to ℕ somewhere, `n.toNat`.
    pub fn has_to_nat(&self) -> bool {
        self.has(|k| matches!(k, TermKind::ToNat(_)))
    }

    /// Whether the tree counts a set in this form somewhere, `A.encard`.
    pub fn has_count(&self, form: CountForm) -> bool {
        self.has(|k| matches!(k, TermKind::Count { form: f, .. } if *f == form))
    }

    /// Whether the tree casts something to another type somewhere, `(n : ℚ)`
    /// of an integer n; an ascription of a term to its own type is none.
    pub fn has_cast(&self) -> bool {
        self.has(|k| matches!(k, TermKind::Cast { inner, to } if inner.ty.as_ref() != Some(to)))
    }

    /// Whether the tree casts something to `ty` somewhere, `(x : ℝ)`.
    pub fn has_cast_to(&self, ty: &LeanType) -> bool {
        self.has(|k| matches!(k, TermKind::Cast { to, .. } if to == ty))
    }

    /// Whether the tree names the constant `name`.
    pub fn names(&self, name: &str) -> bool {
        self.constants().iter().any(|c| c.name == name)
    }

    /// The same tree with no node's type kept, a bound letter's among them:
    /// two terms Lean writes alike compare equal whatever types the writer
    /// knew of their parts.
    pub fn untyped(&self) -> Term {
        let mut out = self.clone();
        out.clear_types();
        out
    }

    fn clear_types(&mut self) {
        self.ty = None;
        if let TermKind::Quantified { letter_ty, .. }
        | TermKind::Bound { letter_ty, .. } = &mut self.kind
        {
            *letter_ty = LeanType::General;
        }
        for c in self.children_mut() {
            c.clear_types();
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

/// A letter not among `used`, made from `letter` by priming it, as Lean
/// writes a renamed bound variable; it joins `used`.
fn fresh_letter(letter: &str, used: &mut std::collections::BTreeSet<String>) -> String {
    let mut new = format!("{letter}'");
    while used.contains(&new) {
        new.push('\'');
    }
    used.insert(new.clone());
    new
}
