//! Sets in Lean: a set of the things a theorem's sets hold is `Set α`, and
//! the page's operations on sets are Mathlib's on `Set`.
//!
//! The members of every set a theorem leaves open are one type `α`, as
//! set.mm's sets all hold sets; 𝒫A's members are `Set α`. A function from
//! one such set to another is a function `α → α` with the fact that it
//! maps the one into the other beside it (`statement`).

use super::expr::{LetterType, Members, Printed, Writer, MAX};
use crate::formula::Node;
use crate::outcome::Route;

/// The Lean type of a letter of this sort where it is a set, a member of
/// one or a map between sets; None for any other sort.
pub fn set_letter_type(sort: &crate::formula::Sort) -> Option<LetterType> {
    use crate::formula::Whole;
    match sort.full()? {
        Whole::Set(_) => Members::of_set(sort.full()?).map(LetterType::Set),
        Whole::Open => Some(LetterType::Member(Members::Things)),
        Whole::Function(from, to) => Some(LetterType::Map {
            from: Members::of(from)?,
            to: Members::of(to)?,
        }),
        _ => None,
    }
}

impl Writer<'_> {
    /// What the members of a set term are; None for a term that is no set
    /// this writer has a type for.
    pub fn members_of(&self, node: &Node) -> Option<Members> {
        if node.is_name() {
            return match self.letters.get(node.text.as_str()) {
                Some(LetterType::Set(m)) => Some(m.clone()),
                // A member of a set of sets, the t of t ∈ 𝒫A, is a set.
                Some(LetterType::Member(Members::Sets(m))) => Some((**m).clone()),
                _ => None,
            };
        }
        match &*node.notation_name() {
            "set-operations" | "set-builder" => {
                let first = match &*node.notation_name() {
                    "set-builder" => node.children.get(1)?,
                    _ => node.children.first()?,
                };
                self.members_of(first)
                    .or_else(|| node.children.get(1).and_then(|c| self.members_of(c)))
            }
            "powerset" => self
                .members_of(node.children.first()?)
                .map(|m| Members::Sets(Box::new(m))),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => {
                node.children.iter().find_map(|c| self.member_kind(c))
            }
            "image" => match self.letters.get(node.children.first()?.text.as_str()) {
                Some(LetterType::Map { to, .. }) => Some(to.clone()),
                _ => None,
            },
            _ => None,
        }
    }

    /// What kind of member a term is: a letter of a set's members, or a set
    /// itself, a member of a set of sets.
    fn member_kind(&self, node: &Node) -> Option<Members> {
        if node.is_name() {
            if let Some(LetterType::Member(m)) = self.letters.get(node.text.as_str()) {
                return Some(m.clone());
            }
        }
        if let Some(LetterType::Map { to, .. }) = node
            .children
            .first()
            .and_then(|f| self.letters.get(f.text.as_str()))
        {
            if &*node.notation_name() == "application" {
                return Some(to.clone());
            }
        }
        self.members_of(node).map(|m| Members::Sets(Box::new(m)))
    }

    /// A set, a member of one, or a map, as Lean writes it.
    pub fn set_term(&self, node: &Node) -> Route<Printed> {
        if node.is_name() {
            return match self.letters.get(node.text.as_str()) {
                Some(
                    LetterType::Set(_) | LetterType::Member(_) | LetterType::Map { .. },
                ) => Route::Built(Printed::atom(super::names::letter(&node.text))),
                _ => Route::no(format!("{} is no set, member or map", node.text)),
            };
        }
        let parts = |want: usize| self.set_parts(node, want);
        match &*node.notation_name() {
            "set-operations" => {
                let p = match parts(2) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Lean's ∪ binds at 65 and ∩ and \ at 70, and reads no ∩
                // beside a \ unbracketed, so an operation inside another is
                // bracketed whatever it is.
                let (op, prec) = match &*node.spelling().text() {
                    "∪" => ("∪", 65),
                    "∩" => ("∩", 70),
                    "∖" => ("\\", 70),
                    other => return Route::no(format!("the set operation {other}")),
                };
                Route::Built(Printed {
                    text: format!("{} {op} {}", p[0].at(prec + 1), p[1].at(prec + 1)),
                    prec,
                })
            }
            "powerset" => match parts(1) {
                Route::Built(p) => Route::Built(Printed {
                    text: format!("𝒫 {}", p[0].at(MAX)),
                    prec: 100,
                }),
                Route::Declined(d) => Route::Declined(d),
            },
            "empty-set" => Route::Built(Printed::atom("∅")),
            "singleton" | "listed-two" | "listed-three" | "listed-four" => {
                // Ascribed its type, which Lean cannot take from a member
                // alone: `{u, w}` of things of α is `({u, w} : Set α)`.
                let ty = node
                    .children
                    .iter()
                    .find_map(|c| self.member_kind(c))
                    .map(|m| format!("Set {}", super::expr::bracketed(&m.lean())));
                match parts(node.children.len()) {
                    Route::Built(p) => {
                        let listed: Vec<String> =
                            p.into_iter().map(|x| x.text).collect();
                        let set = format!("{{{}}}", listed.join(", "));
                        Route::Built(Printed::atom(match ty {
                            Some(t) => format!("({set} : {t})"),
                            None => set,
                        }))
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            "image" => match parts(2) {
                Route::Built(p) => Route::Built(Printed {
                    text: format!("{} '' {}", p[0].at(MAX), p[1].at(MAX)),
                    prec: 80,
                }),
                Route::Declined(d) => Route::Declined(d),
            },
            "set-builder" => self.set_builder(node),
            "application" => self.map_applied(node),
            other => Route::no(format!("{other} as a set")),
        }
    }

    /// Each part of a set term, written as a set's, where it has `want`.
    fn set_parts(&self, node: &Node, want: usize) -> Route<Vec<Printed>> {
        if node.children.len() != want {
            return Route::no(format!(
                "{} of {} parts",
                node.notation_name(),
                node.children.len()
            ));
        }
        let mut out = Vec::new();
        for c in &node.children {
            match self.set_term(c) {
                Route::Built(p) => out.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(out)
    }

    /// {t ∈ X : P(t)}, `{t ∈ X | P t}`: the letter a member of X's, and
    /// the condition read with it.
    fn set_builder(&self, node: &Node) -> Route<Printed> {
        let [letter, set, body] = node.children.as_slice() else {
            return Route::no("a set-builder of other than three parts");
        };
        let Some(members) = self.members_of(set) else {
            return Route::no("a set-builder over a set with no Lean type");
        };
        let domain = match self.set_term(set) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Member(members));
        let condition = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(Printed::atom(format!(
            "{{{} ∈ {} | {}}}",
            super::names::letter(&letter.text),
            domain.text,
            condition.text
        )))
    }

    /// f(x) of a map: its value, a member of the set it maps into.
    fn map_applied(&self, node: &Node) -> Route<Printed> {
        let [f, x] = node.children.as_slice() else {
            return Route::no("a map applied to other than one argument");
        };
        if !matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Map { .. })
        ) {
            return Route::no(format!("{} applied, which is no map", f.text));
        }
        match self.set_term(x) {
            Route::Built(p) => Route::Built(Printed {
                text: format!("{} {}", super::names::letter(&f.text), p.at(MAX)),
                prec: 1023,
            }),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// What a map between sets is: `f : A → B` is `Set.MapsTo f A B`, and
    /// one-to-one and onto add `Set.InjOn f A` and `Set.SurjOn f A B`, each
    /// a part of a conjunction a hypothesis is taken apart by. None where
    /// the node says none of these of a map letter.
    pub fn map_claim(&self, node: &Node) -> Option<Route<Printed>> {
        let extra: &[&str] = match &*node.notation_name() {
            "function-type" => &[],
            "one-to-one" => &["Set.InjOn _f _A"],
            "onto" => &["Set.SurjOn _f _A _B"],
            "one-to-one-onto" => &["Set.InjOn _f _A", "Set.SurjOn _f _A _B"],
            _ => return None,
        };
        let [f, from, to] = node.children.as_slice() else {
            return None;
        };
        if !matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Map { .. })
        ) {
            return None;
        }
        let (a, b) = match (self.set_term(from), self.set_term(to)) {
            (Route::Built(a), Route::Built(b)) => (a.at(MAX), b.at(MAX)),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Some(Route::Declined(d))
            }
        };
        let name = super::names::letter(&f.text);
        let parts: Vec<String> = std::iter::once("Set.MapsTo _f _A _B")
            .chain(extra.iter().copied())
            .map(|p| p.replace("_f", &name).replace("_A", &a).replace("_B", &b))
            .collect();
        let prec = if parts.len() == 1 {
            super::expr::APP
        } else {
            35
        };
        Some(Route::Built(Printed {
            text: parts.join(" ∧ "),
            prec,
        }))
    }

    /// x ∈ S of a set S this writer has a type for: `x ∈ S`.
    pub fn set_membership(&self, x: &Node, set: &Node) -> Option<Route<Printed>> {
        // ∅ holds nothing of any type, so x ∈ ∅ is of x's.
        let empty = &*set.notation_name() == "empty-set";
        let members = self
            .members_of(set)
            .or_else(|| empty.then(|| self.member_kind(x)).flatten())?;
        // ∅ is told its type, which nothing else in `t ∈ ∅` gives Lean.
        let set_text = match empty {
            true => Route::Built(Printed::atom(format!(
                "(∅ : Set {})",
                super::expr::bracketed(&members.lean())
            ))),
            false => self.set_term(set),
        };
        Some(match (self.set_term(x), set_text) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} ∈ {}", a.at(51), b.at(51)),
                prec: 50,
            }),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// A relation between two sets, A = B or A ⊆ B, or two members of one,
    /// x = u; None where neither side is a set or a member this writer has a
    /// type for.
    pub fn set_relation(&self, node: &Node, op: &str) -> Option<Route<Printed>> {
        let [a, b] = node.children.as_slice() else {
            return None;
        };
        self.members_of(a)
            .or_else(|| self.members_of(b))
            .or_else(|| self.member_kind(a))
            .or_else(|| self.member_kind(b))?;
        Some(match (self.set_term(a), self.set_term(b)) {
            (Route::Built(a), Route::Built(b)) => Route::Built(Printed {
                text: format!("{} {op} {}", a.at(51), b.at(51)),
                prec: 50,
            }),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        })
    }

    /// For all t ∈ S, or there is t ∈ S, of a set S: `∀ t ∈ S, …`, the letter
    /// a member of S's; None where S is no set this writer has a type for.
    pub fn quantified_over_set(
        &self,
        letter: &Node,
        set: &Node,
        body: &Node,
        exists: bool,
    ) -> Option<Route<Printed>> {
        let members = self.members_of(set)?;
        let domain = match self.set_term(set) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Member(members));
        let body = match inner.formula(body) {
            Route::Built(p) => p,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let quantifier = if exists { "∃" } else { "∀" };
        Some(Route::Built(Printed {
            text: format!(
                "{quantifier} {} ∈ {}, {}",
                super::names::letter(&letter.text),
                domain.at(51),
                body.text
            ),
            prec: 0,
        }))
    }
}
