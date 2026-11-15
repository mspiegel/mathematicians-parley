//! Formulas, relations, membership and quantifiers.

use super::*;

impl Writer<'_> {
    /// The node, a formula, written as a Lean proposition.
    pub fn formula(&self, node: &Node) -> Route<Printed> {
        // A letter that stands for a statement.
        if node.is_name()
            && self.letters.get(node.text.as_str()) == Some(&LetterType::Statement)
        {
            return Route::Built(Printed::letter(
                super::super::names::letter(&node.text),
                super::super::doc::LeanType::Prop,
            ));
        }
        // not (a = b) between numbers is written a ≠ b, as Mathlib writes it.
        if let ([inner], LOGICAL_NOT) = (node.children.as_slice(), node.notation()) {
            if inner.notation() == EQUALITY
                && inner.children.iter().all(|c| self.is_number(c))
                && self.wide_in_slot(inner).is_none()
            {
                return self.relation(inner, true);
            }
        }
        if let Some(said) = self.slot_witness(node) {
            return said;
        }
        if &*node.notation_name() == "tends-to" {
            return self.tends_to(node);
        }
        if &*node.notation_name() == "function-limit" {
            return self.function_limit(node);
        }
        if &*node.notation_name() == "continuous" {
            return self.continuous(node, "ContinuousOn");
        }
        if &*node.notation_name() == "differentiable" {
            return self.differentiable(node);
        }
        // D is open: `IsOpen D`, of a set of reals.
        if let ("open", [set]) = (&*node.notation_name(), node.children.as_slice()) {
            return self.numbers_at(set, Num::Real).map(|s| {
                Printed::applied(
                    "IsOpen",
                    super::super::doc::Source::Mathlib,
                    vec![s],
                    LeanType::Prop,
                )
            });
        }
        // There is a bijection from A to B: some map of the one's members to
        // the other's that is one-to-one from A onto B, `Set.BijOn g A B`.
        if let ("bijection", [a, b]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            return self.bijection(a, b);
        }
        // f is a function on a set: a Lean function is one on every set of
        // the type it takes, its values off the set none of the page's. Of
        // numbers, a set of numbers it takes; of things, a set of things.
        if let ("function-on", [f, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let takes = match (self.letters.get(f.text.as_str()), self.set_members(set))
            {
                (
                    Some(LetterType::Function { from, .. }),
                    Some(Members::Numbers(n)),
                ) => n <= *from,
                (Some(LetterType::Map { from, .. }), Some(m)) => *from == m,
                _ => false,
            };
            return match takes {
                true => Route::Built(Printed::truth()),
                false => Route::no(format!(
                    "{} is a function on a set of no type it takes",
                    f.text
                )),
            };
        }
        // P(t), the property P of t: `P t`.
        if let ("holds-of", [p, t]) = (&*node.notation_name(), node.children.as_slice())
        {
            let Some(LetterType::Property(members)) = self.letters.get(p.text.as_str())
            else {
                return Route::no(format!(
                    "{} holds of a term, and is no property",
                    p.text
                ));
            };
            let property = LetterType::Property(members.clone()).lean_type();
            return self.element_term(t, members).map(|t| Printed {
                kind: super::super::doc::TermKind::App {
                    head: Box::new(Printed::letter(
                        super::super::names::letter(&p.text),
                        property,
                    )),
                    args: vec![super::super::doc::Arg::Explicit(t)],
                    explicit: false,
                },
                ty: Some(LeanType::Prop),
            });
        }
        // there is a ∈ X, with nothing said of a: set.mm's "there is" over a
        // true body, `∃ a ∈ X, True`.
        if let ("there-is-some", [letter, set]) =
            (&*node.notation_name(), node.children.as_slice())
        {
            let Some(members) = self.set_members(set) else {
                return Route::no("there is some member of a set with no Lean type");
            };
            let s = match self.set_term(set) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = super::super::names::letter(&letter.text);
            let ty = members.letter().lean_type();
            let guard =
                match relation_of("∈", Printed::letter(name.clone(), ty.clone()), s) {
                    Route::Built(g) => g,
                    Route::Declined(d) => return Route::Declined(d),
                };
            return Route::Built(Printed::of(
                super::super::doc::TermKind::Quantified {
                    quant: super::super::doc::Quant::Exists,
                    letter: name,
                    letter_ty: ty,
                    guard: Some(Box::new(guard)),
                    body: Box::new(Printed::truth()),
                    bounded: true,
                },
                LeanType::Prop,
            ));
        }
        // A relation between sets, A ⊆ B or A = B.
        if &*node.notation_name() == "subset" {
            if let Some(r) = self.set_relation(node, "⊆") {
                return r;
            }
        }
        if node.notation() == EQUALITY {
            if let Some(r) = self.set_relation(node, "=") {
                return r;
            }
        }
        // What a map between sets is, f : A → B or f : A → B is one-to-one.
        if let Some(r) = self.map_claim(node) {
            return r;
        }
        // A count of a set, |A| = 2 or 1 ≤ |A|, in ℕ∞; and A is finite.
        if matches!(node.notation(), EQUALITY | ORDER) {
            if let Some(r) = self.count_relation(node) {
                return r;
            }
        }
        if let Some(r) = self.finite(node) {
            return r;
        }
        if let Some(r) = self.subgroup_claim(node) {
            return r;
        }
        if let Some(r) = self.polynomial_claim(node) {
            return r;
        }
        match node.notation() {
            EQUALITY | ORDER if node.children.len() == 2 => self.relation(node, false),
            MEMBERSHIP => self.membership(node),
            // f : A → B, which Lean's types give where f takes and gives
            // those.
            crate::notations::FUNCTION_TYPE => {
                let [f, from, to] = node.children.as_slice() else {
                    return Route::no("a function type of other than three parts");
                };
                // Between sets of numbers, g : D → ℝ: that g maps the one
                // into the other, at the function's own types.
                let Some((takes, gives)) = function_systems(from, to) else {
                    let Route::Built((own_from, own_to)) = self.function_type(f) else {
                        return Route::no(
                            "a function type between sets that are no number system",
                        );
                    };
                    return match (
                        self.numbers_at(from, own_from),
                        self.numbers_at(to, own_to),
                    ) {
                        (Route::Built(a), Route::Built(b)) => {
                            Route::Built(Printed::applied(
                                "Set.MapsTo",
                                super::super::doc::Source::Mathlib,
                                vec![self.function_printed(f), a, b],
                                LeanType::Prop,
                            ))
                        }
                        (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                            Route::Declined(d)
                        }
                    };
                };
                // Between number systems, by f's type, where it takes all
                // the domain's numbers and gives numbers of the codomain:
                // F : ℕ₀ → ℝ of F from ℤ into ℤ.
                match self.function_type(f) {
                    Route::Built((own_from, own_to))
                        if takes <= own_from && own_to <= gives =>
                    {
                        Route::Built(Printed::truth())
                    }
                    Route::Built(_) => {
                        Route::no("a function type other than the function's own")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            THERE_IS | FOR_ALL => self.quantified(node),
            crate::notations::COMMA_CONJUNCTION => {
                let mut parts = Vec::new();
                for (i, c) in node.children.iter().enumerate() {
                    match self.knowing(&node.children[..i]).formula(c) {
                        Route::Built(p) => parts.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                match joined(super::super::doc::Op::AND, parts, 36) {
                    Some(all) => Route::Built(all),
                    None => Route::no("a conjunction of no parts"),
                }
            }
            _ => {
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                if template.yields != Slot::Prop {
                    return Route::no(format!(
                        "{} is a number, not a formula",
                        node.notation_name()
                    ));
                }
                let alpha = match self.alpha_of(node, template) {
                    Route::Built(a) => a,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match self.holes(node, template, alpha) {
                    Route::Built(children) => {
                        fill(template, &children).map(|t| t.typed(LeanType::Prop))
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
        }
    }

    /// A formula that puts a term Lean does not compute as a whole number
    /// in a slot for one: "2^p − 1 divides 2^(p − 1)" of a power that is a
    /// rational in Lean, "2^(p − 1)·(2^p − 1) is perfect", gcd(2^(p − 1), b)
    /// = 1. The term is some whole number m, and the formula is said of m:
    /// `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) ∧ 2 ^ p − 1 ∣ m`. set.mm writes the
    /// term as it stands, and its divides, σ and gcd hold of whole numbers
    /// only, so its formula holds exactly where this one does; the term
    /// keeps its one form (`GOALS.md` decision 20). None where no such slot
    /// holds such a term, or none whose letters are all the formula's own.
    pub(super) fn slot_witness(&self, node: &Node) -> Option<Route<Printed>> {
        let (term, whole) = self.wide_in_slot(node)?;
        let at = match self.carrier(&term) {
            Route::Built(n) => n,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let value = match self.number_fixed(&term, at) {
            Route::Built(v) => v,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let m = witness_letter(node);
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(m.clone(), LetterType::Number(whole));
        let named = Node::name(crate::formula::Sort::of("number"), &m);
        let body = match inner.formula(&put_for(node, &term, &named)) {
            Route::Built(b) => b,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        let named = Printed::cast(
            Printed::letter(m.clone(), LeanType::Num(whole)),
            self.num_type(at),
        );
        let said = match relation_of("=", named, value) {
            Route::Built(r) => r,
            Route::Declined(d) => return Some(Route::Declined(d)),
        };
        Some(Route::Built(Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: super::super::doc::Quant::Exists,
                letter: m,
                letter_ty: LeanType::Num(whole),
                guard: Some(Box::new(said)),
                body: Box::new(body),
                bounded: false,
            },
            LeanType::Prop,
        )))
    }

    /// The first term the formula puts in a slot for a whole number that
    /// Lean does not compute as one, with the slot's type, ℤ or ℕ: an
    /// argument of divides, gcd or σ of a type wider than ℤ, or one of ℕ
    /// that is no natural number. Only a term whose letters are all free
    /// in the formula, so that the witness may stand outside it; and none
    /// inside a connective or a quantifier, whose own parts are formulas
    /// said apart. None where there is none.
    pub(in crate::lean) fn wide_in_slot(&self, node: &Node) -> Option<(Node, Num)> {
        use crate::notations::{BICONDITIONAL, CONDITIONAL, DISJUNCTION, IMPLICATION};
        let joins = self.is_and(node)
            || matches!(
                node.notation(),
                DISJUNCTION
                    | IMPLICATION
                    | CONDITIONAL
                    | BICONDITIONAL
                    | LOGICAL_NOT
                    | FOR_ALL
                    | THERE_IS
            );
        if joins {
            return None;
        }
        node.walk().into_iter().find_map(|n| self.wide_arg(&n))
    }

    /// `wide_in_slot` of one node's own arguments. A power's exponent is no
    /// such slot: one that is no natural number makes the power Lean's
    /// integer power (`Writer::integer_power`).
    pub(in crate::lean) fn wide_arg(&self, n: &Node) -> Option<(Node, Num)> {
        if n.notation() == crate::notations::POWER {
            return None;
        }
        let template = self.template(n).built()?;
        let args = self.args(n);
        template.holes.iter().zip(args).find_map(|(slot, arg)| {
            let whole = match slot {
                Slot::Fixed(w @ (Num::Nat | Num::Int)) => *w,
                _ => return None,
            };
            // A library function the term applies, the gcd of a/gcd(a, b),
            // is no letter the witness could capture.
            let free = arg.names().iter().all(|name| {
                self.letters.contains_key(name.as_str())
                    || self.templates.function(name).is_some()
            });
            // A term said once in ℕ₀ is written `t.toNat` there (`number`).
            let wide = match whole {
                Num::Nat => !self.natural(arg) && !self.said_whole(arg),
                _ => self.carrier(arg).built().is_some_and(|c| c > Num::Int),
            };
            (self.is_number(arg) && free && wide).then(|| (arg.clone(), whole))
        })
    }

    /// The type a formula's `α` holes are computed in: the least that holds
    /// each of them.
    pub(super) fn alpha_of(&self, node: &Node, template: &Template) -> Route<Num> {
        let mut out = Num::Int;
        for (child, slot) in self.args(node).iter().zip(&template.holes) {
            if let Slot::Alpha(floor) = slot {
                out = out.max(*floor);
                match self.carrier(child) {
                    Route::Built(n) => out = out.max(n),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        }
        Route::Built(out)
    }

    /// `a = b`, `a < b` and the rest between two numbers, both sides in the
    /// least type that holds them; a side of numerals alone is told its
    /// type where the other does not fix it. `negated` writes an equation
    /// as `≠`.
    pub(super) fn relation(&self, node: &Node, negated: bool) -> Route<Printed> {
        self.relation_from(node, negated, Num::Int)
    }

    /// A relation of numerals alone, `5 = 0`, written in the type `floor`
    /// at least: the type of the lines it is reached from.
    pub fn closed_formula(&self, node: &Node, floor: Num) -> Route<Printed> {
        // A count, |∅| = 0, is in ℕ∞ whatever the lines around it; sets,
        // {1, …, 0} = ∅, are of the types their members are.
        if self.counts(node)
            || (matches!(node.notation(), EQUALITY | ORDER)
                && self.said_in_extended(node))
        {
            return self.formula(node);
        }
        if let [left, right] = node.children.as_slice() {
            let of_sets = matches!(node.notation(), EQUALITY | ORDER)
                && (self.set_members(left).is_some()
                    || self.set_members(right).is_some());
            if of_sets {
                return self.formula(node);
            }
        }
        if let ([inner], LOGICAL_NOT) = (node.children.as_slice(), node.notation()) {
            if inner.notation() == EQUALITY {
                return self.relation_from(inner, true, floor);
            }
            if inner.notation() == ORDER {
                return self.relation_from(inner, false, floor).map(|r| {
                    Printed::of(
                        super::super::doc::TermKind::Not(Box::new(r)),
                        super::super::doc::LeanType::Prop,
                    )
                });
            }
        }
        match node.notation() {
            EQUALITY | ORDER => self.relation_from(node, false, floor),
            _ => self.formula(node),
        }
    }

    pub(super) fn relation_from(
        &self,
        node: &Node,
        negated: bool,
        floor: Num,
    ) -> Route<Printed> {
        let [left, right] = node.children.as_slice() else {
            return Route::no("a relation of other than two sides");
        };
        // |S| = |∅|: ∅ is a set of what S holds.
        if self.empty_of.is_none() {
            if let Some(m) = self
                .counted_beside_empty(left, right)
                .or_else(|| self.counted_beside_empty(right, left))
            {
                let mut w = self.with_letters(self.letters.clone());
                w.empty_of = Some(m);
                return w.relation_from(node, negated, floor);
            }
        }
        if !self.is_number(left) || !self.is_number(right) {
            return Route::no(format!(
                "{} between terms that are not numbers",
                node.notation_name()
            ));
        }
        let at = match (self.carrier(left), self.carrier(right)) {
            (Route::Built(a), Route::Built(b)) => a.max(b).max(floor),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        // ℂ has no order: x < √y of a y not shown at least 0, whose square
        // root is the principal one in ℂ, is not written.
        if node.notation() == ORDER && at == Num::Complex {
            return Route::no("an order between complex numbers");
        }
        let mut l = match self.number(left, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let r = match self.number(right, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        if !self.pinned(left) && !self.pinned(right) {
            l = self.cast(&l, at);
        }
        let op = match &*node.spelling().text() {
            "=" if node.spelling() == EQUALS && negated => "≠",
            "=" if node.spelling() == EQUALS => "=",
            "<" => "<",
            ">" => ">",
            "≤" => "≤",
            "≥" => "≥",
            other => return Route::no(format!("the relation {other}")),
        };
        relation_of(op, l, r)
    }

    /// `x ∈ S`. In a number system, the membership is what it says of x in
    /// Lean: nothing more than x's type where that already holds it,
    /// `0 < n` for the page's ℕ, which starts at 1, and otherwise that some
    /// member of the system is x. In a range, x lies between its ends.
    pub(super) fn membership(&self, node: &Node) -> Route<Printed> {
        let [x, set] = node.children.as_slice() else {
            return Route::no("a membership of other than two sides");
        };
        // D ∈ 𝒫ℝ of a set of numbers is D ⊆ ℝ.
        if let ("powerset", [whole]) = (&*set.notation_name(), set.children.as_slice())
        {
            if let Some(Members::Numbers(_)) = self.set_members(whole) {
                let subset = node.with_children(vec![x.clone(), whole.clone()]);
                if let Some(r) = self.set_relation(&subset, "⊆") {
                    return r;
                }
            }
        }
        if set.notation() == NUMBER_SYSTEMS {
            if let Some(r) = self.count_in_system(x, set) {
                return r;
            }
            return self.in_system(x, set);
        }
        if &*set.notation_name() == "functions-from" {
            return self.in_functions_from(x, set);
        }
        // x ∈ {a, b, c} of numbers: a membership of Lean's sets, in the
        // least type that holds x and every member, so that x is written
        // once, as the page writes it. Ahead of other sets, whose type is
        // their members' alone.
        if matches!(
            &*set.notation_name(),
            "singleton" | "listed-two" | "listed-three" | "listed-four"
        ) && self.is_number(x)
        {
            let mut at = Num::Int;
            for n in std::iter::once(x).chain(&set.children) {
                match self.carrier(n) {
                    Route::Built(c) => at = at.max(c),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let mut members = Vec::new();
            for member in &set.children {
                match self.number_fixed(member, at) {
                    Route::Built(p) => members.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let x = match self.number_fixed(x, at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let of = LeanType::Set(Box::new(self.num_type(at)));
            return relation_of(
                "∈",
                x,
                Printed::cast(listed_set(members, of.clone()), of),
            );
        }
        if let Some(m) = self.set_membership(x, set) {
            return m;
        }
        if set.notation() == INTEGER_RANGE {
            let [from, to] = set.children.as_slice() else {
                return Route::no("a range of other than two ends");
            };
            // A member of a wider type, f(a) of a real f: an integer that is
            // it, in the range, as `t ∈ ℤ` of a wider t is said, `∃ m : ℤ,
            // (m : ℝ) = f a ∧ m ∈ Finset.Icc 0 (p - 1)`.
            if let Route::Built(own) = self.carrier(x) {
                if own > Num::Int {
                    let ends = (
                        self.number_fixed(from, Num::Int),
                        self.number_fixed(to, Num::Int),
                    );
                    let (Route::Built(low), Route::Built(high)) = ends else {
                        return Route::no("a range whose ends are not integers");
                    };
                    let m = witness_letter(x);
                    let value = match self.number(x, own) {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let int = LeanType::Num(Num::Int);
                    let letter = Printed::letter(m.clone(), int.clone());
                    let is = relation_of(
                        "=",
                        Printed::cast(letter.clone(), self.num_type(own)),
                        value,
                    );
                    let within = relation_of("∈", letter, icc(low, high));
                    let (Route::Built(is), Route::Built(within)) = (is, within) else {
                        return Route::no("a range member of a wider type not written");
                    };
                    return match conjunction(is, within) {
                        Route::Built(said) => {
                            Route::Built(witnessed(m, int, None, said))
                        }
                        Route::Declined(d) => Route::Declined(d),
                    };
                }
            }
            // A range whose ends are no integers as Lean computes them, 6/3,
            // is said by the order of its integer member between them, in
            // the type that holds all three.
            let wide = [x, from, to]
                .iter()
                .any(|n| matches!(self.carrier(n), Route::Built(c) if c > Num::Int));
            if wide {
                let mut at = Num::Int;
                for n in [x, from, to] {
                    match self.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                let mut out = Vec::new();
                for n in [from, x, to] {
                    match self.number(n, at) {
                        Route::Built(p) => out.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                if !self.pinned(x) && !self.pinned(from) {
                    out[0] = self.cast(&out[0], at);
                }
                let [low, x, high] = [out[0].clone(), out[1].clone(), out[2].clone()];
                let (above, below) =
                    match (relation_of("≤", low, x.clone()), relation_of("≤", x, high))
                    {
                        (Route::Built(a), Route::Built(b)) => (a, b),
                        (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                            return Route::Declined(d)
                        }
                    };
                return conjunction(above, below);
            }
            // Each written as an integer, a numeral too, so that a range of
            // numerals alone is not read in ℕ.
            let parts = [
                self.number_fixed(x, Num::Int),
                self.number_fixed(from, Num::Int),
                self.number_fixed(to, Num::Int),
            ];
            let mut out = Vec::new();
            for p in parts {
                match p {
                    Route::Built(p) => out.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let [x, from, to] = [out[0].clone(), out[1].clone(), out[2].clone()];
            return relation_of("∈", x, icc(from, to));
        }
        Route::no(format!("a membership of {}", set.notation_name()))
    }

    /// `x ∈ ℤ` and the like.
    pub(super) fn in_system(&self, x: &Node, set: &Node) -> Route<Printed> {
        let system = match system_of(set) {
            Some(s) => s,
            None => return Route::no(format!("the number system {}", set.text)),
        };
        let own = match self.carrier(x) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let natural_letter = x.is_name()
            && matches!(
                self.letters.get(x.text.as_str()),
                Some(LetterType::Number(Num::Nat))
            );
        let held = if natural_letter { Num::Nat } else { own };
        match system {
            System::Positive if held <= Num::Int => {
                let at = if natural_letter { Num::Nat } else { Num::Int };
                let zero = self.zero_at(x, at);
                let x = match self.number(x, at) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                relation_of("<", zero, x)
            }
            System::NonNegative if held <= Num::Int => {
                if natural_letter {
                    return Route::Built(Printed::truth());
                }
                let zero = self.zero_at(x, Num::Int);
                let x = match self.number(x, Num::Int) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                relation_of("≤", zero, x)
            }
            System::Type(n) if held <= n => Route::Built(Printed::truth()),
            System::Type(n) => {
                let m = witness_letter(x);
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let named = Printed::cast(
                    Printed::letter(m.clone(), self.num_type(n)),
                    self.num_type(own),
                );
                let said = match relation_of("=", named, x) {
                    Route::Built(r) => r,
                    Route::Declined(d) => return Route::Declined(d),
                };
                Route::Built(witnessed(m, self.num_type(n), None, said))
            }
            System::Positive | System::NonNegative => {
                let m = witness_letter(x);
                let x = match self.number(x, own) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let order = if system == System::Positive {
                    "<"
                } else {
                    "≤"
                };
                let int = LeanType::Num(Num::Int);
                let letter = Printed::letter(m.clone(), int.clone());
                let bound = relation_of(
                    order,
                    Printed::numeral("0", int.clone()),
                    letter.clone(),
                );
                let said =
                    relation_of("=", Printed::cast(letter, self.num_type(own)), x);
                match (bound, said) {
                    (Route::Built(b), Route::Built(s)) => {
                        Route::Built(witnessed(m, int, Some(b), s))
                    }
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        Route::Declined(d)
                    }
                }
            }
        }
    }

    /// `there is k ∈ S with P` and `for all k ∈ S, P`, the letter typed by
    /// the set it ranges over.
    pub(super) fn quantified(&self, node: &Node) -> Route<Printed> {
        let [letter, set, body] = node.children.as_slice() else {
            return Route::no("a quantifier of other than three parts");
        };
        if !letter.is_name() {
            return Route::no("a quantifier over a term that is no letter");
        }
        let exists = node.notation() == THERE_IS;
        if let Some(q) = self.quantified_over_set(letter, set, body, exists) {
            return q;
        }
        if let Some(q) = self.quantified_over_polynomials(letter, set, body, exists) {
            return q;
        }
        if &*set.notation_name() == "functions-from" {
            return self.quantified_over_functions(letter, set, body, exists);
        }
        let name = super::super::names::letter(&letter.text);
        let int = super::super::doc::LeanType::Num(Num::Int);
        let named = Printed::letter(name.clone(), int.clone());
        let zero = Printed::numeral("0", int.clone());
        let (system, guard) = if set.notation() == NUMBER_SYSTEMS {
            match system_of(set) {
                Some(System::Type(n)) => (System::Type(n), None),
                Some(System::Positive) => {
                    (System::Positive, Some(relation_of("<", zero, named)))
                }
                Some(System::NonNegative) => {
                    (System::NonNegative, Some(relation_of("≤", zero, named)))
                }
                None => return Route::no(format!("the number system {}", set.text)),
            }
        } else if set.notation() == INTEGER_RANGE {
            let [from, to] = set.children.as_slice() else {
                return Route::no("a range of other than two ends");
            };
            let ends = (self.number(from, Num::Int), self.number(to, Num::Int));
            let (Route::Built(from), Route::Built(to)) = ends else {
                return Route::no("a range whose ends are not integers");
            };
            (
                range_letter_system(set),
                Some(relation_of("∈", named, icc(from, to))),
            )
        } else {
            return Route::no(format!("a quantifier over {}", set.notation_name()));
        };
        let guard = match guard {
            Some(Route::Built(g)) => Some(Box::new(g)),
            Some(Route::Declined(d)) => return Route::Declined(d),
            None => None,
        };
        let ty = letter_type(system);
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&letter.text, system);
        // The letter is bounded by the set it runs over, x ≥ 0 of "for all
        // x ∈ ℕ₀", as a letter the header lets is, for a square root of it.
        inner.bounds = bounds::inside_quantifier(self, letter, set);
        let body = match inner.formula(body) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A body the letter's type already makes true says nothing.
        if body.is_truth() {
            return Route::Built(Printed::truth());
        }
        Route::Built(Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: match exists {
                    true => super::super::doc::Quant::Exists,
                    false => super::super::doc::Quant::ForAll,
                },
                letter: name,
                letter_ty: self.num_type(ty),
                guard,
                body: Box::new(body),
                bounded: false,
            },
            super::super::doc::LeanType::Prop,
        ))
    }

    /// The type of a function from one set to another: between sets of
    /// numbers, a function of the numbers' types, g : {1, …, j} → ℕ a
    /// function from ℤ to ℤ; otherwise a map between what the sets hold.
    /// None where either set has no Lean type.
    pub fn function_between(&self, from: &Node, to: &Node) -> Option<LetterType> {
        match (self.set_members(from)?, self.set_members(to)?) {
            (Members::Numbers(m), Members::Numbers(n)) => {
                Some(LetterType::Function { from: m, to: n })
            }
            (a, b) => Some(LetterType::Map { from: a, to: b }),
        }
    }

    /// "there is f : A → B with …" and "for all f : A → B, …": f a Lean
    /// function of the types the sets' members are, and that it maps A
    /// into B a fact beside it, `∃ f : ℤ → ℤ, Set.MapsTo f A B ∧ …`.
    /// The functions from X to Y, `set`, as Lean takes them: the type of
    /// such a function and its two sets as Lean writes them.
    pub(super) fn functions_from(&self, set: &Node) -> Route<FunctionsFrom> {
        let [from, to] = set.children.as_slice() else {
            return Route::no("the functions between other than two sets");
        };
        let Some(ty) = self.function_between(from, to) else {
            return Route::no("the functions between sets with no Lean type");
        };
        let sides = match &ty {
            LetterType::Function { from: m, to: n } => {
                (self.numbers_at(from, *m), self.numbers_at(to, *n))
            }
            _ => (self.set_term(from), self.set_term(to)),
        };
        match sides {
            (Route::Built(from), Route::Built(to)) => {
                Route::Built(FunctionsFrom { ty, from, to })
            }
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// `f ∈ (the functions from X to Y)`, as Lean says it of f, which a
    /// "for all f : X → Y" asks of its letter: `Set.MapsTo f X Y`.
    pub(super) fn in_functions_from(&self, f: &Node, set: &Node) -> Route<Printed> {
        let sets = match self.functions_from(set) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        if !f.is_name() {
            return Route::no("a membership of the functions of other than a letter");
        }
        let ty = self
            .letters
            .get(f.text.as_str())
            .unwrap_or(&sets.ty)
            .lean_type();
        let letter = Printed::letter(super::super::names::letter(&f.text), ty);
        Route::Built(maps_to(letter, sets.from, sets.to))
    }

    pub(super) fn quantified_over_functions(
        &self,
        letter: &Node,
        set: &Node,
        body: &Node,
        exists: bool,
    ) -> Route<Printed> {
        let FunctionsFrom { ty, from, to } = match self.functions_from(set) {
            Route::Built(f) => f,
            Route::Declined(d) => return Route::Declined(d),
        };
        let name = super::super::names::letter(&letter.text);
        let lean_type = ty.lean_type();
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(letter.text.to_string(), ty);
        let body = match inner.formula(body) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        let maps = maps_to(Printed::letter(name.clone(), lean_type.clone()), from, to);
        Route::Built(Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: match exists {
                    true => super::super::doc::Quant::Exists,
                    false => super::super::doc::Quant::ForAll,
                },
                letter: name,
                letter_ty: lean_type,
                guard: Some(Box::new(maps)),
                body: Box::new(body),
                bounded: false,
            },
            super::super::doc::LeanType::Prop,
        ))
    }
}
