//! Sums, series, integrals, limits and numbers.

use super::*;

impl Writer<'_> {
    /// Σ(k = a to b) t, `∑ k ∈ Finset.Icc a b, t`, and ∏ alike, its index ranging over
    /// the integers from a to b, and t computed in `at`. It is bracketed
    /// wherever it stands in more, since its body reaches as far right as
    /// it can.
    pub(super) fn sum(&self, node: &Node, at: Num) -> Route<Printed> {
        let s = match self.summed(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        // Over a range, the integers between its ends, `∑ k ∈ Finset.Icc a
        // b`; over a set, Mathlib's sum over the members of a finite set,
        // `∑ᶠ x ∈ S`, which is the page's where the set is finite.
        let product = is_product(node);
        let index = super::super::names::letter(&s.index.text);
        let Some(index_ty) = s.inner.letters.get(s.index.text.as_str()) else {
            return Route::no("a sum whose index has no type");
        };
        let index_ty = index_ty.lean_type();
        // (whether over a finite set, what it runs over, the precedence that
        // stands at)
        let (finite, set, need) = match s.over {
            Over::Range { from, to } => {
                match (
                    self.number_fixed(from, Num::Int),
                    self.number_fixed(to, Num::Int),
                ) {
                    (Route::Built(f), Route::Built(t)) => (false, icc(f, t), 0),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        return Route::Declined(d)
                    }
                }
            }
            // ∅ takes the index's type, which Lean cannot read from it.
            Over::Set(set) if &*set.notation_name() == "empty-set" => (
                true,
                empty_of_type(LeanType::Set(Box::new(index_ty.clone()))),
                0,
            ),
            Over::Set(set) => match self.set_term(set) {
                Route::Built(p) => (true, p, MAX),
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        let term = match s.inner.number(s.term, at) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The term is given its type: one built of numerals and naturals,
        // Σ(k = 1 to 3) 5 or 1/2^(j + 1), gives Lean nothing else to read
        // its type from, and Lean would take it in ℕ.
        let term = Printed::cast(term, self.num_type(at));
        Route::Built(Printed::of(
            super::super::doc::TermKind::Bound {
                form: super::super::doc::BoundForm::BigOp {
                    product,
                    finite,
                    set: Box::new(set),
                    need,
                },
                letter: index,
                letter_ty: index_ty,
                body: Box::new(term),
            },
            self.num_type(at),
        ))
    }

    /// Σ(k = a to ∞) t, the value of a series: the limit of its partial
    /// sums, `Filter.limUnder Filter.atTop (fun n : ℤ => ∑ k ∈ Finset.Icc a n, t)`,
    /// as set.mm and the series-sum item take it. Mathlib's `∑'` is 0 for a
    /// series that converges only conditionally, 1 − 1/3 + 1/5 − …, so it is
    /// not used. The partial sums run over a letter the series does not use.
    pub(super) fn series(&self, node: &Node, at: Num) -> Route<Printed> {
        let [index, from, term] = node.children.as_slice() else {
            return Route::no("a series of other than three parts");
        };
        if !index.is_name() {
            return Route::no("a series whose index is no letter");
        }
        if at != Num::Real {
            return Route::no("a series computed in other than ℝ");
        }
        let used: Vec<String> =
            node.walk().iter().map(|n| n.text.to_string()).collect();
        let Some(upper) = ["n", "m", "N", "M", "j"]
            .into_iter()
            .find(|l| !used.iter().any(|u| u == l))
        else {
            return Route::no(
                "a series using every letter its partial sums could run over",
            );
        };
        let mut inner = self.with_letters(self.letters.clone());
        let system = match crate::citing::index_system(from) {
            Some(crate::rules::System::N) => System::Positive,
            Some(crate::rules::System::N0) => System::NonNegative,
            _ => System::Type(Num::Int),
        };
        inner.introduce(&index.text, system);
        let (start, body) =
            match (self.number_fixed(from, Num::Int), inner.number(term, at)) {
                (Route::Built(s), Route::Built(b)) => (s, b),
                (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                    return Route::Declined(d)
                }
            };
        let body = Printed::cast(body, self.num_type(at));
        let int = LeanType::Num(Num::Int);
        let partial = Printed::of(
            super::super::doc::TermKind::Bound {
                form: super::super::doc::BoundForm::BigOp {
                    product: false,
                    finite: false,
                    set: Box::new(icc(start, Printed::letter(upper, int.clone()))),
                    need: 0,
                },
                letter: super::super::names::letter(&index.text),
                letter_ty: int.clone(),
                body: Box::new(body),
            },
            self.num_type(at),
        );
        let sums = Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: super::super::doc::Quant::Fun,
                letter: upper.to_string(),
                letter_ty: int.clone(),
                guard: None,
                body: Box::new(partial),
                bounded: false,
            },
            LeanType::Fun {
                from: Box::new(int),
                to: Box::new(self.num_type(at)),
            },
        );
        Route::Built(Printed::applied(
            "Filter.limUnder",
            super::super::doc::Source::Mathlib,
            vec![
                Printed::head("Filter.atTop", super::super::doc::Source::Mathlib),
                sums,
            ],
            self.num_type(at),
        ))
    }

    /// ∫(a to b) t dx, the integral from a to b, `∫ x in a..b, t`: Mathlib's
    /// interval integral, which runs from its first end to its second and is
    /// negated backwards, as set.mm's directed integral is. The letter is a
    /// real there, and the term is computed in ℝ.
    pub(super) fn integral(&self, node: &Node, at: Num) -> Route<Printed> {
        let [from, to, term, letter] = node.children.as_slice() else {
            return Route::no("an integral of other than four parts");
        };
        if !letter.is_name() {
            return Route::no("an integral whose letter is no letter");
        }
        if at != Num::Real {
            return Route::no("an integral computed in other than ℝ");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner
            .letters
            .insert(letter.text.to_string(), LetterType::Number(Num::Real));
        let (a, b, body) = match (
            self.number(from, Num::Real),
            self.number(to, Num::Real),
            inner.number(term, Num::Real),
        ) {
            (Route::Built(a), Route::Built(b), Route::Built(t)) => (a, b, t),
            (Route::Declined(d), _, _)
            | (_, Route::Declined(d), _)
            | (_, _, Route::Declined(d)) => return Route::Declined(d),
        };
        let real = LeanType::Num(Num::Real);
        let body = Printed::cast(body, real.clone());
        Route::Built(Printed::of(
            super::super::doc::TermKind::Bound {
                form: super::super::doc::BoundForm::Integral {
                    from: Box::new(a),
                    to: Box::new(b),
                },
                letter: super::super::names::letter(&letter.text),
                letter_ty: real.clone(),
                body: Box::new(body),
            },
            real,
        ))
    }

    /// x(n) → L as n → ∞: `Filter.Tendsto (fun n : ℤ => x n) Filter.atTop
    /// (nhds L)`, the letter an integer in ℕ as any page letter in ℕ is, and
    /// the term and its limit computed in the type that holds both. Where
    /// the integers start, no limit sees.
    pub(super) fn tends_to(&self, node: &Node) -> Route<Printed> {
        let [term, limit, letter] = node.children.as_slice() else {
            return Route::no("a limit of other than three parts");
        };
        if !letter.is_name() {
            return Route::no("a limit whose index is no letter");
        }
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&letter.text, System::Positive);
        // A limit is of real numbers, as the tends-to item states it: the
        // sequence and its limit are in ℝ at least, 1/n among them.
        let at = match (inner.carrier(term), self.carrier(limit)) {
            (Route::Built(a), Route::Built(b)) => a.max(b).max(Num::Real),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let (body, l) = match (inner.number(term, at), self.number(limit, at)) {
            (Route::Built(b), Route::Built(l)) => (b, l),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let mathlib = || super::super::doc::Source::Mathlib;
        // Filter.Tendsto (fun n : ℤ => x n) Filter.atTop (nhds L).
        let int = LeanType::Num(Num::Int);
        let sequence = Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: super::super::doc::Quant::Fun,
                letter: super::super::names::letter(&letter.text),
                letter_ty: int.clone(),
                guard: None,
                body: Box::new(Printed::cast(body, self.num_type(at))),
                bounded: false,
            },
            LeanType::Fun {
                from: Box::new(int),
                to: Box::new(self.num_type(at)),
            },
        );
        let near = Printed::applied("nhds", mathlib(), vec![l], LeanType::Prop);
        Route::Built(Printed::applied(
            "Filter.Tendsto",
            mathlib(),
            vec![sequence, Printed::head("Filter.atTop", mathlib()), near],
            LeanType::Prop,
        ))
    }

    /// f tends to L at c: `Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds
    /// L)`, the limit of f at c taken over its domain D with c left out, as
    /// the limit-at definition reads it (`domain_of`).
    pub(super) fn function_limit(&self, node: &Node) -> Route<Printed> {
        let [f, limit, at] = node.children.as_slice() else {
            return Route::no("a function limit of other than three parts");
        };
        if !f.is_name() {
            return Route::no("a limit of a function that has no name");
        }
        if !matches!(
            self.letters.get(f.text.as_str()),
            Some(LetterType::Function { to: Num::Real, .. })
        ) {
            return Route::left_out(format!("{} is no function into ℝ", f.text));
        }
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "a limit of {}, whose domain no line gives",
                f.text
            ));
        };
        let (l, c) = match (self.number(limit, Num::Real), self.number(at, Num::Real)) {
            (Route::Built(l), Route::Built(c)) => (l, c),
            (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                return Route::Declined(d)
            }
        };
        let mathlib = || super::super::doc::Source::Mathlib;
        // Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L).
        let Some(set) = domain.ty.clone() else {
            return Route::no("a limit over a domain with no Lean type");
        };
        let without = match relation_of(
            "\\",
            as_argument(domain),
            listed_set(vec![c.clone()], set),
        ) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        let within =
            Printed::applied("nhdsWithin", mathlib(), vec![c, without], LeanType::Prop);
        let near = Printed::applied("nhds", mathlib(), vec![l], LeanType::Prop);
        Route::Built(Printed::applied(
            "Filter.Tendsto",
            mathlib(),
            vec![self.function_letter(&f.text), within, near],
            LeanType::Prop,
        ))
    }

    /// There is a bijection from A to B: `∃ g : α → β, Set.BijOn g A B`,
    /// α and β the types of A's and B's members. The map's letter is one
    /// neither set uses.
    pub(super) fn bijection(&self, a: &Node, b: &Node) -> Route<Printed> {
        let (Some(from), Some(to)) = (self.set_members(a), self.set_members(b)) else {
            return Route::no("a bijection between sets with no Lean type");
        };
        let used: Vec<String> = [a, b]
            .iter()
            .flat_map(|s| s.walk())
            .map(|n| n.text.to_string())
            .collect();
        let Some(g) = ["g", "h", "φ", "ψ"]
            .iter()
            .find(|g| !used.iter().any(|u| u == *g))
        else {
            return Route::no("a bijection whose sets use every map letter");
        };
        match (self.set_term(a), self.set_term(b)) {
            (Route::Built(x), Route::Built(y)) => {
                let map = LeanType::Fun {
                    from: Box::new(from.member_type()),
                    to: Box::new(to.member_type()),
                };
                let bij = Printed::applied(
                    "Set.BijOn",
                    super::super::doc::Source::Mathlib,
                    vec![Printed::letter(*g, map.clone()), x, y],
                    LeanType::Prop,
                );
                Route::Built(Printed::of(
                    super::super::doc::TermKind::Quantified {
                        quant: super::super::doc::Quant::Exists,
                        letter: g.to_string(),
                        letter_ty: map,
                        guard: None,
                        body: Box::new(bij),
                        bounded: false,
                    },
                    LeanType::Prop,
                ))
            }
            (Route::Declined(d), _) | (_, Route::Declined(d)) => Route::Declined(d),
        }
    }

    /// f is differentiable on U: each point of U is inside f's domain D, D
    /// about it, and f has a derivative there, `∀ x ∈ U, D ∈ nhds x ∧
    /// DifferentiableAt ℝ f x`. set.mm takes a derivative only at a point
    /// inside the domain, where it is Lean's `deriv f`; of f between number
    /// systems, D is all of ℝ and only the derivative is said.
    pub(super) fn differentiable(&self, node: &Node) -> Route<Printed> {
        let [f, set] = node.children.as_slice() else {
            return Route::no("a differentiability of other than a function and a set");
        };
        if !f.is_name()
            || !matches!(
                self.letters.get(f.text.as_str()),
                Some(LetterType::Function {
                    from: Num::Real,
                    to: Num::Real
                })
            )
        {
            return Route::no(format!("{} is no function from ℝ to ℝ", f.text));
        }
        let Some(domain) = self.domain_of(&f.text) else {
            return Route::no(format!(
                "a derivative of {}, whose domain no line gives",
                f.text
            ));
        };
        let u = match self.numbers_at(set, Num::Real) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(x) = ["x", "y", "z", "t", "w", "v"]
            .into_iter()
            .find(|l| !self.letters.contains_key(*l) && *l != &*f.text)
        else {
            return Route::no("a differentiability using every letter it could bind");
        };
        let given = self.domains.contains_key(f.text.as_str());
        let real = LeanType::Num(Num::Real);
        let point = Printed::letter(x, real.clone());
        let at = Printed::applied(
            "DifferentiableAt",
            super::super::doc::Source::Mathlib,
            vec![
                Printed::constant(
                    "ℝ",
                    super::super::doc::Source::Mathlib,
                    LeanType::Universe,
                ),
                self.function_letter(&f.text),
                point.clone(),
            ],
            LeanType::Prop,
        );
        let said = match given {
            true => {
                let near = Printed::applied(
                    "nhds",
                    super::super::doc::Source::Mathlib,
                    vec![point],
                    LeanType::Set(Box::new(LeanType::Set(Box::new(real.clone())))),
                );
                // The domain stands bracketed as an argument does, as a
                // map's domain is written everywhere it is named.
                let inside = match relation_of("∈", as_argument(domain), near) {
                    Route::Built(i) => i,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match conjunction(inside, at) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            false => at,
        };
        let member = Printed::letter(x, real.clone());
        let guard = match relation_of("∈", member, as_argument(u)) {
            Route::Built(g) => g,
            Route::Declined(d) => return Route::Declined(d),
        };
        Route::Built(Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: super::super::doc::Quant::ForAll,
                letter: x.to_string(),
                letter_ty: real,
                guard: Some(Box::new(guard)),
                body: Box::new(said),
                bounded: true,
            },
            LeanType::Prop,
        ))
    }

    /// f is continuous on D, `ContinuousOn f D`, of a function into ℝ and a
    /// set of reals: `predicate` is what goes before f.
    pub(super) fn continuous(&self, node: &Node, predicate: &str) -> Route<Printed> {
        let [f, set] = node.children.as_slice() else {
            return Route::no("a continuity of other than a function and a set");
        };
        if !f.is_name()
            || !matches!(
                self.letters.get(f.text.as_str()),
                Some(LetterType::Function { to: Num::Real, .. })
            )
        {
            return Route::left_out(format!("{} is no function into ℝ", f.text));
        }
        match self.numbers_at(set, Num::Real) {
            Route::Built(s) => Route::Built(Printed::applied(
                predicate,
                super::super::doc::Source::Mathlib,
                vec![self.function_letter(&f.text), s],
                LeanType::Prop,
            )),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// The node, a number, written as a Lean term of type `at`.
    pub fn number(&self, node: &Node, at: Num) -> Route<Printed> {
        self.note_root_form(node);
        let named = self
            .said_integer(node)
            .filter(|s| !s.slot_only || at <= Num::Int);
        if let Some(s) = named {
            let value = match &s.value {
                Some(v) => super::super::tactics::bracket(v.clone()),
                None => Printed::cast(
                    Printed::applied(
                        "Classical.choose",
                        super::super::doc::Source::Core,
                        vec![s.proof.clone()],
                        LeanType::Num(s.ty),
                    ),
                    LeanType::Num(s.ty),
                ),
            };
            return self.raise(value, s.ty, at);
        }
        if let Some(count) = self.finite_count(node) {
            return match count {
                Route::Built(c) => self.raise(c, Num::Nat, at),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        // A term the page says once is in ℕ₀, n or 2k + 1 of letters in
        // ℕ, where Lean wants a natural number: the integer it is, taken to
        // ℕ, which its fact 0 ≤ t brings back.
        if at == Num::Nat && !self.natural(node) && self.said_whole(node) {
            return match self.number(node, Num::Int) {
                Route::Built(t) => Route::Built(Printed::of(
                    super::super::doc::TermKind::ToNat(Box::new(t)),
                    super::super::doc::LeanType::Num(Num::Nat),
                )),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        if at == Num::Nat && !self.natural(node) {
            return Route::no(format!(
                "{} would be computed in ℕ, where subtraction stops at 0",
                self.grammar.print(node)
            ));
        }
        if let Some([base, exponent]) = self.integer_power(node) {
            if at < Num::Rat {
                return Route::no(format!(
                    "{} is a power to an integer, taken in {}",
                    self.grammar.print(node),
                    at.lean()
                ));
            }
            let base = match self.number(base, at) {
                Route::Built(b) => b,
                declined => return declined,
            };
            let exponent = match self.number_fixed(exponent, Num::Int) {
                Route::Built(e) => e,
                declined => return declined,
            };
            // Lean reads no negation after `^`, so `a ^ -m` is written
            // `a ^ (-m)`: an exponent that binds less tightly than `^` is
            // bracketed.
            let exponent = match exponent.prec() < 76 {
                true => super::super::tactics::bracket(exponent),
                false => exponent,
            };
            return Route::Built(Printed::infix(
                super::super::doc::Op::POWER,
                base,
                exponent,
                self.num_type(at),
            ));
        }
        if is_big_operator(node) {
            return self.sum(node, at);
        }
        if &*node.notation_name() == "series" {
            return self.series(node, at);
        }
        if &*node.notation_name() == "integral" {
            return self.integral(node, at);
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) if *n == at => {
                    Route::Built(Printed::letter(
                        super::super::names::letter(&node.text),
                        self.num_type(*n),
                    ))
                }
                Some(LetterType::Number(n)) if *n < at => Route::Built(self.cast(
                    &Printed::letter(
                        super::super::names::letter(&node.text),
                        self.num_type(*n),
                    ),
                    at,
                )),
                Some(LetterType::Number(n)) => Route::no(format!(
                    "{} is in {}, which Lean would cast down to {}",
                    node.text,
                    n.lean(),
                    at.lean()
                )),
                _ => Route::no(format!("{} has no Lean number type", node.text)),
            },
            NUMERAL => Route::Built(Printed::numeral(&*node.text, self.num_type(at))),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                let applied = match self.applied(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let Some(arg) = node.children.get(1) else {
                    return Route::no("an application with no argument");
                };
                let arg = match &applied.takes {
                    Members::Numbers(from) => self.number(arg, *from),
                    _ => self.set_term(arg),
                };
                let arg = match arg {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let to = applied.gives;
                let value = Printed::of(
                    super::super::doc::TermKind::App {
                        head: Box::new(self.function_printed(&node.children[0])),
                        args: vec![super::super::doc::Arg::Explicit(arg)],
                        explicit: false,
                    },
                    self.num_type(to),
                );
                self.raise(value, to, at)
            }
            _ => {
                // A library function takes the form for its arguments' own
                // types, cos(0) `Real.cos 0` even in a line of complex
                // numbers, and its value is cast up there as any value is.
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let here = match template.yields {
                    Slot::Alpha(floor) => {
                        if at < floor && at != Num::Nat {
                            return Route::no(format!(
                                "{} is computed in {} at least, where Lean is asked for {}",
                                self.grammar.print(node),
                                floor.lean(),
                                at.lean()
                            ));
                        }
                        at
                    }
                    Slot::Fixed(n) => n,
                    Slot::Prop => {
                        return Route::no(format!(
                            "{} is a formula, not a number",
                            node.notation_name()
                        ))
                    }
                };
                // A subtraction a form computes in ℕ stops at 0, so it is
                // the page's only where the page says the difference is at
                // least 0, whatever its parts are: a − b of a, b ∈ ℕ is not.
                if here == Num::Nat
                    && node.spelling() == crate::notations::MINUS
                    && !self.said_whole(node)
                {
                    return Route::no(format!(
                        "{} would be computed in ℕ, where subtraction stops at 0",
                        self.grammar.print(node)
                    ));
                }
                // A value of a fixed type, ⌊x⌋ in ℤ, computes what it takes
                // in that part's own least type, not the type around it.
                let alpha = match template.yields {
                    Slot::Fixed(_) => match self.alpha_of(node, template) {
                        Route::Built(a) => a,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    _ => here,
                };
                let children = match self.holes(node, template, alpha) {
                    Route::Built(c) => c,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // A value of a fixed type an operation makes, ⌊x⌋ mod 10 in ℤ,
                // is cast up whole at its own type first: Lean puts a cast
                // around such a term at its leaves, `(a % (10 : ℤ) : ℝ)`
                // taking the remainder in ℝ.
                let value = match fill(template, &children) {
                    Route::Built(v) => v.typed(self.num_type(here)),
                    Route::Declined(d) => return Route::Declined(d),
                };
                let value = match template.yields {
                    Slot::Fixed(_) if here < at && value.prec() < APP => {
                        self.cast(&value, here)
                    }
                    _ => value,
                };
                self.raise(value, here, at)
            }
        }
    }

    /// A value of type `own` as a term of type `at`: itself, or cast up.
    pub(super) fn raise(&self, value: Printed, own: Num, at: Num) -> Route<Printed> {
        if own == at {
            Route::Built(value)
        } else if own == Num::Real && at == Num::Complex && value.prec() == 75 {
            // Lean takes `(x ^ a : ℂ)` as x cast up to the power a, and has
            // no power of a complex number to a real exponent, so a power is
            // cast whole, at its own type first.
            let own_typed = self.cast(&value, own);
            Route::Built(self.cast(&own_typed, at))
        } else if own < at {
            Route::Built(self.cast(&value, at))
        } else {
            Route::no(format!(
                "a value in {} where Lean is asked for {}",
                own.lean(),
                at.lean()
            ))
        }
    }

    /// Each child of a node in its template's hole: a number in the type
    /// the hole takes, `alpha` for a hole of the formula's type, or a
    /// formula.
    pub(super) fn holes(
        &self,
        node: &Node,
        template: &Template,
        alpha: Num,
    ) -> Route<Vec<Printed>> {
        let args = self.args(node);
        if args.len() != template.holes.len() {
            return Route::no(format!(
                "{} has {} parts and its lean template {} holes",
                node.notation_name(),
                args.len(),
                template.holes.len()
            ));
        }
        // A value of a fixed type, ⌊7/2⌋ in ℤ, takes no type from around
        // it, so where nothing in what it takes fixes that type the type is
        // written: ⌊(7 : ℝ) / 2⌋.
        let told = matches!(template.yields, Slot::Fixed(_))
            && !args
                .iter()
                .zip(&template.holes)
                .any(|(c, s)| matches!(s, Slot::Alpha(_)) && self.pinned(c));
        // The later part of "P and Q" or "if P then Q" is read where P holds,
        // √x of "x > 0 and x² < √x" the square root of a number at least 0.
        let guarded = self.is_and(node)
            || matches!(
                node.notation(),
                crate::notations::IMPLICATION | crate::notations::CONDITIONAL
            );
        let mut out = Vec::new();
        for (i, (child, slot)) in args.iter().zip(&template.holes).enumerate() {
            let printed = match slot {
                Slot::Alpha(_) if told => {
                    self.number(child, alpha).map(|p| self.cast(&p, alpha))
                }
                Slot::Alpha(_) => self.number(child, alpha),
                Slot::Fixed(n) => self.number_fixed(child, *n),
                Slot::Prop if guarded && i > 0 => {
                    self.knowing(&args[..i]).formula(child)
                }
                Slot::Prop => self.formula(child),
            };
            match printed {
                Route::Built(p) => out.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(out)
    }

    /// A number in a hole that always takes type `n`: computed there, a
    /// term too wide for it declined. A formula of numerals alone is
    /// written with its type.
    pub fn number_fixed(&self, child: &Node, n: Num) -> Route<Printed> {
        if n != Num::Nat {
            match self.carrier(child) {
                Route::Built(c) if c > n => {
                    return Route::no(format!(
                        "{} is in {}, where Lean needs {}",
                        self.grammar.print(child),
                        c.lean(),
                        n.lean()
                    ))
                }
                Route::Built(_) => {}
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let printed = match self.number(child, n) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        if self.pinned(child) || n == Num::Nat {
            Route::Built(printed)
        } else {
            Route::Built(self.cast(&printed, n))
        }
    }
}
