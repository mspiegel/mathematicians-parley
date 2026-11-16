//! Templates, functions, carriers and natural forms.

use super::*;
use crate::notations::{
    COMPOSITION, DERIVATIVE, INTEGRAL, INVERSE, NTH_DERIVATIVE, POLYNOMIAL_DEGREE,
    SUPREMUM, UNARY_MINUS,
};

impl Writer<'_> {
    /// The node's arguments that every Lean form of its notation reads at ℝ,
    /// the A/B of ⌊A/B⌋, whatever their own types.
    pub fn always_real_args<'n>(&self, node: &'n Node) -> Vec<&'n Node> {
        let Some(pattern) = self.grammar.written_by(node.spelling()) else {
            return Vec::new();
        };
        let real = self
            .templates
            .always_real(&node.notation_name(), &pattern.pattern);
        self.args(node)
            .iter()
            .zip(real)
            .filter(|(_, r)| *r)
            .map(|(a, _)| a)
            .collect()
    }

    /// Whether child `at` of `parent` is written in the type of the formula
    /// it stands in: a hole its template computes in the formula's type
    /// (`Slot::Alpha`), a side, a part of a sum or product, a power's base.
    /// A hole of a type of its own (`Slot::Fixed`), an exponent or a
    /// function's argument, is not, nor is a library function's name. An
    /// equation's or an order's sides have no template: `relation` writes
    /// both in the one type that holds them, the formula's.
    pub fn in_formula_type(&self, parent: &Node, at: usize) -> bool {
        if matches!(parent.notation(), EQUALITY | ORDER) {
            return true;
        }
        let Route::Built(template) = self.template(parent) else {
            return false;
        };
        let hole = match self.library_function(parent).is_some() {
            true => at.checked_sub(1),
            false => Some(at),
        };
        matches!(
            hole.and_then(|h| template.holes.get(h)),
            Some(Slot::Alpha(_))
        )
    }

    /// The template the node's notation and pattern have in Lean, or a
    /// decline naming the notation.
    pub fn template(&self, node: &Node) -> Route<&Template> {
        if let Some(t) = self.library_function(node) {
            return Route::Built(t);
        }
        let name = node.notation_name();
        let Some(pattern) = self.grammar.written_by(node.spelling()) else {
            return Route::no(format!("{name} is written by no plain pattern"));
        };
        // A real power or square root of a base not shown at least 0 is the
        // principal value, which is complex: its form in ℂ.
        if !self.principal_is_real(node) {
            let args = vec![Num::Complex; node.children.len()];
            return match self.templates.get(&name, &pattern.pattern, &args) {
                Some(t) if t.yields == Slot::Fixed(Num::Complex) => Route::Built(t),
                _ => Route::no(format!("notation {name} has no lean-builds form in ℂ")),
            };
        }
        // Of forms by type, the one for its terms' own types: a letter of
        // ℕ is a natural number, though it is computed in ℤ at least.
        let args: Vec<Num> = node
            .children
            .iter()
            .filter(|c| self.is_number(c))
            .filter_map(|c| match self.letters.get(c.text.as_str()) {
                Some(LetterType::Number(Num::Nat)) if c.is_name() => Some(Num::Nat),
                _ => self.carrier(c).built(),
            })
            .collect();
        match self.templates.get(&name, &pattern.pattern, &args) {
            Some(t) => Route::Built(t),
            None => Route::no(format!("notation {name} has no lean-builds field")),
        }
    }

    /// The 0 a term is compared with in `at`: told its type where nothing
    /// in the term fixes one, as 2^n − 1 of a natural n, which Lean would
    /// otherwise read in ℕ, where its subtraction stops at 0.
    pub(super) fn zero_at(&self, x: &Node, at: Num) -> Printed {
        let zero = Printed::numeral("0", self.num_type(at));
        if at == Num::Nat || self.pinned(x) {
            zero
        } else {
            Printed::cast(zero, self.num_type(at))
        }
    }

    /// The Lean form of the library function a node applies, `gcd(a, b)`;
    /// None for any other node, a letter of the page applied included.
    pub fn library_function(&self, node: &Node) -> Option<&Template> {
        if !matches!(
            node.notation(),
            crate::notations::APPLICATION | crate::notations::APPLICATION_TO_TWO
        ) {
            return None;
        }
        let f = node.children.first()?;
        if !f.is_name() || self.letters.contains_key(f.text.as_str()) {
            return None;
        }
        // Of a function Lean has at several types, the form its arguments'
        // types take: cos of a complex number is Complex.cos, and σ of a
        // natural number `ArithmeticFunction.sigma 1 n`, of an integer its
        // `toNat`'s.
        let args: Vec<Num> = node.children[1..]
            .iter()
            .filter_map(|a| self.argument_type(a))
            .collect();
        self.templates.function_at(&f.text, &args)
    }

    /// The type a library function reads an argument at: ℕ for a natural
    /// number, n of σ(n) with n ∈ ℕ, written `n.toNat` where n is an
    /// integer (`number`), and otherwise the least that holds it.
    pub(super) fn argument_type(&self, a: &Node) -> Option<Num> {
        match self.natural_form(a) {
            NaturalForm::AsItIs | NaturalForm::ToNat => Some(Num::Nat),
            NaturalForm::Integer => self.carrier(a).built(),
        }
    }

    /// What a node's template fills its holes with: its children, or for a
    /// library function applied, what it is applied to.
    pub fn args<'n>(&self, node: &'n Node) -> &'n [Node] {
        if self.library_function(node).is_some() {
            &node.children[1..]
        } else {
            &node.children
        }
    }

    /// Whether the node is a number: by its sort, or a letter this writer
    /// gives a number type, the ε a "for all ε ∈ ℝ" binds, whose sort a
    /// record's reading may leave unknown.
    pub fn is_number(&self, node: &Node) -> bool {
        // A count of a set is a number of ℕ∞, which the writer's number
        // types do not hold (`sets::count_term`).
        if self.counts(node) {
            return false;
        }
        node.sort.is("number")
            || (node.is_name()
                && matches!(
                    self.letters.get(node.text.as_str()),
                    Some(LetterType::Number(_))
                ))
            // g⁻¹(y), (g ∘ f)(x) and a map applied, of functions of numbers,
            // whose sort the checker leaves open, and f(i) of a function
            // letter into numbers a quantifier binds.
            || (node.notation() == crate::notations::APPLICATION
                && node.children.first().is_some_and(|f| {
                    self.inverse_of_function(f).is_some()
                        || ((matches!(f.notation(), COMPOSITION | DERIVATIVE | NTH_DERIVATIVE)
                            || MapRule::of(f).is_some())
                            && self.function_type(f).built().is_some())
                        || (f.is_name()
                            && self.library_function(node).is_none()
                            && self.applied(node).built().is_some())
                }))
    }

    /// The least number type that holds the node, ℤ at least: the type a
    /// formula made of it alone is computed in.
    pub fn carrier(&self, node: &Node) -> Route<Num> {
        // A term the theorem takes the floor of is a real at least, unless a
        // line says it is a number of a narrower type, which is written as
        // that number (`said_integer`).
        let own = self.own_carrier(node);
        match own {
            Route::Built(n)
                if !self.reals.is_empty()
                    && self.said_integer(node).is_none()
                    && self.reals.contains(&self.grammar.print(node)) =>
            {
                Route::Built(n.max(Num::Real))
            }
            other => other,
        }
    }

    /// The least number type that holds the node by its own parts.
    pub(super) fn own_carrier(&self, node: &Node) -> Route<Num> {
        // A term a line says is an integer is the integer it gives.
        if let Some(s) = self.said_integer(node) {
            return Route::Built(s.ty);
        }
        // A count of a finite set is a natural number, computed in ℤ.
        if let Some(count) = self.finite_count(node) {
            return count.map(|_| Num::Int);
        }
        // A power to an exponent that is no natural number is taken in a
        // field, where Lean's integer power is what the page means.
        if let Some([base, _]) = self.integer_power(node) {
            return match self.carrier(base) {
                Route::Built(n) => Route::Built(n.max(Num::Rat)),
                declined => declined,
            };
        }
        // A sum or a product is computed in its terms' type, its index an
        // integer.
        if is_big_operator(node) {
            return match self.summed(node) {
                Route::Built(s) => s.inner.carrier(s.term),
                Route::Declined(d) => Route::Declined(d),
            };
        }
        // A series is a limit, of real numbers as the series-sum item
        // states it.
        if matches!(node.notation(), SERIES | INTEGRAL) {
            return Route::Built(Num::Real);
        }
        // A polynomial's degree is a natural number, computed in ℤ as a
        // count is.
        if degree_of(node).is_some() {
            return Route::Built(Num::Int);
        }
        // A least upper bound is a number of its set's type (`supremum`).
        if let Some(set) = supremum_of(node) {
            return match self.set_members(set) {
                Some(Members::Numbers(n)) => Route::Built(n.max(Num::Int)),
                _ => Route::no("a least upper bound of a set of no numbers"),
            };
        }
        match node.notation() {
            NAME => match self.letters.get(node.text.as_str()) {
                Some(LetterType::Number(n)) => Route::Built((*n).max(Num::Int)),
                Some(LetterType::Function { .. }) => {
                    Route::no(format!("{} is a function, not a number", node.text))
                }
                Some(LetterType::Statement) => {
                    Route::no(format!("{} is a statement, not a number", node.text))
                }
                Some(
                    LetterType::Set(_)
                    | LetterType::Member(_)
                    | LetterType::Map { .. }
                    | LetterType::Group
                    | LetterType::Identity(_)
                    | LetterType::Subgroup(_)
                    | LetterType::Property(_),
                ) => Route::no(format!("{} is no number", node.text)),
                None => Route::no(format!("{} has no Lean type", node.text)),
            },
            NUMERAL => Route::Built(if node.text.contains('.') {
                Num::Rat
            } else {
                Num::Int
            }),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                match self.applied(node) {
                    Route::Built(a) => Route::Built(a.gives.max(Num::Int)),
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            _ => {
                let template = match self.template(node) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match template.yields {
                    Slot::Fixed(n) => Route::Built(n.max(Num::Int)),
                    Slot::Prop => Route::no(format!(
                        "{} is a formula, not a number",
                        node.notation_name()
                    )),
                    Slot::Alpha(floor) => {
                        let mut out = floor;
                        for (child, slot) in self.args(node).iter().zip(&template.holes)
                        {
                            if let Slot::Alpha(_) = slot {
                                match self.carrier(child) {
                                    Route::Built(n) => out = out.max(n),
                                    Route::Declined(d) => return Route::Declined(d),
                                }
                            }
                        }
                        Route::Built(out)
                    }
                }
            }
        }
    }

    /// How Lean writes a term where a natural number is wanted, a power's
    /// exponent or a library function's argument (`NaturalForm`).
    pub fn natural_form(&self, node: &Node) -> NaturalForm {
        if self.natural(node) {
            NaturalForm::AsItIs
        } else if self.said_whole(node) {
            NaturalForm::ToNat
        } else {
            NaturalForm::Integer
        }
    }

    /// The base and exponent of a power whose exponent is no natural number
    /// as Lean computes one and is not said once in ℕ₀: a negative, an
    /// integer letter, or n − 1 of n ∈ ℕ. None for any other node.
    pub fn integer_power<'n>(&self, node: &'n Node) -> Option<&'n [Node; 2]> {
        if node.notation() != crate::notations::POWER {
            return None;
        }
        let parts: &[Node; 2] = node.children.as_slice().try_into().ok()?;
        (self.natural_form(&parts[1]) == NaturalForm::Integer).then_some(parts)
    }

    /// What the function an application applies takes and gives: a
    /// function of numbers, or a map from a set of things into numbers,
    /// t : X → ℝ, whose value is a number.
    pub(super) fn applied(&self, node: &Node) -> Route<Applied> {
        let Some(f) = node.children.first() else {
            return Route::no("an application of nothing");
        };
        if let Some(LetterType::Map {
            from,
            to: Members::Numbers(gives),
        }) = self.letters.get(f.text.as_str())
        {
            return Route::Built(Applied {
                takes: from.clone(),
                gives: *gives,
            });
        }
        match self.function_type(f) {
            Route::Built((from, to)) => Route::Built(Applied {
                takes: Members::Numbers(from),
                gives: to,
            }),
            Route::Declined(d) => Route::Declined(d),
        }
    }

    /// The types a function takes and gives: a function letter's, or a
    /// composite's, g ∘ f taking what f takes and giving what g gives.
    pub fn function_type(&self, f: &Node) -> Route<(Num, Num)> {
        // A map takes the numbers its set holds, as a letter of that set is
        // typed, and gives what its rule is computed in.
        if let Some(map) = MapRule::of(f) {
            let Some(over) = self.map_over(&map) else {
                return Route::no("a map over a set of no numbers");
            };
            return self
                .map_rule_writer(&map, over)
                .carrier(map.rule)
                .map(|to| (super::letter_type(over), to));
        }
        if f.is_name() {
            return match self.letters.get(f.text.as_str()) {
                Some(LetterType::Function { from, to }) => Route::Built((*from, *to)),
                _ => Route::no(format!("{} has no Lean function type", f.text)),
            };
        }
        // g⁻¹ takes what g gives and gives what g takes; the bridge's
        // inverse is of a function of one type.
        if let Some((g, _)) = self.inverse_of_function(f) {
            return match self.letters.get(g.text.as_str()) {
                Some(LetterType::Function { from, to }) if from == to => {
                    Route::Built((*to, *from))
                }
                _ => Route::no(format!("{}⁻¹ of a function between two types", g.text)),
            };
        }
        // f′ of a function of reals into ℝ, Mathlib's `deriv f`, is one too,
        // and so is f^(n), `iteratedDeriv`.
        if let (DERIVATIVE, [g]) | (NTH_DERIVATIVE, [g, _]) =
            (f.notation(), f.children.as_slice())
        {
            return match self.function_type(g) {
                Route::Built((Num::Real, Num::Real)) => {
                    Route::Built((Num::Real, Num::Real))
                }
                Route::Built(_) => {
                    Route::no("a derivative of a function not from ℝ to ℝ")
                }
                Route::Declined(d) => Route::Declined(d),
            };
        }
        let [g, inner] = f.children.as_slice() else {
            return Route::no("a function that is no letter or composite");
        };
        if f.notation() != COMPOSITION {
            return Route::no("a function that is no letter or composite");
        }
        let (from, middle) = match self.function_type(inner) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (takes, to) = match self.function_type(g) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        if takes != middle {
            return Route::no("a composite of functions whose types do not meet");
        }
        Route::Built((from, to))
    }

    /// The function letter a term is the inverse of, g of g⁻¹, with the
    /// domain a line gives it; None for any other term.
    pub(super) fn inverse_of_function<'n>(
        &self,
        f: &'n Node,
    ) -> Option<(&'n Node, Printed)> {
        let [g] = f.children.as_slice() else {
            return None;
        };
        if f.notation() != INVERSE
            || !matches!(
                self.letters.get(g.text.as_str()),
                Some(LetterType::Function { .. })
            )
        {
            return None;
        }
        Some((g, self.domains.get(g.text.as_str())?.clone()))
    }

    /// A function as Lean writes it, a citation's value as well: a letter,
    /// a map `(fun y : ℝ => y + 1)`, `(g ∘ f)`, `(deriv f)` or the inverse
    /// of a map on its domain, each but a letter in brackets. Declined
    /// where a map's rule is no number Lean writes.
    pub fn function_printed(&self, f: &Node) -> Route<Printed> {
        // A map, `(fun y : ℝ => y + 1)`: its rule in what it gives
        // (`function_type`), its letter of the type it takes.
        if let Some(map) = MapRule::of(f) {
            let Some(over) = self.map_over(&map) else {
                return Route::no("a map over a set of no numbers");
            };
            let inner = self.map_rule_writer(&map, over);
            let to = match inner.carrier(map.rule) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let from = LeanType::Num(super::letter_type(over));
            return inner.number(map.rule, to).map(|body| {
                paren(Printed::of(
                    super::super::doc::TermKind::Quantified {
                        quant: super::super::doc::Quant::Fun,
                        letter: super::super::names::letter(&map.letter.text),
                        letter_ty: from.clone(),
                        guard: None,
                        body: Box::new(body),
                        bounded: false,
                    },
                    LeanType::Fun {
                        from: Box::new(from),
                        to: Box::new(LeanType::Num(to)),
                    },
                ))
            });
        }
        if let Some((g, domain)) = self.inverse_of_function(f) {
            let letter = self.function_letter(&g.text);
            let ty = letter.ty.clone();
            let inverse = Printed {
                kind: super::super::doc::TermKind::App {
                    head: Box::new(Printed::head(
                        super::super::sets::INVERSE,
                        super::super::doc::Source::Bridge(
                            super::super::doc::bridges::BridgeModule::Functions,
                        ),
                    )),
                    args: vec![
                        super::super::doc::Arg::Explicit(letter),
                        super::super::doc::Arg::Explicit(domain),
                    ],
                    explicit: false,
                },
                ty,
            };
            return Route::Built(paren(inverse));
        }
        // f^(n), the n-th derivative: Mathlib's `iteratedDeriv` at the
        // order as a natural number, n.toNat of an integer letter of ℕ₀.
        if let (NTH_DERIVATIVE, [g, n]) = (f.notation(), f.children.as_slice()) {
            let (inner, order) =
                match (self.function_printed(g), self.number(n, Num::Nat)) {
                    (Route::Built(p), Route::Built(k)) => (p, k),
                    (Route::Declined(d), _) | (_, Route::Declined(d)) => {
                        return Route::Declined(d)
                    }
                };
            let ty = inner.ty.clone();
            return Route::Built(paren(Printed {
                kind: super::super::doc::TermKind::App {
                    head: Box::new(Printed::head(
                        "iteratedDeriv",
                        super::super::doc::Source::Mathlib,
                    )),
                    args: vec![
                        super::super::doc::Arg::Explicit(order),
                        super::super::doc::Arg::Explicit(inner),
                    ],
                    explicit: false,
                },
                ty,
            }));
        }
        if let (DERIVATIVE, [g]) = (f.notation(), f.children.as_slice()) {
            let inner = match self.function_printed(g) {
                Route::Built(p) => p,
                declined => return declined,
            };
            let ty = inner.ty.clone();
            return Route::Built(paren(Printed {
                kind: super::super::doc::TermKind::App {
                    head: Box::new(Printed::head(
                        "deriv",
                        super::super::doc::Source::Mathlib,
                    )),
                    args: vec![super::super::doc::Arg::Explicit(inner)],
                    explicit: false,
                },
                ty,
            }));
        }
        match f.children.as_slice() {
            [g, inner] => {
                let outer = match self.function_printed(g) {
                    Route::Built(p) => p,
                    declined => return declined,
                };
                let inner = match self.function_printed(inner) {
                    Route::Built(p) => p,
                    declined => return declined,
                };
                let ty = outer.ty.clone();
                Route::Built(paren(Printed {
                    kind: super::super::doc::TermKind::Infix {
                        op: super::super::doc::Op::COMPOSE,
                        lhs: Box::new(outer),
                        rhs: Box::new(inner),
                    },
                    ty,
                }))
            }
            _ => Route::Built(self.function_letter(&f.text)),
        }
    }

    /// The number system a map's letter runs over: its set, where that is
    /// one, ℕ a positive integer as a letter of ℕ is; else the type of its
    /// set's numbers, ℝ of S ⊆ ℝ. None where its set holds no numbers.
    fn map_over(&self, map: &MapRule) -> Option<System> {
        system_of(map.set).or_else(|| match self.set_members(map.set)? {
            Members::Numbers(n) => Some(System::Type(n)),
            _ => None,
        })
    }

    /// The writer a map's rule is read with: the outer letters, and the
    /// map's own letter introduced in `over` (`map_over`), shadowing any
    /// letter of the same name outside.
    fn map_rule_writer(&self, map: &MapRule, over: System) -> Writer<'_> {
        let mut inner = self.with_letters(self.letters.clone());
        inner.introduce(&map.letter.text, over);
        inner
    }

    /// A function letter with the Lean type the writer gives it, where it
    /// gives one.
    pub(super) fn function_letter(&self, name: &str) -> Printed {
        Printed {
            kind: super::super::doc::TermKind::Letter(super::super::names::letter(
                name,
            )),
            ty: self.letters.get(name).map(LetterType::lean_type),
        }
    }

    /// Whether some part of the node fixes the type Lean computes it in: a
    /// letter, a function's value, or an operation of a fixed type. A
    /// formula of numerals alone is computed in ℕ unless told otherwise.
    pub fn pinned(&self, node: &Node) -> bool {
        match node.notation() {
            NAME => true,
            NUMERAL => false,
            _ if is_big_operator(node)
                || matches!(node.notation(), SERIES | INTEGRAL) =>
            {
                true
            }
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                true
            }
            _ => match self.template(node) {
                Route::Built(t) => match t.yields {
                    Slot::Alpha(_) => self
                        .args(node)
                        .iter()
                        .zip(&t.holes)
                        .any(|(c, s)| matches!(s, Slot::Alpha(_)) && self.pinned(c)),
                    _ => true,
                },
                Route::Declined(_) => true,
            },
        }
    }

    /// Whether a term may be computed in ℕ as Lean computes it there:
    /// built by `+`, `·` and powers from ℕ letters, numerals and values in
    /// ℕ. Subtraction and division are not.
    pub fn natural(&self, node: &Node) -> bool {
        if self.finite_count(node).is_some() || degree_of(node).is_some() {
            return true;
        }
        // A term a step names as a natural number is the one it names.
        if let Some(s) = self.said_integer(node) {
            return s.ty == Num::Nat;
        }
        // A power to an exponent that is no natural number is Lean's
        // integer power, in ℚ at least, whatever its base.
        if self.integer_power(node).is_some() {
            return false;
        }
        match node.notation() {
            NAME => matches!(
                self.letters.get(node.text.as_str()),
                Some(LetterType::Number(Num::Nat))
            ),
            NUMERAL => !node.text.contains('.'),
            crate::notations::APPLICATION if self.library_function(node).is_none() => {
                matches!(
                    self.applied(node),
                    Route::Built(Applied {
                        gives: Num::Nat,
                        ..
                    })
                )
            }
            _ => {
                let Route::Built(t) = self.template(node) else {
                    return false;
                };
                match t.yields {
                    Slot::Fixed(Num::Nat) => true,
                    Slot::Alpha(Num::Int) => {
                        let literal = node.spelling().text();
                        !matches!(&*literal, "−" | "/")
                            && node.notation() != UNARY_MINUS
                            && self.args(node).iter().zip(&t.holes).all(|(c, s)| {
                                !matches!(s, Slot::Alpha(_)) || self.natural(c)
                            })
                    }
                    _ => false,
                }
            }
        }
    }

    /// A sum's parts: the writer its term is read with, its index letter an
    /// integer there, and its index, ends and term.
    pub(super) fn summed<'n>(&self, node: &'n Node) -> Route<Summed<'_, 'n>> {
        let (index, over, term) = match (over_range(node), node.children.as_slice()) {
            (Some([index, from, to, term]), _) => {
                (index, Over::Range { from, to }, term)
            }
            (None, [index, set, term])
                if matches!(node.notation(), SUM_OVER | PRODUCT_OVER) =>
            {
                (index, Over::Set(set), term)
            }
            (None, [index, from, to, term]) => (index, Over::Range { from, to }, term),
            (None, _) => return Route::no("a sum of other than four parts"),
        };
        if !index.is_name() {
            return Route::no("a sum whose index is no letter");
        }
        // Over a range the index is an integer; over a set, a member of it;
        // over ∅, which holds members of no one type, what the function
        // the term applies to the index takes, k of Σ(k ∈ ∅) t(k).
        let ty = match &over {
            Over::Range { .. } => LetterType::Number(Num::Int),
            Over::Set(set) => match self
                .set_members(set)
                .or_else(|| self.index_taken(index, term))
                .or_else(|| self.empty_holds(set))
                .or_else(|| self.empty_of_numbers(set))
            {
                Some(m) => m.letter(),
                None => return Route::no("a sum over a set with no Lean type"),
            },
        };
        let mut inner = self.with_letters(self.letters.clone());
        inner.letters.insert(index.text.to_string(), ty);
        inner.wholes.shift_remove(&*index.text);
        // An index from 0 or 1 is said once in ℕ₀ or ℕ by where it starts
        // (`citing::index_system`), so x^k of Σ(k = 0 to n) x^k is a
        // natural power.
        if let Over::Range { from, .. } = &over {
            match crate::citing::index_system(from) {
                Some(crate::rules::System::N) => {
                    inner.introduce(&index.text, System::Positive)
                }
                Some(crate::rules::System::N0) => {
                    inner.introduce(&index.text, System::NonNegative)
                }
                _ => {}
            }
        }
        let range = match &over {
            Over::Range { from, to } => Some((*from, *to)),
            Over::Set(_) => None,
        };
        inner.bounds = bounds::inside_sum(self, index, range);
        Route::Built(Summed {
            inner,
            index,
            over,
            term,
        })
    }

    /// What ∅ holds where the lines around it say (`empty_of`), the members
    /// of X in the base of an induction on the parts of X; None for any
    /// other set, or where nothing says.
    pub(super) fn empty_holds(&self, set: &Node) -> Option<Members> {
        match set.notation() {
            EMPTY_SET => self.empty_of.clone(),
            _ => None,
        }
    }

    /// The integers, for ∅ in a sum that nothing else types, Σ(k ∈ ∅) k²:
    /// the index is a number, ∅ holds none, and a formula is computed in
    /// the least type, ℤ, that holds what it writes, as the library's
    /// `sum-empty-set` is over a `Set ℤ`. None for any other set.
    pub(super) fn empty_of_numbers(&self, set: &Node) -> Option<Members> {
        (set.notation() == EMPTY_SET).then_some(Members::Numbers(Num::Int))
    }

    /// What a function the term applies to the index letter takes, the
    /// members k is among in t(k); None where the term applies none to it.
    pub(super) fn index_taken(&self, index: &Node, term: &Node) -> Option<Members> {
        term.walk().iter().find_map(|n| {
            let applies = n.notation() == crate::notations::APPLICATION
                && self.library_function(n).is_none()
                && matches!(n.children.as_slice(), [_, x] if x.is_name() && x.text == index.text);
            match applies.then(|| self.applied(n)) {
                Some(Route::Built(a)) => Some(a.takes),
                _ => None,
            }
        })
    }
}

/// The function a degree is of, F of deg(F); None for any other term.
pub(super) fn degree_of(node: &Node) -> Option<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (POLYNOMIAL_DEGREE, [f]) => Some(f),
        _ => None,
    }
}

/// The set a least upper bound is of, S of sup S; None for any other term.
pub(super) fn supremum_of(node: &Node) -> Option<&Node> {
    match (node.notation(), node.children.as_slice()) {
        (SUPREMUM, [set]) => Some(set),
        _ => None,
    }
}

/// A map, the map sending y ∈ A to E or y ∈ A ↦ E: Lean's `fun y => E`, a
/// function on the whole type of A's members, as a function letter is.
pub(super) struct MapRule<'n> {
    /// The letter it binds, y.
    pub letter: &'n Node,
    /// The set the letter runs over, A.
    pub set: &'n Node,
    /// What it sends the letter to, E.
    pub rule: &'n Node,
}

impl<'n> MapRule<'n> {
    /// The map `f` is; None where it is no map.
    pub fn of(f: &'n Node) -> Option<MapRule<'n>> {
        let (crate::notations::MAP, [letter, set, rule]) =
            (f.notation(), f.children.as_slice())
        else {
            return None;
        };
        Some(MapRule { letter, set, rule })
    }
}
