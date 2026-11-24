//! Proof methods: kinds, exhibits, counts and non-negativity.

use std::collections::BTreeMap;
use std::iter::Peekable;

use super::super::doc::CountForm::{Extended, Natural};
use super::super::doc::{forms, CountForm, LeanType, Quant, TermKind};
use super::super::templates::Num;
use super::super::{expr, tactics as t};
use super::*;
use crate::checker::record::Besides;
use crate::citing::bounds::Bound;
use crate::citing::finite::{FiniteBy, Making};
use crate::citing::{
    claimed_member, finite, nonzero_said_once, reason_within, OnceReason, SaidOnceFact,
};
use crate::corpus::{Define, DefineParts};
use crate::formula::node::Sort;
use crate::formula::page;
use crate::matching::Binding;
use crate::notations::{
    ADDITIVE, APPLICATION, AT_LEAST, AT_MOST, CARDINALITY, EQUALS, FOR_ALL,
    FUNCTIONS_FROM, GREATER, INTEGER_RANGE, LESS, MEMBERSHIP, MULTIPLICATIVE, NUMERAL,
    ORDER, PLUS, POLYNOMIALS, POWER, POWERSET, SET_BUILDER, SUPERSCRIPT, THERE_IS,
    THERE_IS_SOME, TIMES,
};
use crate::rules::WHOLE;
use crate::{corpus, matching, rules};

impl<'a> Proof<'a> {
    /// The proof of `fact`, a define of a kind's, by the define's reason.
    pub(super) fn kind_proof(
        &self,
        d: usize,
        fact: &Node,
    ) -> Route<super::super::doc::Proof> {
        let line = &self.thm.defines[d];
        let members = &self.sources.checked.grammar.members;
        let kinded = match line.kinded(&self.thm.path, members) {
            Ok(Some(k)) => k,
            Ok(None) => return Route::no("a define of a kind with no reason"),
            Err(p) => return Route::no(p.to_string()),
        };
        let Ok(just) = &kinded.shown.by else {
            return Route::no("a define whose reason does not read");
        };
        // What the check found the reason's lines hold, as a requires line's
        // proof reads it (`CheckedTheorem::held_by_lines`).
        *self.held_now.borrow_mut() = self.held_at(just.line);
        let reason = Reason {
            just,
            cited: self.rec.cited_requires.get(&kinded.shown.line),
        };
        self.proof_of(reason, 0, fact)
    }

    /// A define naming a whole number its value is shown to be, `let e =
    /// p/d, a positive integer` with `p/d ∈ ℕ` its reason's fact: that
    /// fact proved by the reason, as a requires line is, and the name taken
    /// from it, `obtain ⟨e, hD1_pos, hD1⟩`, so that the define's equation
    /// e = p/d is said in the value's type.
    pub(super) fn kinded_witness(
        &mut self,
        d: usize,
        name: &str,
        body: Node,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let shown = match self.kind_shown(d) {
            Route::Built(s) => s,
            Route::Declined(why) => return Route::Declined(why),
        };
        let KindShown { fact, says, proof } = shown;
        let kind_line = Tactic::Have {
            name: format!("{}_kind", line_name(&line.label)),
            says,
            proof: Box::new(proof),
        };
        let [_, set] = fact.children.as_slice() else {
            return Route::no("a kind's fact that is no membership");
        };
        // The letter is an integer whatever its kind; ℕ and ℕ₀ say its order
        // beside it, 0 < e or 0 ≤ e, as `let e ∈ ℕ` does.
        let system = match super::super::expr::system_of(set) {
            Some(
                s @ (super::super::expr::System::Positive
                | super::super::expr::System::NonNegative),
            ) => s,
            Some(
                s @ super::super::expr::System::Type(super::super::templates::Num::Int),
            ) => s,
            _ => return Route::no("a define of a kind other than ℕ, ℕ₀ or ℤ"),
        };
        let ordered = !matches!(system, super::super::expr::System::Type(_));
        let ty = super::super::templates::Num::Int;
        let label = line_name(&line.label);
        let (at, page_label) = (line.line, line.label.clone());
        let letter = super::super::names::letter(name);
        // Its kind as a line of the letter, `A ∈ ℕ`, proved by the order
        // named beside it, `0 < A`: a step finds the letter's fact there.
        if ordered {
            let member = fact
                .with_children(vec![Node::name(body.sort.clone(), name), set.clone()]);
            self.store(
                format!("{page_label} kind"),
                vec![LineSentence {
                    at: 0,
                    node: member,
                    name: None,
                    proof: super::super::tactics::hyp(&format!("{label}_pos")),
                    says: None,
                }],
            );
        }
        // A value of integers, k + 1, is the letter as any define's value
        // is: Lean's `set` of it, which a step citing the define unfolds
        // (`cited_defines`); its kind said as an order of the value, 0 < k +
        // 1, which the `set` makes an order of the letter.
        let integer = self
            .writer
            .carrier(&body)
            .built()
            .is_some_and(|n| n <= super::super::templates::Num::Int);
        if integer {
            let value = match self.writer.number_fixed(&body, ty) {
                Route::Built(v) => v,
                Route::Declined(why) => return Route::Declined(why),
            };
            self.push_at(depth, kind_line, at, Spot::Statement);
            self.name_value(d, name, LetterType::Number(ty), value, body, depth);
            self.writer.introduce(name, system);
            if ordered {
                self.push_at(
                    depth,
                    Tactic::Name {
                        name: format!("{label}_pos"),
                        term: super::super::tactics::hyp(&format!("{label}_kind")),
                    },
                    at,
                    Spot::Statement,
                );
            }
            return Route::Built(());
        }
        // A value of a wider type, p/d: its kind's fact is a witness, `∃ m :
        // ℤ, 0 < m ∧ (m : ℚ) = p/d`, and the letter is that m.
        let names = match ordered {
            true => vec![letter.clone(), format!("{label}_pos"), label.clone()],
            false => vec![letter.clone(), label.clone()],
        };
        self.push_at(depth, kind_line, at, Spot::Statement);
        self.push_at(
            depth,
            Tactic::Obtain {
                names,
                says: None,
                from: super::super::tactics::hyp(&format!("{label}_kind")),
            },
            at,
            Spot::Statement,
        );
        self.writer.introduce(name, system);
        self.witness_letters.push(WitnessLetter {
            value: body.clone(),
            letter: Node::name(body.sort.clone(), name),
        });
        let equation = Node::of(
            EQUALS,
            Sort::of("formula"),
            vec![Node::name(body.sort.clone(), name), body],
        );
        self.named.insert(page_label.clone(), vec![label.clone()]);
        self.witnessed.insert(page_label.clone());
        self.trees
            .insert(page_label, vec![LineSentence::only(equation, label)]);
        Route::Built(())
    }

    /// The function a step narrows, of values Lean computes wider than the
    /// step says they are, `for all x ∈ ℚ, g(x) ∈ ℕ` of `g : ℚ → ℚ`
    /// (`CheckedTheorem::define_values`): the choice of the witness the
    /// step's fact gives at each member, under the define's own name, `obtain
    /// ⟨g, s5_pos, s5_eq⟩ : ∃ h : ℚ → ℤ, (∀ x, 0 < h x) ∧ ∀ x, ↑(h x) = g
    /// x`. Every line from here writes the narrowed function, as a line
    /// saying a term is an integer makes every later line write that integer
    /// (`SaidInteger`); the define's equation is said again of it, `∀ x,
    /// ↑(g x) = v`, so that a step citing the define reads the function it
    /// writes. `says` is the step's fact as Lean states it, `∀ x ∈ X, ∃ m :
    /// ℤ, ↑m = g x`, by the step's name `hyp`; a fact over all of a number
    /// type has no guard. None where the fact is not of that form, a type `g
    /// : ℚ → ℕ`, which narrows nothing Lean can choose from.
    pub(super) fn narrowed_function(
        &mut self,
        narrowing: Narrowing,
        says: &Printed,
        at: usize,
        depth: usize,
    ) -> Option<()> {
        let Narrowing {
            function,
            from,
            to,
            ref hyp,
        } = narrowing;
        // ∀ a ∈ X, ∃ m : ℤ, ↑m = v: the guard, and the value in its type.
        let TermKind::Quantified {
            quant: Quant::ForAll,
            letter,
            letter_ty,
            guard,
            body: each,
            ..
        } = &says.kind
        else {
            return None;
        };
        // The witness's bound, where the step gives one, the guard `0 < m`
        // of `∃ m : ℤ, 0 < m ∧ ↑m = v`, and its equation.
        let TermKind::Quantified {
            quant: Quant::Exists,
            letter: witness_letter,
            guard: bound,
            body: witness,
            ..
        } = &each.kind
        else {
            return None;
        };
        let TermKind::Infix { rhs: value, .. } = &witness.kind else {
            return None;
        };
        // The value is the function's, g x, and no other sentence's term.
        let TermKind::App { head, .. } = &super::terms::bare_term(value).kind else {
            return None;
        };
        let own = super::super::names::letter(&function);
        if !matches!(&head.kind, TermKind::Letter(l) if *l == own) {
            return None;
        }
        let function_ty = LetterType::Function { from, to }.lean_type();
        let a = || t::hyp(letter);
        let h = || t::hyp("h");
        // ∃ g : ℤ → ℤ, ∀ a ∈ X, ↑(g a) = v.
        // The chosen function's binder, apart from the define's own name,
        // which the statement says it equals: `∃ g' : ℚ → ℤ, ∀ x, ↑(g' x) =
        // g x`.
        let chosen_name = format!("{own}'");
        let g_a = applied_to(t::hyp(&chosen_name), a());
        let equal = Printed::infix(
            super::super::doc::Op::EQUALS,
            Printed::cast(
                g_a.clone(),
                value
                    .ty
                    .clone()
                    .unwrap_or(super::super::doc::LeanType::Prop),
            ),
            (**value).clone(),
            super::super::doc::LeanType::Prop,
        );
        let every = |body: Printed| {
            Printed::of(
                TermKind::Quantified {
                    quant: Quant::ForAll,
                    letter: letter.clone(),
                    letter_ty: letter_ty.clone(),
                    guard: guard.clone(),
                    body: Box::new(body),
                    bounded: false,
                },
                super::super::doc::LeanType::Prop,
            )
        };
        // The bound said of the function's values, `∀ x, 0 < g x`, beside its
        // equation: `∃ g, (∀ x, 0 < g x) ∧ ∀ x, ↑(g x) = v`.
        let bounded = bound.as_ref().map(|b| {
            b.substituted(&BTreeMap::from([(witness_letter.clone(), g_a.clone())]))
        });
        let said = match &bounded {
            Some(b) => Printed::infix(
                super::super::doc::Op::AND,
                every(b.clone()),
                every(equal),
                super::super::doc::LeanType::Prop,
            ),
            None => every(equal),
        };
        let chosen =
            super::super::expr::witnessed(chosen_name.clone(), function_ty, None, said);
        // Each part of the witness's spec, by its projection: the whole of
        // it, or its bound and its equation apart.
        let parts: Vec<Vec<&str>> = match bounded {
            Some(_) => vec![vec!["choose_spec", "1"], vec!["choose_spec", "2"]],
            None => vec![vec!["choose_spec"]],
        };
        let made = match guard {
            // ⟨fun a => if h : a ∈ X then (s5 a h).choose else 0, fun a h =>
            // by simp only [h, ↓reduceDIte]; exact (s5 a h).choose_spec⟩.
            Some(guard) => {
                let at_member = || applied_to(applied_to(t::hyp(hyp), a()), h());
                let pick = Printed::of(
                    TermKind::DependentIf {
                        proof: "h".to_string(),
                        cond: guard.clone(),
                        yes: Box::new(projected(at_member(), &["choose"])),
                        no: Box::new(Printed::numeral(
                            "0",
                            super::super::doc::LeanType::Num(to),
                        )),
                    },
                    super::super::doc::LeanType::Num(to),
                );
                // The function applied is reduced and its `if` taken by h
                // together, as `rw` does not reach under the application.
                let spec = |path: &[&str]| {
                    t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
                        t::simp_only(
                            false,
                            None,
                            vec![
                                t::forwards(h()),
                                t::forwards(t::lemma("↓reduceDIte")),
                            ],
                            None,
                        ),
                        Tactic::Exact(projected(at_member(), path)),
                    ])))
                };
                let mut out = vec![untyped_lambda(&[letter.as_str()], pick)];
                out.extend(
                    parts
                        .iter()
                        .map(|p| untyped_lambda(&[letter.as_str(), "h"], spec(p))),
                );
                super::super::expr::anonymous(out)
            }
            // ⟨fun x => (s5 x).choose, fun x => (s5 x).choose_spec⟩.
            None => {
                let at_member = || applied_to(t::hyp(hyp), a());
                let mut out = vec![untyped_lambda(
                    &[letter.as_str()],
                    projected(at_member(), &["choose"]),
                )];
                out.extend(parts.iter().map(|p| {
                    untyped_lambda(&[letter.as_str()], projected(at_member(), p))
                }));
                super::super::expr::anonymous(out)
            }
        };
        let ordered = parts.len() > 1;
        let equation = format!("{hyp}_eq");
        let names = match ordered {
            true => vec![own.clone(), format!("{hyp}_pos"), equation.clone()],
            false => vec![own.clone(), equation.clone()],
        };
        // The define's equation, said of the narrowed function at every
        // member, `∀ x, ↑(g x) = v`: read before the function's type
        // changes, and proved after, from the step's equation and the
        // define's `set`.
        let restated = self.define_restated(&function)?;
        self.narrowings.push(NarrowingUndo {
            depth,
            function: function.clone(),
            letter: self.writer.letters.get(&function).cloned(),
            label: restated.label.clone(),
            tree: self.trees.get(&restated.label).cloned(),
            named: self.named.get(&restated.label).cloned(),
            witnessed: self.witnessed.contains(&restated.label),
        });
        self.push_at(
            depth,
            Tactic::Obtain {
                names,
                says: Some(chosen),
                from: made,
            },
            at,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(function.clone(), LetterType::Function { from, to });
        // The step's own sentence, read from here of the narrowed function:
        // `∀ x, 0 < g x` of ℕ, the bound beside its equation, and of ℤ what
        // Lean's type gives.
        let mut lambda = vec![letter.as_str()];
        if guard.is_some() {
            lambda.push("_");
        }
        let given = match ordered {
            true => t::hyp(&format!("{hyp}_pos")),
            false => untyped_lambda(&lambda, t::lemma("trivial")),
        };
        // A line above it that names the function is read from here of the
        // narrowed one, through the step's equation, where a step cites it:
        // `∀ x, f✝ x = F ↑x` as `∀ x, ↑(f x) = F ↑x`, by `simp only [←
        // s2_eq] at h`. A line that put a value of the function in a set
        // stated it by a witness, `∃ m : ℤ, ↑m = f✝ a ∧ m ∈ R`, which the
        // narrowed function's value is: the cast taken off the witness's
        // equation and the witness put for (`exists_eq_left`).
        let cast_inj = match to {
            super::super::templates::Num::Rat => "Rat.cast_inj",
            super::super::templates::Num::Real => "Complex.ofReal_inj",
            _ => "Int.cast_inj",
        };
        let carried = |old: &Printed, says: Option<Printed>, witnessed: bool| {
            let mut rules = vec![t::backwards(t::hyp(&equation))];
            if witnessed {
                rules.push(t::forwards(t::lemma(cast_inj)));
                rules.push(t::forwards(t::lemma("exists_eq_left")));
            }
            // Of a narrowing over a set, `∀ a ∈ X, ↑(f a) = f✝ a`, the
            // equation holds under the line's own guard, which `simp`
            // takes from where it rewrites (`+contextual`).
            let proof = super::super::doc::Proof::By(Tactic::Seq(vec![
                t::name_h(old),
                t::simp_only(guard.is_some(), None, rules, Some(t::at_h(false))),
                t::exact_mod_cast(t::hyp("h")),
            ]));
            match says {
                Some(says) => super::conversions::shown(says, proof),
                None => t::by_term(proof),
            }
        };
        let in_a_set = |node: &Node| {
            node.walk().iter().any(|n| {
                matches!((n.notation(), n.children.as_slice()),
                    (MEMBERSHIP, [value, _])
                        if value.notation() == APPLICATION
                            && value.children.first().is_some_and(|g| *g.text == *function))
            })
        };
        for said in self.trees.values_mut() {
            for sentence in said.iter_mut() {
                if sentence.name.as_deref() == Some(hyp.as_str()) {
                    sentence.says = self.writer.formula(&sentence.node).built();
                    sentence.proof = given.clone();
                    sentence.name = None;
                    continue;
                }
                let names_it = sentence
                    .node
                    .walk()
                    .iter()
                    .any(|n| n.is_name() && *n.text == *function);
                if !names_it {
                    continue;
                }
                sentence.says = self.writer.formula(&sentence.node).built();
                let witnessed = in_a_set(&sentence.node);
                sentence.proof =
                    carried(&sentence.proof, sentence.says.clone(), witnessed);
                sentence.name = None;
            }
        }
        let says = self.writer.formula(&restated.said).built()?;
        let define_hyp = line_name(&restated.label);
        let name = format!("{define_hyp}_{}", own);
        // fun x h => (s5_eq x h).trans (by simp only [hD3])
        let mut at_member = applied_to(t::hyp(&equation), a());
        let mut bound = vec![letter.as_str()];
        if guard.is_some() {
            at_member = applied_to(at_member, h());
            bound.push("h");
        }
        let unfolded = t::by_term(super::super::doc::Proof::By(t::simp_only(
            false,
            None,
            vec![t::forwards(t::hyp(&define_hyp))],
            None,
        )));
        let proof = super::super::doc::Proof::Term(untyped_lambda(
            &bound,
            applied_to(projected(at_member, &["trans"]), unfolded),
        ));
        self.push_at(
            depth,
            Tactic::Have {
                name: name.clone(),
                says,
                proof: Box::new(proof),
            },
            at,
            Spot::Statement,
        );
        self.named
            .insert(restated.label.clone(), vec![name.clone()]);
        self.witnessed.insert(restated.label.clone());
        self.trees.insert(
            restated.label,
            vec![LineSentence::only(restated.said, name)],
        );
        Some(())
    }

    /// The define of `function`, its label and its equation said at every
    /// member of its domain, `for all x ∈ ℚ, g(x) = 2^|numer(x)|·…`, as a
    /// tree, for `narrowed_function`. None for a function no define of the
    /// theorem gives by one argument.
    fn define_restated(&self, function: &str) -> Option<DefineEquation> {
        let line = self.thm.defines.iter().find(|d| {
            matches!(corpus::define_parts(&d.text),
                Route::Built(DefineParts::One(def)) if def.name == function)
        })?;
        let Route::Built(DefineParts::One(def)) = corpus::define_parts(&line.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let FunctionRead { domain, body } =
            self.function_read(line.line, &param.name).built()?;
        let g = &self.sources.checked.grammar;
        let a_node =
            Node::name(domain.sort.held().unwrap_or_else(Sort::none), &param.name);
        let f_node = Node::name(Sort::of("function"), function);
        let f_a = page::made_as(g, "_(_)", vec![f_node, a_node.clone()])?;
        let equation = Node::of(EQUALS, Sort::of("formula"), vec![f_a, body]);
        let said =
            page::made_as(g, "for all _ ∈ _, _", vec![a_node, domain, equation])?;
        Some(DefineEquation {
            label: line.label.clone(),
            said,
        })
    }

    /// The functions step `i` narrows, each a define's whose values a
    /// sentence of the step puts among numbers narrower than Lean computes
    /// them in (`CheckedTheorem::define_values`), declared after the step
    /// from the sentence that says so (`narrowed_function`). `said` is each
    /// sentence's `have`, by its name. A function already of those numbers
    /// is not narrowed again.
    pub(super) fn narrow_at_step(
        &mut self,
        i: usize,
        said: &[(String, Printed)],
        at: usize,
        depth: usize,
    ) {
        let narrowing: Vec<(String, super::super::templates::Num)> = self
            .rec
            .define_values
            .iter()
            .flat_map(|(name, values)| {
                values.iter().filter(|v| v.step == i).map(|v| {
                    let narrow = super::super::expr::recorded_set_type(v.system);
                    (name.clone(), narrow)
                })
            })
            .collect();
        for (name, narrow) in narrowing {
            let Some(LetterType::Function { from, to }) =
                self.writer.letters.get(&name).cloned()
            else {
                continue;
            };
            if narrow >= to {
                continue;
            }
            for (hyp, says) in said {
                let narrowing = Narrowing {
                    function: name.clone(),
                    from,
                    to: narrow,
                    hyp: hyp.clone(),
                };
                if self.narrowed_function(narrowing, says, at, depth).is_some() {
                    break;
                }
            }
        }
    }

    /// Put back what each narrowing written deeper than `depth` changed,
    /// where the block it stands in ends: outside it the function is the
    /// define's again.
    pub(super) fn narrowings_ended(&mut self, depth: usize) {
        while self.narrowings.last().is_some_and(|n| n.depth > depth) {
            let Some(undo) = self.narrowings.pop() else {
                return;
            };
            match undo.letter {
                Some(ty) => self.writer.letters.insert(undo.function, ty),
                None => self.writer.letters.shift_remove(&undo.function),
            };
            match undo.tree {
                Some(tree) => self.trees.insert(undo.label.clone(), tree),
                None => self.trees.shift_remove(&undo.label),
            };
            match undo.named {
                Some(named) => self.named.insert(undo.label.clone(), named),
                None => self.named.shift_remove(&undo.label),
            };
            if !undo.witnessed {
                self.witnessed.remove(&undo.label);
            }
        }
    }

    /// The widest numbers a line of the page gives a define's function as
    /// its type, as Lean types them (`CheckedTheorem::define_values`): ℚ of
    /// `f : ℕ → ℚ`, where Lean needs the function itself of those numbers.
    /// A line saying its values are among wider numbers, `L(k) ∈ ℝ` of
    /// rational values, is a fact of them, which a cast reaches. None where
    /// no line gives a type.
    pub(super) fn values_said_widest(
        &self,
        name: &str,
    ) -> Option<super::super::templates::Num> {
        self.rec
            .define_values
            .get(name)?
            .iter()
            .filter(|said| said.typed)
            .map(|said| super::super::expr::recorded_set_type(said.system))
            .max()
    }

    /// Whether a define's value at its argument, an integer, is a thing, a
    /// member of a set of things: e(i) of `e : {1, …, n} → E`.
    fn thing_valued(&self, param: &str, body: &Node) -> bool {
        let mut letters = self.writer.letters.clone();
        letters.insert(
            param.to_string(),
            LetterType::Number(super::super::templates::Num::Int),
        );
        matches!(
            self.writer.with_letters(letters).member_kind(body),
            Some(super::super::expr::Members::Things(_))
        )
    }

    /// A define of a function of one number in a proof, `let S(m) =
    /// Σ(j = 1 to m) 3^j, for m ∈ ℕ`: Lean's `set` of a function from the
    /// type of the set its argument runs over to the least type holding its
    /// value, whose hypothesis, named by the label, a step citing the define
    /// unfolds it by (`written_out`).
    pub(super) fn define_function(
        &mut self,
        d: usize,
        def: &Define,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let [param] = def.params.as_slice() else {
            return Route::no("a define of a function of more than one argument");
        };
        let FunctionRead { domain, body } =
            match self.function_read(line.line, &param.name) {
                Route::Built(read) => read,
                Route::Declined(d) => return Route::Declined(d),
            };
        // A function whose values are sets, I(k) = {|x| : x ∈ 𝒫{1, …, k}},
        // or pairs, f(i) = (L(i), M(i)), or things, g(i) = e(i) of a walk's
        // edges: a map from its domain's members to sets of the value's
        // members, to pairs, or to things.
        if set_valued(self.rec, &def.name)
            || super::terms::pair_valued(self.rec, &def.name)
            || self.thing_valued(&param.name, &body)
        {
            let from = match (
                super::super::expr::system_of(&domain),
                self.writer.set_members(&domain),
            ) {
                (Some(system), _) => super::super::expr::Members::Numbers(
                    super::super::expr::letter_type(system)
                        .max(super::super::templates::Num::Int),
                ),
                (None, _) if domain.notation() == INTEGER_RANGE => {
                    super::super::expr::Members::Numbers(
                        super::super::templates::Num::Int,
                    )
                }
                (None, Some(m)) => m,
                (None, None) => return Route::no(SET_VALUED),
            };
            return self.define_map(d, def, from, FunctionRead { domain, body }, depth);
        }
        let (domain, body) = (&domain, &body);
        // A function on ℕ, ℕ₀ or a range {0, …, m} takes integers, as the
        // writer's sequences do, so that q(j) of a sum's index is written
        // as it stands; its values off the range are none of the page's.
        let from = match (
            super::super::expr::system_of(domain),
            self.writer.set_members(domain),
        ) {
            (Some(system), _) => super::super::expr::letter_type(system)
                .max(super::super::templates::Num::Int),
            (None, _) if domain.notation() == INTEGER_RANGE => {
                super::super::templates::Num::Int
            }
            (None, Some(super::super::expr::Members::Numbers(n))) => {
                n.max(super::super::templates::Num::Int)
            }
            // On a set of other members, a subgroup's elements: a map on
            // their type.
            (None, Some(members)) => {
                let read = FunctionRead {
                    domain: domain.clone(),
                    body: body.clone(),
                };
                return self.define_map(d, def, members, read, depth);
            }
            (None, None) => {
                return Route::no(
                    "a define of a function on a set Lean has no type for",
                )
            }
        };
        // The value is read with the argument a number of that type, in ℕ
        // or ℕ₀ where the domain or range puts it, 10^k of k ∈ ℕ₀ written as
        // the steps write it; the argument is no letter of the proof's
        // after it.
        let system = match super::super::expr::system_of(domain) {
            Some(s) => Some(s),
            None if domain.notation() == INTEGER_RANGE => {
                Some(super::super::expr::range_letter_system(domain))
            }
            None => None,
        };
        let whole_before = self.writer.wholes.get(&param.name).copied();
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), LetterType::Number(from));
        if let Some(s) = system {
            self.writer.introduce(&param.name, s);
        }
        // The widest numbers a line of the page puts the values among
        // (`CheckedTheorem::define_values`).
        let widest = self.values_said_widest(&def.name);
        // Of a real or complex argument, values of that type at least, as a
        // header function's are (`header_function`); of wider numbers a line
        // says, values of those, `fun n => (n : ℚ)` of `f(n) = n` and `f : ℕ
        // → ℚ`.
        let value = match self.writer.carrier(body) {
            Route::Built(to) => {
                let to = match from >= super::super::templates::Num::Real {
                    true => to.max(from),
                    false => to,
                };
                let to = widest.map_or(to, |w| to.max(w));
                self.writer.number_fixed(body, to).map(|v| (to, v))
            }
            Route::Declined(why) => Route::Declined(why),
        };
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        match whole_before {
            Some(s) => self.writer.wholes.insert(param.name.clone(), s),
            None => self.writer.wholes.shift_remove(&param.name),
        };
        let (to, value) = match value {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        let name = super::super::names::letter(&def.name);
        let label = line_name(&line.label);
        let function = LetterType::Function { from, to }.lean_type();
        // A lambda term, which the writer's comparisons apply where the
        // letter stands applied, as `simp only [hD]` does
        // (`forms::alike_once_set`).
        let lambda = Printed {
            kind: super::super::doc::TermKind::Quantified {
                quant: super::super::doc::term::Quant::Fun,
                letter: super::super::names::letter(&param.name),
                letter_ty: LetterType::Number(from).lean_type(),
                guard: None,
                body: Box::new(value),
                bounded: false,
            },
            ty: Some(function.clone()),
        };
        self.push_at(
            depth,
            Tactic::Set {
                name: name.clone(),
                ty: function,
                value: lambda,
                with: label.clone(),
            },
            line.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Function { from, to });
        // Of real or complex numbers on a set, [0, 1]: its domain, within
        // which its limits and derivatives are taken (`domain_of`), as a
        // header function's is.
        let whole = matches!(
            super::super::expr::system_of(domain),
            Some(super::super::expr::System::Type(_))
        );
        if !whole && from >= super::super::templates::Num::Real {
            match self.writer.numbers_at(domain, from) {
                Route::Built(p) => {
                    self.writer.domains.insert(def.name.clone(), p);
                }
                Route::Declined(why) => return Route::Declined(why),
            }
        }
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define of a function on a set of members other than numbers, `let
    /// t(c) = g·c, for c ∈ H` of a subgroup H: Lean's `set` of a map from
    /// the members' type to the value's, `set t : G → G := fun c => g * c`,
    /// as a function the header lets on such a set is (`header_function`).
    /// Its domain is the set, within which the page applies it.
    pub(super) fn define_map(
        &mut self,
        d: usize,
        def: &Define,
        from: super::super::expr::Members,
        read: FunctionRead,
        depth: usize,
    ) -> Route<()> {
        let line = &self.thm.defines[d];
        let Some(param) = def.params.first() else {
            return Route::no("a define of a map of no argument");
        };
        let FunctionRead { domain, body } = read;
        let before = self
            .writer
            .letters
            .insert(param.name.clone(), from.letter());
        // Its value a member of a set, g·c, or a set itself, {|x| : x ∈
        // 𝒫{1, …, k}}, of the set's members' type.
        let to = self.writer.member_kind(&body).or_else(|| {
            self.writer
                .members_of(&body)
                .map(|m| super::super::expr::Members::Sets(Box::new(m)))
        });
        let value = match to {
            Some(to) => self.writer.set_term(&body).map(|v| (to, v)),
            None => Route::no(
                "a define of a map whose value is no member Lean has a type for",
            ),
        };
        match before {
            Some(ty) => self.writer.letters.insert(param.name.clone(), ty),
            None => self.writer.letters.shift_remove(&param.name),
        };
        let (to, value) = match value {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        let name = super::super::names::letter(&def.name);
        let label = line_name(&line.label);
        let ty = LetterType::Map {
            from: from.clone(),
            to,
        };
        let function = ty.lean_type();
        let lambda = Printed {
            kind: super::super::doc::TermKind::Quantified {
                quant: super::super::doc::term::Quant::Fun,
                letter: super::super::names::letter(&param.name),
                letter_ty: from.member_type(),
                guard: None,
                body: Box::new(value),
                bounded: false,
            },
            ty: Some(function.clone()),
        };
        self.push_at(
            depth,
            Tactic::Set {
                name,
                ty: function,
                value: lambda,
                with: label.clone(),
            },
            line.line,
            Spot::Statement,
        );
        self.writer.letters.insert(def.name.clone(), ty);
        if let Route::Built(set) = self.writer.set_term(&domain) {
            self.writer.domains.insert(def.name.clone(), set);
        }
        self.named.insert(line.label.clone(), vec![label]);
        Route::Built(())
    }

    /// A define of the theorem's file, outside the theorem, that its
    /// statement is read with: Lean's `set`, of the least type holding the
    /// term it names, its equation named by the name.
    pub(super) fn define_outside(&mut self, name: &str, body: &Node) -> Route<()> {
        // A set it names, B = {1, 2}: the set, of the type its members give.
        if let Some(members) = self.writer.members_of(body) {
            let value = match self.writer.set_term(body) {
                Route::Built(v) => v,
                Route::Declined(d) => return Route::Declined(d),
            };
            let lean = super::super::names::letter(name);
            let ty = LetterType::Set(members);
            self.push_at(
                1,
                Tactic::Set {
                    name: lean.clone(),
                    ty: ty.lean_type(),
                    value,
                    with: format!("h_{lean}"),
                },
                self.thm.line,
                Spot::Statement,
            );
            self.writer.letters.insert(name.to_string(), ty);
            return Route::Built(());
        }
        let ty = match self.writer.carrier(body) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let value = match self.writer.number_fixed(body, ty) {
            Route::Built(v) => v,
            Route::Declined(d) => return Route::Declined(d),
        };
        let lean = super::super::names::letter(name);
        let line = self.thm.line;
        self.push_at(
            1,
            Tactic::Set {
                name: lean.clone(),
                ty: self.writer.num_type(ty),
                value,
                with: format!("h_{lean}"),
            },
            line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(name.to_string(), LetterType::Number(ty));
        Route::Built(())
    }

    /// `exhibit`: the claim's "there is", with the values the checker read
    /// for its letters, and what it says of them by the lines the checker
    /// found to state it (`Exhibit::shown`); declined where none does.
    pub(super) fn exhibit(
        &self,
        just: &Justification,
        node: &Node,
    ) -> Route<super::super::doc::Proof> {
        let Some(exhibit) = self
            .rec
            .exhibited
            .get(&just.line)
            .and_then(|all| all.iter().flatten().next())
        else {
            return Route::no("an exhibit the checker read no values for");
        };
        let binding = &exhibit.values;
        // The facts asked of the values, in the checker's order: each
        // letter's membership, then the body's parts.
        let mut shown = exhibit.shown.iter().peekable();
        // there is a ∈ X with nothing said of a, `∃ a ∈ X, True`: the
        // member, that it is in X, and nothing.
        if let (THERE_IS_SOME, [letter, set]) =
            (node.notation(), node.children.as_slice())
        {
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let Some(members) = self.writer.set_members(set) else {
                return Route::no("there is some member of a set with no Lean type");
            };
            // That the value is in X, from the record's first fact.
            let membership = page::made_as(
                self.writer.grammar,
                "_ ∈ _",
                vec![value.clone(), set.clone()],
            );
            let wanted = membership.and_then(|m| self.writer.formula(&m).built());
            let Some(in_set) = self.fact_shown(wanted.as_ref(), &[], shown.next())
            else {
                return Route::no(UNSHOWN_FACT);
            };
            return self.writer.element_term(value, &members).map(|v| {
                let nothing = Printed::constant(
                    "trivial",
                    super::super::doc::Source::Core,
                    super::super::doc::LeanType::Prop,
                );
                super::super::doc::Proof::Term(super::super::expr::anonymous(vec![
                    v, in_set, nothing,
                ]))
            });
        }
        let mut parts = Vec::new();
        let mut known = Vec::new();
        let mut body = node;
        // The claim as Lean has it, each "there is" given its value in turn:
        // what each fact about the values says there.
        let mut lean_body = self.writer.formula(node).built();
        while body.notation() == THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let membership = shown.next();
            // A member of a set: the value as the writer writes a member,
            // and its membership by the line that says it.
            if let Some(members) = self.writer.members_of(set) {
                let term = match self.writer.element_term(value, &members) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let (guard, next) = exists_at(lean_body.as_ref(), &term);
                parts.push(term);
                let Some(fact) = self.fact_shown(guard.as_ref(), &known, membership)
                else {
                    return Route::no(UNSHOWN_FACT);
                };
                parts.push(fact);
                lean_body = next;
                body = inner;
                continue;
            }
            // A polynomial: the function, and that it is one; a function
            // between sets of numbers: the function, of the types the
            // quantifier gives it, and that it maps the one set into the
            // other. Lean states the one or the other first in what the
            // "there is" says, `∃ q, q ∈ polynomials ∧ …`, `∃ f, Set.MapsTo
            // f A B ∧ …`, proved where the checker found it stated.
            let function = match (set.notation(), set.children.as_slice()) {
                (POLYNOMIALS, _) => Some(self.writer.set_term(value)),
                (FUNCTIONS_FROM, [from, to]) => {
                    Some(self.function_given(&self.writer, value, from, to))
                }
                _ => None,
            };
            if let Some(function) = function {
                let p = match function {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let (asked, rest) = match exists_at(lean_body.as_ref(), &p) {
                    (Some(guard), next) => (Some(guard), next),
                    (None, Some(next)) => match and_sides(&next) {
                        Some((first, rest)) => (Some(first), Some(rest)),
                        None => (None, Some(next)),
                    },
                    (None, None) => (None, None),
                };
                parts.push(p);
                let Some(fact) = self.fact_shown(asked.as_ref(), &known, membership)
                else {
                    return Route::no(UNSHOWN_FACT);
                };
                parts.push(fact);
                lean_body = rest;
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == INTEGER_RANGE {
                (super::super::templates::Num::Int, true)
            } else {
                match super::super::expr::system_of(set) {
                    Some(s) => (
                        super::super::expr::letter_type(s),
                        !matches!(s, super::super::expr::System::Type(_)),
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            let (guard, next) = match self.witness(value, ty) {
                Route::Built(w) => {
                    let at = exists_at(lean_body.as_ref(), &w.term);
                    parts.push(w.term);
                    known.extend(w.known);
                    at
                }
                Route::Declined(d) => return Route::Declined(d),
            };
            if guarded {
                let Some(fact) = self.fact_shown(guard.as_ref(), &known, membership)
                else {
                    return Route::no(UNSHOWN_FACT);
                };
                parts.push(fact);
            }
            lean_body = next;
            body = inner;
        }
        if parts.is_empty() {
            return Route::no("an exhibit of no \"there is\"");
        }
        let Some(facts) =
            self.facts_shown(body, lean_body.as_ref(), &known, &mut shown)
        else {
            return Route::no(UNSHOWN_FACT);
        };
        parts.push(facts);
        Route::Built(super::super::doc::Proof::Term(
            super::super::expr::anonymous(parts),
        ))
    }

    /// What proves a fact an exhibit says of its values, `wanted` as Lean
    /// has it where it is known, from where the checker found it stated
    /// (`shown`), after the tactics `known` that put a witness's facts in
    /// scope; None where no line states it.
    pub(super) fn fact_shown(
        &self,
        wanted: Option<&Printed>,
        known: &[Tactic],
        shown: Option<&Supplied>,
    ) -> Option<Printed> {
        let (wanted, shown) = (wanted?, shown?);
        match self
            .supplied_proof(&shown.by, wanted, shown.meeting.as_ref())
            .built()
        {
            Some(p) => Some(after_known(known, p)),
            None => self.with_known(&shown.by, wanted, known),
        }
    }

    /// The facts an exhibit says of its values, `said`, taken apart as Lean
    /// nests its "and", each proved as `fact_shown` proves it: `wanted` is
    /// the same as Lean has it, where it is known, and `shown` gives where
    /// each part stands, in order. A statement the record holds as its one
    /// last entry, a phrase whose meaning is an "and", `{v} is a clique of
    /// size at least 1`, is proved whole.
    pub(super) fn facts_shown<'s, I: Iterator<Item = &'s Supplied> + Clone>(
        &self,
        said: &Node,
        wanted: Option<&Printed>,
        known: &[Tactic],
        shown: &mut Peekable<I>,
    ) -> Option<Printed> {
        // One entry left for all `said` says: the record holds it whole.
        let whole = shown.clone().count() == 1;
        match self.writer.and_sides(said).filter(|_| !whole) {
            Some((l, r)) => {
                let (wl, wr) = match wanted.and_then(and_sides) {
                    Some((a, b)) => (Some(a), Some(b)),
                    None => (None, None),
                };
                let left = self.facts_shown(l, wl.as_ref(), known, shown)?;
                let right = self.facts_shown(r, wr.as_ref(), known, shown)?;
                Some(super::super::expr::anonymous(vec![left, right]))
            }
            _ => self.fact_shown(wanted, known, shown.next()),
        }
    }

    /// The claim sentence `node` of the step whose reason is on `line`, as
    /// the step's `have` states it (`claimed_all`): what Lean's goal for it
    /// is, a claim of numerals alone in the type of the lines it is reached
    /// from, a claim of counts in the form the step writes its counts in.
    /// None for a sentence no step's `have` states, a calculation's row.
    /// The claim as a line of the proof states it, where one does: a
    /// calculation's row as the calculation states it (`row_stated`), its
    /// counts in the form the rows take them; outside a calculation and a
    /// witness, the step's `have` (`stated_claim`), its counts in the form
    /// the step writes them. Inside a witness's `refine` the goal is what
    /// the claim says of the witness, which no line states (`in_witness`).
    pub(super) fn stated_form(&self, line: usize, node: &Node) -> Option<Printed> {
        let relation = node.notation() == EQUALITY || node.notation() == ORDER;
        if let Some(row) = self.row_stated.borrow().clone().filter(|_| relation) {
            return Some(row);
        }
        if self.worked_in.get().is_some() || self.in_witness.get() {
            return None;
        }
        self.stated_claim(line, node)
    }

    /// The claim a step's proof is met with, as Lean states it: as a line
    /// states it (`stated_form`); else a relation of numbers in a
    /// calculation's type, told that type (`Writer::closed_formula`); else as
    /// the writer writes it.
    pub(super) fn claim_as_stated(&self, line: usize, node: &Node) -> Option<Printed> {
        if let Some(stated) = self.stated_form(line, node) {
            return Some(stated);
        }
        let relation = node.notation() == EQUALITY || node.notation() == ORDER;
        let of_numbers = node.children.iter().all(|c| self.writer.is_number(c));
        match self.worked_in.get() {
            Some(at) if relation && of_numbers => {
                self.writer.closed_formula(node, at).built()
            }
            _ => self.writer.formula(node).built(),
        }
    }

    pub(super) fn stated_claim(&self, line: usize, node: &Node) -> Option<Printed> {
        self.thm
            .steps
            .iter()
            .find(|s| s.just.line == line)
            .and_then(|step| self.claimed_all(step).built())
            .and_then(|all| all.into_iter().find(|(_, n, _)| n.same(node)))
            .map(|(_, _, printed)| printed)
    }

    /// Every set the claim counts, and the item at the citation's values
    /// counts, written from its page formula with why it is finite
    /// (`finite_proof`); a set not shown finite is left out.
    pub(super) fn finite_counted(
        &self,
        cited: &Cited,
        sentence: &Sentence,
        claim: &Node,
    ) -> Vec<ShownFinite> {
        let item = self.at_values(&sentence.says, &cited.binding);
        self.counted_sets(&[claim, &item])
            .iter()
            .filter_map(|set| self.shown_finite(set))
            .collect()
    }

    /// Each set the formulas count, once.
    pub(super) fn counted_sets(&self, formulas: &[&Node]) -> Vec<Node> {
        let mut seen: Vec<Node> = Vec::new();
        for set in formulas
            .iter()
            .flat_map(|n| n.walk())
            .filter(|c| c.notation() == CARDINALITY)
            .filter_map(|c| c.children.first().cloned())
        {
            if !seen
                .iter()
                .any(|s| matching::alike_top(s, &set, self.sources.ctx))
            {
                seen.push(set);
            }
        }
        seen
    }

    /// The set written from its page formula with why it is finite
    /// (`finite_proof`); None where it is not shown finite.
    pub(super) fn shown_finite(&self, set: &Node) -> Option<ShownFinite> {
        Some(ShownFinite {
            set: self.writer.set_term(set).built()?,
            proof: self.finite_proof(set)?,
        })
    }

    /// The proof of a hypothesis of a cited item from what the checker
    /// found supplies it (`Supplied`), `wanted` as Lean asks it at the
    /// citation's values: a count equal to itself, which the values make
    /// true (`count_itself`); a count Lean asks in ℕ∞ of a line that counts
    /// in ℤ (`counted_across`); any other as a line that supplies a fact is
    /// met (`supplied_proof`).
    pub(super) fn supplied_hypothesis(
        &self,
        s: &Supplied,
        wanted: &Printed,
        binding: &Binding,
    ) -> Route<Printed> {
        let at_values = || self.at_values(&s.want, binding);
        // A line's "for all" over a set holding the one asked.
        if let Some(n) = &s.narrowed {
            let proof = match self.line_proof(&s.by) {
                Route::Built((proof, _)) => proof,
                Route::Declined(d) => return Route::Declined(d),
            };
            return match narrowed_proof(n, proof, wanted) {
                Some(p) => Route::Built(p),
                None => {
                    Route::no("a narrowed line whose sets no row of the table relates")
                }
            };
        }
        match &s.by {
            // A count equal to itself, which Lean writes in two forms.
            SuppliedBy::Identity(_) | SuppliedBy::Unstated
                if wanted.has_count(Extended) =>
            {
                match self.count_itself(&at_values()) {
                    Some(p) => Route::Built(p),
                    None => {
                        Route::no("a count equal to itself of a set not shown finite")
                    }
                }
            }
            SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at)
                if wanted.has_count(Extended) =>
            {
                let (proof, says) = match self.line_says(at) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                if let Some(met) = self.count_values(at, &proof, &says, wanted) {
                    return met;
                }
                if !says.has_count(Natural) {
                    return self.supplied_proof(&s.by, wanted, s.meeting.as_ref());
                }
                match self.counted_across(proof, wanted, &at_values()) {
                    Some(p) => Route::Built(p),
                    None => Route::no("a count in ℕ∞ of a set not shown finite"),
                }
            }
            _ => match self.counts_apart(&s.by, wanted) {
                Some(met) => met,
                None => match self.supplied_proof(&s.by, wanted, s.meeting.as_ref()) {
                    Route::Built(p) => Route::Built(p),
                    // A line whose powers Lean writes as integer powers, `2 ^
                    // abs (Rat.num x)`, for a hypothesis that writes them to
                    // their exponents' `toNat`, each exponent at least 0 as
                    // the record shows (`powers_converted_at`).
                    Route::Declined(d) => {
                        match self.powers_supplied(s, wanted, binding) {
                            Some(p) => Route::Built(p),
                            None => Route::Declined(d),
                        }
                    }
                },
            },
        }
    }

    /// The proof of `wanted`, a cited item's hypothesis, from the line that
    /// supplies it where the two are apart only in powers one writes as
    /// integer powers and the other to their exponents' `toNat`, and in casts
    /// (`powers_converted_at`). None of any other two.
    fn powers_supplied(
        &self,
        s: &Supplied,
        wanted: &Printed,
        binding: &Binding,
    ) -> Option<Printed> {
        let (SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at)) = &s.by else {
            return None;
        };
        let (proof, says) = self.line_says(at).built()?;
        let asked = self.at_values(&s.want, binding);
        self.powers_converted_at(&[&at.written, &asked], &says, wanted, &proof, false)
            .map(super::super::tactics::by_term)
    }

    /// The proof of `wanted` from the line `by` names where the two count a
    /// set in different forms, one in ℕ∞ and the other in ℤ: `|X| = k + 1`
    /// assumed of a set the record shows finite only from that line on, or
    /// an instance's condition in ℕ∞ of a line in ℤ. Both are taken to the
    /// count in ℕ (`counted_between`). None where the line is no line, or
    /// the two count alike.
    pub(super) fn counts_apart(
        &self,
        by: &SuppliedBy,
        wanted: &Printed,
    ) -> Option<Route<Printed>> {
        let (SuppliedBy::Line(at) | SuppliedBy::SaidOnce(at)) = by else {
            return None;
        };
        let (proof, says) = self.line_says(at).built()?;
        let apart = (wanted.has_count(Extended) && says.has_count(Natural))
            || (wanted.has_count(Natural) && says.has_count(Extended));
        if !apart {
            return None;
        }
        if let Some(met) = self.count_values(at, &proof, &says, wanted) {
            return Some(met);
        }
        Some(
            match self.counted_between(&proof, &says, wanted, &[&at.written]) {
                Some(p) => Route::Built(p),
                None => Route::no("a count in ℕ∞ of a set not shown finite"),
            },
        )
    }

    /// The proof of `wanted` from `proof` of the line at `at`, which `says`,
    /// where the two are one count equal to a value in ℕ₀, in ℕ∞ in the one
    /// and in ℤ in the other (`count_value_shape`): met by the count's
    /// definition one way (`count_value_met`), and by the set's finiteness
    /// the other (`count_value_made`). None where they are not such a pair.
    pub(super) fn count_values(
        &self,
        at: &FirstAt,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Route<Printed>> {
        let (EQUALITY, [count, value]) =
            (at.written.notation(), at.written.children.as_slice())
        else {
            return None;
        };
        // A count said as some natural number, asked in ℕ∞ at the value.
        if let Some(p) = super::orders::witness_to_value(proof, says, wanted) {
            return Some(Route::Built(super::super::tactics::by_term(p)));
        }
        if super::orders::count_value_shape(says, wanted).is_some() {
            return Some(match self.count_value_met(value, proof, says, wanted) {
                Some(p) => Route::Built(super::super::tactics::by_term(p)),
                None => Route::no("a count's value not shown at 0 or above"),
            });
        }
        let (Some(()), [set]) = (
            super::orders::count_value_shape(wanted, says),
            count.children.as_slice(),
        ) else {
            return None;
        };
        Some(match self.count_value_made(set, proof, says, wanted) {
            Some(p) => Route::Built(super::super::tactics::by_term(p)),
            None => Route::no("a count in ℕ∞ of a set not shown finite"),
        })
    }

    /// The proof of `wanted`, a count in ℕ∞ Lean asks, `X.encard = ((0 : ℕ)
    /// : ℕ∞)`, from `proof` of a line that counts the same sets in ℤ,
    /// `(X.ncard : ℤ) = 0`, each set `at_values` counts that `wanted` counts
    /// in ℕ∞ finite by why the record says it is: each such count taken to
    /// its count in ℕ (`Set.Finite.cast_ncard_eq`), and the two then met
    /// across their casts (`exact_mod_cast`). None where such a set is not
    /// shown finite.
    pub(super) fn counted_across(
        &self,
        proof: Printed,
        wanted: &Printed,
        at_values: &Node,
    ) -> Option<Printed> {
        let in_extended = |written: &Printed| {
            wanted.walk().iter().any(|c| {
                matches!(&c.kind, TermKind::Count { set, form: CountForm::Extended }
                    if set.untyped() == written.untyped())
            })
        };
        if let Some(each) = self.counted_across_each(proof.clone(), wanted, at_values) {
            return Some(each);
        }
        let mut rules = Vec::new();
        for set in self.counted_sets(&[at_values]) {
            // A set the writer does not write as the page does, one a define
            // of the file names, written out, is no count Lean asks in ℕ∞.
            let Route::Built(written) = self.writer.set_term(&set) else {
                continue;
            };
            if in_extended(&written) {
                rules.push(t::backwards(cast_ncard_eq(&self.shown_finite(&set)?)));
            }
        }
        Some(t::by_term(super::super::doc::Proof::By(t::on_h(
            &proof,
            vec![
                t::call("rw", vec![TacticArg::Rules(rules)]),
                // The goal's counts now the line's, apart only in casts.
                t::exact_mod_cast(t::hyp("h")),
            ],
        ))))
    }

    /// `counted_across` of a "for all y ∈ S" Lean asks, `∀ Y ∈ K, Y.encard
    /// = …` of a line `∀ Y ∈ K, (Y.ncard : ℤ) = …`: at each member, the
    /// counts taken across there, y finite as a member of S
    /// (`member_finite`) and any other set as the record says, and a
    /// natural count Lean writes as `(n : ℤ).toNat` read as n
    /// (`Int.toNat_natCast`). None where `wanted` is no such "for all", or
    /// a set it counts in ℕ∞ is not shown finite.
    fn counted_across_each(
        &self,
        proof: Printed,
        wanted: &Printed,
        at_values: &Node,
    ) -> Option<Printed> {
        let TermKind::Quantified {
            quant: Quant::ForAll,
            letter,
            guard: Some(_),
            body,
            ..
        } = &bare_term(wanted).kind
        else {
            return None;
        };
        let (FOR_ALL, [bound, set, inner]) =
            (at_values.notation(), at_values.children.as_slice())
        else {
            return None;
        };
        // The member's type as the citing proof has it, `Set G` of a member
        // of K : Set (Set G), not the item's own.
        let member_ty = self.writer.members_of(set)?.letter().lean_type();
        let member = "h_mem";
        let in_extended = |written: &Printed| {
            body.walk().iter().any(|c| {
                matches!(&c.kind, TermKind::Count { set, form: CountForm::Extended }
                    if set.untyped() == written.untyped())
            })
        };
        let mut rules = Vec::new();
        for counted in self.counted_sets(&[inner]) {
            if counted.is_name() && counted.text == bound.text {
                let shown = ShownFinite {
                    set: Printed::letter(letter, member_ty.clone()),
                    proof: self.member_finite(set, t::hyp(member))?,
                };
                rules.push(t::backwards(cast_ncard_eq(&shown)));
                continue;
            }
            let Route::Built(written) = self.writer.set_term(&counted) else {
                continue;
            };
            if in_extended(&written) {
                rules.push(t::backwards(cast_ncard_eq(&self.shown_finite(&counted)?)));
            }
        }
        if rules.is_empty() {
            return None;
        }
        let to_nat_of_cast = body.walk().iter().any(|n| {
            let TermKind::ToNat(inner) = &n.kind else {
                return false;
            };
            let mut inner = &**inner;
            while let TermKind::Paren(within) = &inner.kind {
                inner = within;
            }
            matches!(inner.kind, TermKind::Cast { .. })
        });
        if to_nat_of_cast {
            rules.push(t::forwards(t::lemma("Int.toNat_natCast")));
        }
        let at_member = applied_to(applied_to(proof, t::hyp(letter)), t::hyp(member));
        Some(untyped_lambda(
            &[letter.as_str(), member],
            t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
                t::simp_only(false, None, rules, None),
                t::exact_mod_cast(at_member),
            ]))),
        ))
    }

    /// That a member of `set` is finite, from `member`, the proof of its
    /// membership: of 𝒫A, a part of A, `(p : A.Finite).subset h`; of a set
    /// built from 𝒫A, {X ⊆ A : P(X)}, the same of `h.1`; of a define's name,
    /// as of its value. None for any other set, or an A not shown finite.
    pub(super) fn member_finite(&self, set: &Node, member: Printed) -> Option<Printed> {
        let value = match set.is_name() {
            true => self.define_value_tree(&set.text)?,
            false => set.clone(),
        };
        let (whole, member) = match (value.notation(), value.children.as_slice()) {
            (POWERSET, [a]) => (a.clone(), member),
            (SET_BUILDER, [_, of, _]) if of.notation() == POWERSET => {
                (of.children.first()?.clone(), projected(member, &["1"]))
            }
            _ => return None,
        };
        let whole_finite = self.finite_proof(&whole)?;
        Some(applied_to(
            projected(super::super::tactics::bracket(whole_finite), &["subset"]),
            member,
        ))
    }

    /// The value a define of no argument names, as the checker read its
    /// rule; None where no such define names `name`, or its rule did not
    /// read.
    fn define_value_tree(&self, name: &str) -> Option<Node> {
        self.thm.defines.iter().find_map(|d| {
            let Route::Built(DefineParts::One(one)) = corpus::define_parts(&d.text)
            else {
                return None;
            };
            (one.name == name && one.params.is_empty())
                .then(|| super::headers::rule_tree(&one.body, d, self.rec))
                .flatten()
        })
    }

    /// The proof of `wanted` from `proof` of `says` where one of the two
    /// counts a set in ℕ∞ that the other counts in ℤ, an assumption
    /// `V.encard = 2` for a row `(V.ncard : ℤ) = 2`: each set the terms
    /// `nodes` count that either counts in ℕ∞, shown finite as the record
    /// says, taken to its count in ℕ in the line and the goal alike
    /// (`Set.Finite.cast_ncard_eq`), and the two then met across their
    /// casts (`exact_mod_cast`); a set not shown finite keeps its count in
    /// ℕ∞ in both. None where no set counted in ℕ∞ is shown finite.
    pub(super) fn counted_between(
        &self,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
        nodes: &[&Node],
    ) -> Option<Printed> {
        let in_extended = |written: &Printed| {
            [says, wanted].iter().any(|s| {
                s.walk().iter().any(|c| {
                    matches!(&c.kind, TermKind::Count { set, form: CountForm::Extended }
                        if set.untyped() == written.untyped())
                })
            })
        };
        let mut rules = Vec::new();
        for set in self.counted_sets(nodes) {
            let Route::Built(written) = self.writer.set_term(&set) else {
                continue;
            };
            // A set not shown finite keeps its count in ℕ∞ in both.
            if let (true, Some(finite)) =
                (in_extended(&written), self.shown_finite(&set))
            {
                rules.push(t::backwards(cast_ncard_eq(&finite)));
            }
        }
        if rules.is_empty() {
            return None;
        }
        // Each count rewritten alike in the line and the goal, the two then
        // apart only in casts.
        Some(t::by_term(super::super::doc::Proof::By(t::on_h(
            proof,
            vec![
                t::simp_only(false, None, rules, Some(t::at_h(true))),
                t::exact_mod_cast(t::hyp("h")),
            ],
        ))))
    }

    /// The proof of a set's count equal to itself, `|A| = |A|` of an item's
    /// `|X| = m` at X := A, m := |A|, which the citation's values make true
    /// and Lean writes in two forms, the item's count in ℕ∞ and the value's
    /// in ℤ, `A.encard = (((A.ncard : ℤ).toNat : ℕ) : ℕ∞)`: one for a
    /// finite A, by why the record says it is (`finite_proof`). None where
    /// `at_values` is no such equation or A is not shown finite.
    pub(super) fn count_itself(&self, at_values: &Node) -> Option<Printed> {
        let counted = |n: &Node| match (n.notation(), n.children.as_slice()) {
            (CARDINALITY, [set]) => Some(set.clone()),
            _ => None,
        };
        let [lhs, rhs] = at_values.children.as_slice() else {
            return None;
        };
        let (set, other) = (counted(lhs)?, counted(rhs)?);
        if at_values.notation() != EQUALITY
            || !matching::alike_top(&set, &other, self.sources.ctx)
        {
            return None;
        }
        Some(t::by_term(super::super::doc::Proof::By(t::call(
            "rw",
            vec![t::rules(vec![
                t::lemma("Int.toNat_natCast"),
                cast_ncard_eq(&self.shown_finite(&set)?),
            ])],
        ))))
    }

    /// Each exponent of a power in the claim, or in the cited item at the
    /// citation's values, that the record shows at least 0, as Lean writes
    /// it with the proof (`nonneg_proof`).
    pub(super) fn exponents_shown_whole(
        &self,
        cited: &Cited,
        sentence: &Sentence,
        claim: &Node,
    ) -> Vec<NonNegative> {
        let known = self.supplied_whole(cited);
        let item = self.at_values(&sentence.says, &cited.binding);
        self.exponents_whole_in(&[claim, &item], &known)
    }

    /// A line read, `says`, met with the claim, `wanted`: alike in every form
    /// the writer chose (`forms::differences`); or apart only in a power one
    /// writes as an integer power and the other to its exponent's `toNat`,
    /// each converted as a citation's is (`forms_converted`), its exponent's
    /// fact from the record, read from the page formulas of the two,
    /// `pages`; or apart otherwise, or at an exponent with no fact.
    pub(super) fn powers_met(
        &self,
        pages: &[&Node],
        says: &Printed,
        wanted: &Printed,
        proof: &Printed,
        turned: bool,
    ) -> PowersMet {
        let templates = self.writer.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        let facing = match turned {
            true => forms::turned_statement(says),
            false => says.clone(),
        };
        if forms::differences(&facing, wanted, &widen).is_empty() {
            return PowersMet::Alike;
        }
        match self.powers_converted_at(pages, says, wanted, proof, turned) {
            Some(proof) => PowersMet::Converted(Box::new(proof)),
            None => PowersMet::Apart,
        }
    }

    /// `powers_met`'s conversion: None where the two are alike already, or
    /// apart otherwise than in such powers.
    pub(super) fn powers_converted_at(
        &self,
        pages: &[&Node],
        says: &Printed,
        wanted: &Printed,
        proof: &Printed,
        turned: bool,
    ) -> Option<super::super::doc::Proof> {
        let templates = self.writer.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        let facing = match turned {
            true => forms::turned_statement(says),
            false => says.clone(),
        };
        let found = forms::differences(&facing, wanted, &widen);
        let to_nat = |d: &forms::FormDifference| {
            matches!(d, forms::FormDifference::ToNat { .. })
        };
        if found.is_empty() || !found.iter().all(to_nat) {
            return None;
        }
        let mut zpow = forms::integer_exponents(&facing);
        zpow.extend(forms::integer_exponents(wanted));
        let whole: Vec<NonNegative> = self
            .exponents_whole_in(pages, &[])
            .into_iter()
            .filter(|w| zpow.iter().any(|e| forms::alike(e, &w.exponent)))
            .collect();
        let exponents: Vec<Printed> =
            whole.iter().map(|w| w.exponent.clone()).collect();
        let left = forms::differences(
            &forms::with_natural_powers(&facing, &exponents),
            &forms::with_natural_powers(wanted, &exponents),
            &widen,
        );
        let conversion = Conversion {
            finite: &[],
            whole: &whole,
            bound: &[],
            cast_powers: false,
            identities: &[],
            numeral_to_nat: leaves_numeral_to_nat(&facing)
                || leaves_numeral_to_nat(wanted),
        };
        (!whole.is_empty() && left.is_empty())
            .then(|| forms_converted(proof, &conversion, turned))
    }

    /// Each exponent of a power in the page formulas `pages` that the
    /// record shows at least 0, as Lean writes it, with the proof
    /// (`nonneg_proof`), `known` among the facts it is shown from.
    pub(super) fn exponents_whole_in(
        &self,
        pages: &[&Node],
        known: &[ShownWhole],
    ) -> Vec<NonNegative> {
        let ctx = self.sources.ctx;
        let mut out = Vec::new();
        let mut seen: Vec<Node> = Vec::new();
        for e in pages
            .iter()
            .flat_map(|n| n.walk())
            .filter(|n| n.notation() == POWER)
            .filter_map(|n| n.children.get(1).cloned())
        {
            if seen.iter().any(|s| matching::alike_top(s, &e, ctx)) {
                continue;
            }
            seen.push(e.clone());
            let (Route::Built(exponent), Some(proof)) = (
                self.writer
                    .number_fixed(&e, super::super::templates::Num::Int),
                self.nonneg_proof(&e, known),
            ) else {
                continue;
            };
            out.push(NonNegative { exponent, proof });
        }
        out
    }

    /// The values a citation gives the cited item's letters in ℕ or ℕ₀,
    /// each with the proof of `0 ≤ v` from where the checker found the
    /// item's hypothesis `m ∈ ℕ₀` supplied (`Cited::supplied`).
    pub(super) fn supplied_whole(&self, cited: &Cited) -> Vec<ShownWhole> {
        cited
            .supplied
            .iter()
            .filter_map(|s| {
                let at = self.at_values(&s.want, &cited.binding);
                let (value, system) = membership_of_whole(&at)?;
                let wanted = self.writer.formula(&at).built()?;
                let proof = self
                    .supplied_proof(&s.by, &wanted, s.meeting.as_ref())
                    .built()?;
                Some(ShownWhole {
                    term: value.clone(),
                    proof: nonneg_of(system, proof),
                })
            })
            .collect()
    }

    /// The proof that `e` is above 0, `0 < e`, from why the said-once walk
    /// puts it in ℕ (`citing::reason_within`), as `positive_by` writes it.
    /// None where the walk does not put e in ℕ, or gives a reason
    /// `positive_by` writes no proof for.
    pub(super) fn positive_proof(&self, e: &Node) -> Option<Printed> {
        let letters = self.writer.page_systems();
        let nonzero = |d: &Node| nonzero_said_once(d, &letters);
        let said = |_: &Node, _: rules::System| None;
        let reason = reason_within(e, rules::System::N, &letters, &nonzero, &said)?;
        let facts = match self.step_now.get() {
            Some(i) => self.step_facts(i),
            None => Vec::new(),
        };
        self.positive_by(e, &reason, &facts)
    }

    /// The proof that the integer `e` is at least 0, `0 ≤ e`, from why the
    /// said-once walk puts it in ℕ₀ (`citing::reason_within`), the walk the
    /// Metamath build proves memberships from. A part the walk does not take
    /// apart is in ℕ₀ where `known` gives it, a hypothesis of a cited item
    /// the checker found supplied, or where a line the step names says so,
    /// `i − n ∈ ℕ₀` of an `instantiate … from 2.1`. None where the walk does
    /// not put e in ℕ₀, or gives a reason `nonneg_by` writes no proof for.
    pub(super) fn nonneg_proof(
        &self,
        e: &Node,
        known: &[ShownWhole],
    ) -> Option<Printed> {
        let ctx = self.sources.ctx;
        let mut known = known.to_vec();
        known.extend(self.wholes_in_scope());
        let known = known.as_slice();
        let letters = self.writer.page_systems();
        let nonzero = |d: &Node| nonzero_said_once(d, &letters);
        let said = |t: &Node, s: rules::System| {
            (rules::System::N0.within(s)
                && known.iter().any(|k| matching::alike_top(&k.term, t, ctx)))
            .then_some(OnceReason::Stated)
        };
        let reason = reason_within(e, rules::System::N0, &letters, &nonzero, &said)?;
        self.nonneg_by(e, &reason, known)
    }

    /// The terms the lines in scope put at 0 or above, each with its proof
    /// of `0 ≤ t`: a line's bound (`Bound::said_by`), 4.3's `0 < e`, and a
    /// membership of ℕ or ℕ₀ the step names.
    pub(super) fn wholes_in_scope(&self) -> Vec<ShownWhole> {
        match self.step_now.get() {
            Some(i) => self.wholes_among(&self.step_facts(i)),
            None => self.wholes_among(&[]),
        }
    }

    /// `wholes_in_scope`, the memberships read from `facts`: the step's
    /// lines, and those a requires line's own reason names.
    pub(super) fn wholes_among(
        &self,
        facts: &[super::super::algebra::Cited],
    ) -> Vec<ShownWhole> {
        self.wholes_among_in(facts, &self.writer)
    }

    /// `wholes_among`, each fact read as `writer` writes it.
    pub(super) fn wholes_among_in(
        &self,
        facts: &[super::super::algebra::Cited],
        writer: &Writer,
    ) -> Vec<ShownWhole> {
        let mut known = Vec::new();
        for b in self.writer.bounds.terms.iter().filter(|b| b.least >= 0) {
            if let Some(proof) = self.bound_nonneg(b) {
                known.push(ShownWhole {
                    term: b.term.clone(),
                    proof,
                });
            }
        }
        for f in facts {
            let Some((term, system)) = membership_of_whole(&f.node) else {
                continue;
            };
            if super::cited_lines::written_as_bound(&f.node, writer) {
                known.push(ShownWhole {
                    term: term.clone(),
                    proof: nonneg_of(system, f.proof.clone()),
                });
            }
        }
        known
    }

    /// The proof of `wanted`, a membership the said-once walk gives
    /// (`SuppliedBy::Walked`) as Lean states it, from the walk's reason:
    /// `0 ≤ t` of a t in ℕ₀ (`nonneg_by`), `0 < t` of one in ℕ
    /// (`positive_by`). Declined for a membership Lean states otherwise,
    /// or a reason those write no proof for.
    pub(super) fn walked_proof(
        &self,
        walked: &SaidOnceFact,
        wanted: &Printed,
    ) -> Route<Printed> {
        let [term, set] = walked.fact.children.as_slice() else {
            return Route::no("a said-once fact that is no membership");
        };
        let system = rules::System::of_sign(&set.text);
        // A bound Lean writes as a membership it defines by it, `b * d ∈
        // {n : ℤ | 0 < n}`, read as that bound.
        let wanted = &super::super::doc::forms::unfolded(wanted);
        // A number the step names in it, cast back, put back as its integer
        // first, which the reason speaks of (`put_back`).
        let back = self.put_back(wanted);
        let left = back.as_ref().map(|b| b.left.clone());
        let wanted = left.as_ref().unwrap_or(wanted);
        if super::super::doc::forms::relation_type(wanted)
            != Some(LeanType::Num(Num::Int))
        {
            return Route::no("a said-once membership Lean states outside ℤ");
        }
        // A term the walk took beside a cited equation (`Besides::of`), its
        // bound carried along the equation from the other side's, as a
        // `membership` claim shown so is (`bound_beside`).
        if let (Some(beside), Some(system), Some(i)) =
            (Besides::of(&walked.shown), system, self.step_now.get())
        {
            let just = &self.thm.steps[i].just;
            let cited = self.cited_equations(&just.refs);
            return match self.bound_beside(&beside, system, just, &cited) {
                Some(p) => Route::Built(match back {
                    Some(b) => b.then(p),
                    None => p,
                }),
                None => Route::no(format!(
                    "a membership beside an equation no bound is written for, of {}",
                    self.writer.grammar.print(term)
                )),
            };
        }
        let proof = match (system, relation_symbol(wanted)) {
            // A natural number Lean casts up, `(Int.gcd s w : ℤ)`.
            (Some(rules::System::N0), Some("≤")) if natural_cast_bounded(wanted) => {
                Some(Printed::applied(
                    "Nat.cast_nonneg",
                    super::super::doc::Source::Mathlib,
                    vec![Printed::of(
                        super::super::doc::TermKind::Elided,
                        LeanType::Prop,
                    )],
                    LeanType::Prop,
                ))
            }
            (Some(rules::System::N0), Some("≤")) => {
                self.nonneg_by(term, &walked.reason, &self.wholes_in_scope())
            }
            (Some(rules::System::N), Some("<")) => {
                let facts = match self.step_now.get() {
                    Some(i) => self.step_facts(i),
                    None => Vec::new(),
                };
                self.positive_by(term, &walked.reason, &facts)
            }
            _ => {
                return Route::no("a said-once membership Lean states as no bound at 0")
            }
        };
        match proof {
            Some(p) => Route::Built(match back {
                Some(b) => b.then(p),
                None => p,
            }),
            None => Route::no(format!(
                "a said-once reason no proof is written for, of {}",
                self.writer.grammar.print(term)
            )),
        }
    }

    /// `0 < e` for the reason the said-once walk puts e in ℕ: a numeral, by
    /// `norm_num`; a letter, from the line that introduces it in ℕ; a term
    /// one of `facts` puts in ℕ, that line; a sum or a product of parts in
    /// ℕ, `add_pos` or `mul_pos` of theirs. None for any other reason.
    pub(super) fn positive_by(
        &self,
        e: &Node,
        reason: &OnceReason,
        facts: &[super::super::algebra::Cited],
    ) -> Option<Printed> {
        let both = |lemma: &str, reasons: &[OnceReason]| {
            let ([a, b], [ra, rb]) = (e.children.as_slice(), reasons) else {
                return None;
            };
            Some(Printed::applied(
                lemma,
                super::super::doc::Source::Mathlib,
                vec![
                    super::super::tactics::bracket(self.positive_by(a, ra, facts)?),
                    super::super::tactics::bracket(self.positive_by(b, rb, facts)?),
                ],
                super::super::doc::LeanType::Prop,
            ))
        };
        match (reason, e.notation()) {
            (OnceReason::Numeral, _) => Some(norm_num_term()),
            (OnceReason::Letter, _) => self.letter_positive(e),
            // A term a line the step names puts in ℕ, `0 < 2^p − 1`: that
            // line.
            (OnceReason::Stated, _) => {
                let line = named_line(facts, e, rules::System::N, self.sources.ctx)?;
                Some(line.name)
            }
            (OnceReason::Built(reasons), ADDITIVE) if e.spelling() == PLUS => {
                both("add_pos", reasons)
            }
            (OnceReason::Built(reasons), MULTIPLICATIVE) if e.spelling() == TIMES => {
                both("mul_pos", reasons)
            }
            // A power of a base in ℕ, `pow_pos` of the base's.
            (OnceReason::Built(reasons), POWER | SUPERSCRIPT) => {
                let ([base, _], [rb]) = (e.children.as_slice(), reasons.as_slice())
                else {
                    return None;
                };
                Some(Printed::applied(
                    "pow_pos",
                    super::super::doc::Source::Mathlib,
                    vec![
                        super::super::tactics::bracket(
                            self.positive_by(base, rb, facts)?,
                        ),
                        Printed::of(
                            super::super::doc::TermKind::Elided,
                            super::super::doc::LeanType::Prop,
                        ),
                    ],
                    super::super::doc::LeanType::Prop,
                ))
            }
            // n! of an n in ℕ₀, by the factorial bridge's `factorial_nat`.
            (OnceReason::Factorial(inner), _) => {
                let [n] = e.children.as_slice() else {
                    return None;
                };
                let at = self
                    .writer
                    .number_fixed(n, super::super::templates::Num::Int)
                    .built()?;
                let nonneg = self.nonneg_by(n, inner, &self.wholes_in_scope())?;
                Some(Printed::applied(
                    "LeanBridges.Counting.factorial_nat",
                    super::super::doc::Source::Bridge(BridgeModule::Counting),
                    vec![
                        super::super::tactics::bracket(at),
                        super::super::tactics::bracket(nonneg),
                    ],
                    super::super::doc::LeanType::Prop,
                ))
            }
            _ => None,
        }
    }

    /// `0 < n` of a letter the line in scope that introduces it puts in ℕ,
    /// which Lean states so; or in a range from a numeral at least 1, `k ∈
    /// {1, …, n}`, by the range's lower bound, `lt_of_lt_of_le (by norm_num)
    /// (Finset.mem_Icc.mp h).1`. None where no line in scope introduces it
    /// so.
    pub(super) fn letter_positive(&self, e: &Node) -> Option<Printed> {
        if !e.is_name() {
            return None;
        }
        self.trees.values().flatten().find_map(|s| {
            if let Some((letter, system)) = super::super::statement::introduces(&s.node)
            {
                return (letter.as_str() == &*e.text
                    && system == super::super::expr::System::Positive)
                    .then(|| s.proof.clone());
            }
            if super::super::statement::range_letter(&s.node)?.as_str() != &*e.text {
                return None;
            }
            let from = s.node.children.get(1)?.children.first()?;
            // As Lean states the range: a finite set, or a set.
            let set_lemma = match s.says.as_ref().is_some_and(|t| t.names("Set.Icc")) {
                true => "Set.mem_Icc",
                false => "Finset.mem_Icc",
            };
            Some(range_bound(
                range_row(Some(rules::System::N), from)?.lean?,
                set_lemma,
                s.proof.clone(),
            ))
        })
    }

    /// `0 ≤ t` of a term a line in scope bounds below at 0 or above
    /// (`Bound`), from that line as Lean states it: `t ∈ ℕ₀` itself, `t ∈ ℕ`
    /// by `le_of_lt`, `a ≤ t` by `le_trans` of `0 ≤ a`, `a < t` by `le_of_lt`
    /// of `lt_of_le_of_lt` of `0 ≤ a`, the numeral's fact by `norm_num`.
    /// None where no line in scope says it, or says it of a bound that is no
    /// numeral.
    pub(super) fn bound_nonneg(&self, b: &Bound) -> Option<Printed> {
        let ctx = self.sources.ctx;
        let said = b.said_by.as_ref()?;
        let line = self
            .trees
            .values()
            .flatten()
            .find(|s| matching::alike_top(&s.node, said, ctx))?;
        let proof = line.proof.clone();
        if said.notation() == MEMBERSHIP {
            let (_, system) = membership_of_whole(said)?;
            return Some(nonneg_of(system, proof));
        }
        let [l, r] = said.children.as_slice() else {
            return None;
        };
        let s = said.spelling();
        let (bound, strict) = match () {
            _ if said.notation() != ORDER => return None,
            _ if s == LESS => (l, true),
            _ if s == GREATER => (r, true),
            _ if s == AT_MOST => (l, false),
            _ if s == AT_LEAST => (r, false),
            _ => return None,
        };
        if bound.notation() != NUMERAL {
            return None;
        }
        let applied = |name: &str, args: Vec<Printed>| {
            Printed::applied(
                name,
                super::super::doc::Source::Mathlib,
                args,
                super::super::doc::LeanType::Prop,
            )
        };
        Some(match strict {
            true => applied(
                "le_of_lt",
                vec![super::super::tactics::bracket(applied(
                    "lt_of_le_of_lt",
                    vec![norm_num_term(), proof],
                ))],
            ),
            false => applied("le_trans", vec![norm_num_term(), proof]),
        })
    }

    /// `nonneg_proof` of `e` for the reason the walk gives: a part `known`
    /// gives, by its proof; a numeral, by `norm_num`; a letter, from the line
    /// that introduces it (`letter_nonneg`); a factorial, a natural number
    /// cast, `Nat.cast_nonneg`; a sum or a product of parts the
    /// walk puts in ℕ₀, `add_nonneg` or `mul_nonneg` of theirs. None for any
    /// other reason.
    pub(super) fn nonneg_by(
        &self,
        e: &Node,
        reason: &OnceReason,
        known: &[ShownWhole],
    ) -> Option<Printed> {
        let ctx = self.sources.ctx;
        let both = |lemma: &str, parts: &[Node], reasons: &[OnceReason]| {
            let ([a, b], [ra, rb]) = (parts, reasons) else {
                return None;
            };
            Some(Printed::applied(
                lemma,
                super::super::doc::Source::Mathlib,
                vec![
                    super::super::tactics::bracket(self.nonneg_by(a, ra, known)?),
                    super::super::tactics::bracket(self.nonneg_by(b, rb, known)?),
                ],
                super::super::doc::LeanType::Prop,
            ))
        };
        match (reason, e.notation()) {
            (OnceReason::Stated, _) => known
                .iter()
                .find(|k| matching::alike_top(&k.term, e, ctx))
                .map(|k| k.proof.clone()),
            (OnceReason::Numeral, _) => Some(norm_num_term()),
            (OnceReason::Letter, _) => self.letter_nonneg(e),
            // n! is a natural number, which Lean casts to ℤ.
            (OnceReason::Factorial(_), _) => Some(Printed::applied(
                "Nat.cast_nonneg",
                super::super::doc::Source::Mathlib,
                vec![Printed::of(
                    super::super::doc::TermKind::Elided,
                    super::super::doc::LeanType::Prop,
                )],
                super::super::doc::LeanType::Prop,
            )),
            // |x|, `abs_nonneg`.
            (OnceReason::Absolute { .. }, _) => Some(Printed::applied(
                "abs_nonneg",
                super::super::doc::Source::Mathlib,
                vec![Printed::of(
                    super::super::doc::TermKind::Elided,
                    super::super::doc::LeanType::Prop,
                )],
                super::super::doc::LeanType::Prop,
            )),
            // A power of a base in ℕ₀, `pow_nonneg` of the base's.
            (OnceReason::Built(reasons), POWER | SUPERSCRIPT) => {
                let ([base, _], [rb]) = (e.children.as_slice(), reasons.as_slice())
                else {
                    return None;
                };
                Some(Printed::applied(
                    "pow_nonneg",
                    super::super::doc::Source::Mathlib,
                    vec![
                        super::super::tactics::bracket(
                            self.nonneg_by(base, rb, known)?,
                        ),
                        Printed::of(
                            super::super::doc::TermKind::Elided,
                            super::super::doc::LeanType::Prop,
                        ),
                    ],
                    super::super::doc::LeanType::Prop,
                ))
            }
            (OnceReason::Built(reasons), ADDITIVE) if e.spelling() == PLUS => {
                both("add_nonneg", &e.children, reasons)
            }
            // A row of the closure table (`rules::WHOLE`), (t + 1) mod 10,
            // the divisor's bound by its own reason.
            (OnceReason::Built(reasons), _)
                if self
                    .sources
                    .targets
                    .operation(e)
                    .is_some_and(|op| WHOLE.iter().any(|w| w.op == op.label)) =>
            {
                let op = self.sources.targets.operation(e)?;
                let divisor = || match (op.parts.as_slice(), reasons.as_slice()) {
                    ([_, right], [_, rr]) => self.positive_by(right, rr, &[]),
                    _ => None,
                };
                whole_nonneg(&op.label, divisor)
            }
            (OnceReason::Built(reasons), MULTIPLICATIVE) if e.spelling() == TIMES => {
                both("mul_nonneg", &e.children, reasons)
            }
            _ => None,
        }
    }

    /// `0 ≤ n` of a letter the said-once walk puts in ℕ₀, from the line in
    /// scope that introduces it: `n ∈ ℕ₀`, which Lean states `0 ≤ n`; `n ∈
    /// ℕ`, `le_of_lt` of its `0 < n`; `n ∈ {a, …, b}` of a numeral a,
    /// `le_trans` of `0 ≤ a` and the range's lower bound. None where no line
    /// in scope introduces it so.
    pub(super) fn letter_nonneg(&self, e: &Node) -> Option<Printed> {
        if !e.is_name() {
            return None;
        }
        let lines = self
            .trees
            .values()
            .flatten()
            .map(|s| (s.node.clone(), s.proof.clone()));
        lines.chain(self.claim_member()).find_map(|(node, proof)| {
            if let Some((letter, system)) = super::super::statement::introduces(&node) {
                if letter.as_str() != &*e.text {
                    return None;
                }
                return match system {
                    expr::System::Positive => Some(nonneg_of(rules::System::N, proof)),
                    expr::System::NonNegative => Some(proof),
                    expr::System::Type(_) => None,
                };
            }
            let letter = super::super::statement::range_letter(&node)?;
            let from = node.children.get(1)?.children.first()?;
            if letter.as_str() != &*e.text || from.notation() != NUMERAL {
                return None;
            }
            // 0 ≤ a of any numeral start, and a ≤ k.
            Some(range_bound("le_trans", "Finset.mem_Icc", proof))
        })
    }

    /// The membership the step's claim, a "for all", gives its letter while
    /// the claim's binders are open (`intros_now`), with its proof, the
    /// hypothesis Lean introduces with the letter (`h_j` of `j ∈ ℕ₀`). None
    /// outside such a claim.
    pub(super) fn claim_member(&self) -> Option<(Node, Printed)> {
        let step = &self.thm.steps[self.step_now.get()?];
        let sentence = step.claim.sentences().into_iter().next()?;
        let claim = self.rec.page.get(&sentence)?;
        let (member, _) = claimed_member(claim, self.writer.grammar)?;
        let letter = member.children.first().filter(|l| l.is_name())?;
        let h = format!("h_{}", super::super::names::letter(&letter.text));
        self.intros_now
            .borrow()
            .contains(&h)
            .then(|| (member.clone(), super::super::tactics::hyp(&h)))
    }

    /// The proof that `set` is finite, from why the checker says it is
    /// (`citing::finite::finite_by` over the facts the writer is given): a
    /// line's name where a line says so; `(whole).subset h` of a part of a
    /// finite set by the line `h`; and how the set is made, by Mathlib's
    /// lemmas for ∅, a listed set, a range, 𝒫, ∪, an image, and `.subset`
    /// of A ∖ B, A ∩ B and a set-builder within A. None where the set is not
    /// shown finite, or the reason names nothing a proof is written from: a
    /// define's function, or a letter bound over a set.
    pub(super) fn finite_proof(&self, set: &Node) -> Option<Printed> {
        // A set a define names is finite by the `have` beside the define,
        // which proves it of the value Lean writes for the letter.
        if let Some(have) = set
            .is_name()
            .then(|| self.finite_defined.get(&*set.text))
            .flatten()
        {
            return Some(super::super::tactics::hyp(have));
        }
        let why = finite::finite_by(&self.writer.finite, set)?;
        self.proof_of_finite(&why, set)
    }

    /// Whether `says` counts `set` itself in ℕ∞, `S.encard`, and not only
    /// some set inside it.
    fn counts_extended_of(&self, says: &Printed, set: &Node) -> bool {
        let Route::Built(written) = self.writer.set_term(set) else {
            return false;
        };
        says.walk().iter().any(|t| {
            matches!(&t.kind, super::super::doc::TermKind::Count { set: s, form }
                if *form == super::super::doc::CountForm::Extended
                    && s.untyped() == written.untyped())
        })
    }

    /// `finite_proof` of `set` for the reason `why`.
    pub(super) fn proof_of_finite(
        &self,
        why: &FiniteBy,
        set: &Node,
    ) -> Option<Printed> {
        let field = |inner: Printed, name: &str| projected(inner, &[name]);
        let hole = || Printed::of(TermKind::Elided, super::super::doc::LeanType::Prop);
        let constant = |name: &str| {
            Printed::constant(
                name,
                super::super::doc::Source::Mathlib,
                super::super::doc::LeanType::Prop,
            )
        };
        // A part of A, by the membership of each member: `fun _ h => h.1` of
        // a set-builder, A ∖ B or A ∩ B within A, `h.2` of A ∩ B within B.
        let part_of = |whole: Printed, side: &str| {
            let member = untyped_lambda(
                &["_", "h"],
                Printed {
                    kind: TermKind::Field {
                        inner: Box::new(super::super::tactics::hyp("h")),
                        field: side.to_string(),
                    },
                    ty: Some(super::super::doc::LeanType::Prop),
                },
            );
            applied_to(
                field(whole, "subset"),
                super::super::tactics::bracket(member),
            )
        };
        let child = |k: usize| set.children.get(k);
        let of = |k: usize| {
            let part = child(k)?;
            self.finite_proof(part)
        };
        match why {
            FiniteBy::Said(line) => self.line_saying(line),
            // A count given as a number at least 1, written in ℕ,
            // `(X.ncard : ℤ) = 2`: its count is not 0, by the line and the
            // bounds in scope.
            // A count Lean states in ℕ∞, `V.encard = ↑2`, an assumption a
            // direction takes from the claim: finite by that line, whatever
            // the number.
            FiniteBy::Counted { line, .. }
                if self.line_sentence(line).is_some_and(|said| {
                    said.says
                        .as_ref()
                        .is_some_and(|s| self.counts_extended_of(s, set))
                }) =>
            {
                Some(Printed::applied(
                    "Set.finite_of_encard_eq_coe",
                    super::super::doc::Source::Mathlib,
                    vec![self.line_sentence(line)?.proof.clone()],
                    super::super::doc::LeanType::Prop,
                ))
            }
            // The count is not 0: were it, the line would say 0 is its
            // number, which is above 0 as the said-once walk puts it in ℕ
            // (`positive_proof`).
            FiniteBy::Counted {
                line,
                at_least_one: true,
            } => {
                let said = self.line_sentence(line)?;
                let [_, value] = said.node.children.as_slice() else {
                    return None;
                };
                // The number as the line states it, and the statement that
                // it is above 0, which a numeral's `norm_num` is told.
                let says = said.says.as_ref()?;
                let (_, number) = super::orders::equation_sides(says)?;
                let ty = number
                    .ty
                    .clone()
                    .unwrap_or(super::super::doc::LeanType::Num(
                        super::super::templates::Num::Int,
                    ));
                let above = Printed::of(
                    super::super::doc::TermKind::Ascribed {
                        says: Box::new(
                            super::super::expr::relation_of(
                                "<",
                                Printed::numeral("0", ty),
                                number.clone(),
                            )
                            .built()?,
                        ),
                        proof: Box::new(self.positive_proof(value)?),
                    },
                    super::super::doc::LeanType::Prop,
                );
                let ne = Printed::applied(
                    "ne_of_lt",
                    super::super::doc::Source::Mathlib,
                    vec![t::bracket(above)],
                    super::super::doc::LeanType::Prop,
                );
                let at = TacticArg::At(vec![super::super::doc::Location::Hypothesis(
                    "h".to_string(),
                )]);
                let not_zero = untyped_lambda(
                    &["h0"],
                    t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
                        t::name_h(&said.proof),
                        t::call("rw", vec![t::rules(vec![t::hyp("h0")]), at]),
                        Tactic::Exact(applied_to(
                            ne,
                            t::bracket(t::by_term(super::super::doc::Proof::By(
                                t::exact_mod_cast(t::hyp("h")),
                            ))),
                        )),
                    ]))),
                );
                Some(Printed::applied(
                    "Set.finite_of_ncard_ne_zero",
                    super::super::doc::Source::Mathlib,
                    vec![t::bracket(not_zero)],
                    super::super::doc::LeanType::Prop,
                ))
            }
            // A count that may be 0, written in ℕ∞, `X.encard = ↑m`. One
            // written in ℕ, `(X.ncard : ℤ) = 0`, was written so because the
            // set was finite before the line: why it was then.
            FiniteBy::Counted {
                line,
                at_least_one: false,
            } => {
                let said = self.line_sentence(line)?;
                let in_naturals = said.says.as_ref().is_some_and(|s| {
                    s.has_count(super::super::doc::CountForm::Natural)
                });
                if in_naturals {
                    let mut before = self.writer.finite.clone();
                    before.shift_remove(&finite::key(set));
                    let why = finite::finite_by(&before, set)?;
                    return self.proof_of_finite(&why, set);
                }
                Some(Printed::applied(
                    "Set.finite_of_encard_eq_coe",
                    super::super::doc::Source::Mathlib,
                    vec![said.proof.clone()],
                    super::super::doc::LeanType::Prop,
                ))
            }
            // Each member some e(i) of a range of integers: the range's
            // image covers it (`LeanBridges.Sets.finite_of_covered_by_range`).
            FiniteBy::Covered { line, .. } => {
                let said = self.line_node(line)?;
                let [_, _, body] = said.children.as_slice() else {
                    return None;
                };
                let over = body.children.get(1)?;
                if over.notation() != INTEGER_RANGE {
                    return None;
                }
                Some(Printed::applied(
                    "LeanBridges.Sets.finite_of_covered_by_range",
                    super::super::doc::Source::Bridge(
                        super::super::doc::bridges::BridgeModule::Sets,
                    ),
                    vec![hole(), hole(), hole(), self.line_saying(line)?],
                    super::super::doc::LeanType::Prop,
                ))
            }
            FiniteBy::Part { line, whole } => {
                let said = self.line_node(line)?;
                let whole_set = match (said.notation(), said.children.as_slice()) {
                    (MEMBERSHIP, [_, powerset]) => powerset.children.first()?,
                    (_, [_, whole]) => whole,
                    _ => return None,
                };
                let whole_proof = self.proof_of_finite(whole, whole_set)?;
                Some(applied_to(
                    field(whole_proof, "subset"),
                    self.line_saying(line)?,
                ))
            }
            FiniteBy::Made(made) => match made {
                Making::Empty => Some(constant("Set.finite_empty")),
                Making::Listed => Some(applied_to(constant("Set.toFinite"), hole())),
                Making::Range => Some(applied_to(
                    applied_to(constant("Set.finite_Icc"), hole()),
                    hole(),
                )),
                Making::Powerset(_) => Some(field(of(0)?, "powerset")),
                Making::Builder(_) => Some(part_of(of(1)?, "1")),
                Making::Minus(_) => Some(part_of(of(0)?, "1")),
                Making::Inter(_) => match of(0) {
                    Some(left) => Some(part_of(left, "1")),
                    None => Some(part_of(of(1)?, "2")),
                },
                Making::Union(_, _) => Some(applied_to(
                    field(of(0)?, "union"),
                    super::super::tactics::bracket(of(1)?),
                )),
                Making::Image(_) => Some(applied_to(field(of(2)?, "image"), hole())),
                // gH, Lean's `(g * ·) '' H`: the image of a finite H.
                Making::Coset(_) => Some(applied_to(field(of(1)?, "image"), hole())),
                Making::Applied(_) => None,
                // The functions from a finite X to a finite Y.
                Making::Functions(_, _) => Some(applied_to(
                    applied_to(
                        super::super::tactics::bridge_lemma(
                            "LeanBridges.Functions.functions_from_finite",
                            super::super::doc::bridges::BridgeModule::Functions,
                        ),
                        super::super::tactics::bracket(of(0)?),
                    ),
                    super::super::tactics::bracket(of(1)?),
                )),
                // X ×ˢ Y of a finite X and a finite Y: Mathlib's `Set.Finite.prod`.
                Making::Product(_, _) => Some(applied_to(
                    field(of(0)?, "prod"),
                    super::super::tactics::bracket(of(1)?),
                )),
            },
            // The `have` written beside the define (`define`).
            FiniteBy::Define(name) => self
                .finite_defined
                .get(name)
                .map(|have| super::super::tactics::hyp(have)),
            FiniteBy::Bound(_) | FiniteBy::MemberOf(_) => None,
        }
    }
}
