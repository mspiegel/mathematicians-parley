//! Proof methods: chains, orders and instantiation.

use super::*;

impl<'a> Proof<'a> {
    /// The sentence of a line in scope that is `line`, by its tree.
    pub(super) fn line_node(
        &self,
        line: &crate::formula::node::ByShape,
    ) -> Option<&Node> {
        self.line_sentence(line).map(|s| &s.node)
    }

    /// The proof of the sentence of a line in scope that is `line`, by its
    /// tree: its name, or the projection that takes it.
    pub(super) fn line_saying(
        &self,
        line: &crate::formula::node::ByShape,
    ) -> Option<Printed> {
        self.line_sentence(line).map(|s| s.proof.clone())
    }

    /// The sentence of a line in scope that is `line`, by its tree.
    pub(super) fn line_sentence(
        &self,
        line: &crate::formula::node::ByShape,
    ) -> Option<&LineSentence> {
        self.trees
            .values()
            .flatten()
            .find(|s| s.node.spelt_alike(&line.0))
    }

    /// A `transitivity` step's chain composed link by link
    /// (`CheckedTheorem::links`): each link the line the checker placed it
    /// in, read the way the chain goes, an equation read from its right side
    /// by `.symm` and an order by its converse, which Lean takes as the same
    /// statement; a chain going down taken as its links going up from the
    /// last; and the links joined by the lemma for each pair of relations,
    /// `lt_of_le_of_lt` of `≤` then `<`. Closed by `exact`, or by
    /// `exact_mod_cast` where the claim is in another type than the links.
    /// None where a link stands in no line, or the links are not all in one
    /// type, or the chain is of equations alone, which the claim may write
    /// either way round.
    pub(super) fn chain_composed(
        &self,
        just: &Justification,
        node: &Node,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let converse = |s: &str| -> Option<&'static str> {
            match s {
                "=" => Some("="),
                "<" => Some(">"),
                ">" => Some("<"),
                "≤" => Some("≥"),
                "≥" => Some("≤"),
                _ => None,
            }
        };
        let Some(chain) = self.rec.links.get(&just.line) else {
            return Route::no("a chain the checker placed no links of");
        };
        let links = &chain.links;
        let mut facts = Vec::new();
        for link in links {
            let Some(at) = &link.at else {
                return Route::no("a chain's link the checker found in no line");
            };
            match self.order_fact(at, w) {
                Route::Built(f) => facts.push(f),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The links are joined in the widest type any of them is in, each
        // in a narrower one taken up to it (`fact_in_type`); links of no
        // number type, sets `A = B = C`, as they stand.
        let mut widest = None;
        let numbers = facts
            .iter()
            .filter(|f| number_type(&f.says).is_some())
            .count();
        if numbers != 0 && numbers != facts.len() {
            return Route::no("a chain's links of numbers and of other things");
        }
        for f in &facts {
            if let (Some(t), w) = (number_type(&f.says), widest) {
                widest = Some(w.map_or(t, |w| std::cmp::max(t, w)));
            }
        }
        // A chain the checker met only with identity elements dropped, `n·1`
        // beside `n`, is no composition Lean takes as written: linear
        // arithmetic over its links, which reads `n * 1` as `n`.
        if !chain.as_written {
            let mut added = Vec::new();
            for f in facts {
                match self.fact_in_type(f, widest, w) {
                    Route::Built(p) => added.push(p),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let claim_in = self
                .claim_as_stated(just.line, node)
                .and_then(|c| number_type(&c));
            if claim_in != widest {
                return Route::no(
                    "a chain met with identities dropped, its claim in another type",
                );
            }
            return Route::Built(match split_linarith(&[], added).kind {
                super::super::doc::TermKind::By(proof) => *proof,
                other => super::super::doc::Proof::Term(Printed {
                    kind: other,
                    ty: None,
                }),
            });
        }
        let mut read: Vec<(Printed, &'static str)> = Vec::new();
        for (link, f) in links.iter().zip(facts) {
            let Some(symbol) = relation_symbol(&f.says) else {
                return Route::no("a chain's link that is no relation");
            };
            // Only a relation of the five makes a link.
            let Some(turned) = converse(symbol) else {
                return Route::no(
                    "a chain's link that is not one of the five relations",
                );
            };
            // The record reads the link from the side the page writes it;
            // Lean may state the line the other way round, `3 * M < N` of
            // the page's `N > 3M`, and the link is then read from the other.
            let page = self
                .writer
                .formula(&link.said)
                .built()
                .and_then(|p| relation_symbol(&p).map(str::to_string));
            let restated =
                page.is_some_and(|p| converse(&p) == Some(symbol) && p != symbol);
            let turned_here = link.turned != restated;
            let proof = match self.fact_in_type(f, widest, w) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            read.push(match (turned_here, symbol) {
                (true, "=") => (super::super::tactics::symm(proof), "="),
                (true, _) => (proof, turned),
                (false, s) => (proof, s),
            });
        }
        if read.iter().any(|(_, s)| matches!(*s, ">" | "≥")) {
            let mut up = Vec::new();
            for (p, s) in read.into_iter().rev() {
                match s {
                    "=" => up.push((super::super::tactics::symm(p), "=")),
                    s => match converse(s) {
                        Some(c) => up.push((p, c)),
                        None => return Route::no("a chain's link with no converse"),
                    },
                }
            }
            read = up;
        }
        let mut links = read.into_iter();
        let Some((mut proof, mut rel)) = links.next() else {
            return Route::no("a chain of no links");
        };
        for (next, s) in links {
            let (lemma, joined) = match (rel, s) {
                ("=", "=") => ("Eq.trans", "="),
                ("=", "≤") => ("Eq.trans_le", "≤"),
                ("=", "<") => ("Eq.trans_lt", "<"),
                ("≤", "=") => ("LE.le.trans_eq", "≤"),
                ("≤", "≤") => ("le_trans", "≤"),
                ("≤", "<") => ("lt_of_le_of_lt", "<"),
                ("<", "=") => ("LT.lt.trans_eq", "<"),
                ("<", "≤") => ("lt_of_lt_of_le", "<"),
                ("<", "<") => ("lt_trans", "<"),
                _ => return Route::no("a chain whose links run both ways"),
            };
            proof = Printed::applied(
                lemma,
                super::super::doc::Source::Mathlib,
                vec![proof, next],
                super::super::doc::LeanType::Prop,
            );
            rel = joined;
        }
        // A chain of equations the claim writes the other way round, `c =
        // a` of `a = b = c`, is the chain turned; an order Lean reads either
        // way round, `c > a` being `a < c`.
        if rel == "=" && chain.claim_turned {
            proof = super::super::tactics::symm(super::super::tactics::bracket(proof));
        }
        let Some(claim) = self.claim_as_stated(just.line, node) else {
            return Route::no("a chain's claim Lean does not state");
        };
        // A claim of ℚ is taken back from the chain in ℝ by ℚ's cast lemmas
        // (`real_to_rat`).
        if let Some(to) = widest.filter(|t| number_type(&claim) != Some(*t)) {
            let wide = match w.closed_formula(node, to) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            if rat_crossing(&claim, &wide) {
                let chained = super::super::doc::Proof::Term(proof);
                return match real_to_rat(chained, &claim, wide) {
                    Some(p) => Route::Built(p),
                    None => Route::no(
                        "a chain's claim of ℚ taken from ℝ by no relation lemma",
                    ),
                };
            }
        }
        let tactic = match number_type(&claim) == widest {
            true => Tactic::Exact(proof),
            false => super::super::tactics::exact_mod_cast(proof),
        };
        Route::Built(super::super::doc::Proof::By(tactic))
    }

    /// A fact an order step or a chain adds, in the number type `to`: as
    /// it stands where Lean states it there, or where `to` is none; else
    /// stated in `to` and taken up within a `show T by …`, which `linarith`
    /// reads before it runs, where an ascription's proof is left to after.
    /// From ℚ to ℝ by ℚ's cast lemmas (`rat_to_real`); between other types
    /// by `exact_mod_cast`, where `norm_cast` moves every cast
    /// (`lifts_whole`). Never a define's kind, which the page writes of the
    /// define's value and Lean proves of its letter.
    pub(super) fn fact_in_type(
        &self,
        f: OrderFactTerm,
        to: Option<super::super::templates::Num>,
        w: &Writer,
    ) -> Route<Printed> {
        use super::super::doc::Proof;
        let Some(to) = to.filter(|t| number_type(&f.says) != Some(*t)) else {
            return Route::Built(f.proof);
        };
        if !f.widens {
            return Route::no("a define's kind taken up to a wider type");
        }
        let says = match w.closed_formula(&f.node, to) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        // From ℚ to ℝ by ℚ's cast lemmas (`rat_to_real`), not `norm_cast`.
        if rat_crossing(&f.says, &says) {
            return match rat_to_real(f.proof, &f.says, says) {
                Some(p) => Route::Built(p),
                None => Route::no("a fact of ℚ taken to ℝ by no relation lemma"),
            };
        }
        if !lifts_whole(&f.says, to) {
            return Route::no(format!(
                "a fact {} in a narrower type than norm_cast takes up to {}",
                f.says.text(),
                says.text()
            ));
        }
        Route::Built(super::super::tactics::bracket(shown(
            says,
            Proof::By(super::super::tactics::exact_mod_cast(f.proof)),
        )))
    }

    /// A sentence of an order step's claim from what the checker recorded
    /// it rests on (`CheckedTheorem::orders`): each part joined by "and" by
    /// `order_part`, the parts in `⟨…⟩` as the sentence joins them. `line`
    /// is the justification's, `k` the sentence's place, `node` the
    /// sentence as Lean states it.
    pub(super) fn order_proof(
        &self,
        line: usize,
        k: usize,
        node: &Node,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let Some(parts) = self.rec.orders.get(&line).and_then(|o| o.sentences.get(k))
        else {
            return Route::no("an order step the checker recorded no facts for");
        };
        let mut left = parts.iter();
        let proof = match self.order_joined(node, &mut left, w) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        match left.next() {
            None => Route::Built(proof),
            Some(_) => {
                Route::no("an order step recorded with more parts than its claim")
            }
        }
    }

    /// The proof of `node`, a sentence or a part of one, taking its parts
    /// joined by "and" from `parts` left to right, as the checker counts
    /// them.
    pub(super) fn order_joined<'p>(
        &self,
        node: &Node,
        parts: &mut impl Iterator<Item = &'p crate::checker::record::OrderPart>,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        let Some((left, right)) = w.and_sides(node) else {
            let Some(part) = parts.next() else {
                return Route::no(
                    "an order step recorded with fewer parts than its claim",
                );
            };
            return self.order_part(part, node, w);
        };
        let mut items = Vec::new();
        for child in [left, right] {
            match self.order_joined(child, parts, w) {
                Route::Built(Proof::Term(t)) => items.push(t),
                Route::Built(p) => items.push(super::super::tactics::by_term(p)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        Route::Built(Proof::Term(super::super::expr::anonymous(items)))
    }

    /// One part of an order step's claim, `node`, from what it rests on:
    /// the fact that says a disequality, `Ne.symm` of it where it says it
    /// turned; `ne_of_lt` or `ne_of_gt` of the order a `weakening` makes
    /// one of; otherwise `linarith only` over the facts it adds, each
    /// disequality it takes both ways split first by `Ne.lt_or_gt`.
    ///
    /// Linear arithmetic adds facts of one type. Where Lean states the
    /// claim and the facts in different number types, it works in the
    /// widest of them: a fact in a narrower one is taken up to it by
    /// `exact_mod_cast`, and a claim in a narrower one is proved there and
    /// taken down by `exact_mod_cast`.
    pub(super) fn order_part(
        &self,
        part: &crate::checker::record::OrderPart,
        node: &Node,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::{LeanType, Proof, Source, TermKind};
        use crate::checker::record::Weakened;
        let wanted = match w.formula(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        if let Some(r) = &part.restates {
            let fact = match self.order_fact(&r.by, w) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if super::super::doc::forms::relation_types_apart(&fact.says, &wanted) {
                return Route::no(
                    "a disequality an order step restates, in another type",
                );
            }
            // The checker found the two the same up to moving terms across,
            // `a − b ≠ 0` of `a ≠ b`: where Lean writes them alike the fact
            // is the claim; otherwise an equation denying the claim gives
            // one denying the fact by linear arithmetic.
            if fact.says.text() == wanted.text() {
                return Route::Built(Proof::Term(fact.proof));
            }
            if r.turned {
                let turned = Printed::applied(
                    "Ne.symm",
                    Source::Mathlib,
                    vec![fact.proof.clone()],
                    LeanType::Prop,
                );
                if turned_relation_text(&fact.says).as_deref() == Some(&wanted.text()) {
                    return Route::Built(Proof::Term(turned));
                }
            }
            let mut with = vec![super::super::tactics::hyp("h")];
            for f in &part.uses {
                match self.order_fact(f, w) {
                    Route::Built(t)
                        if !super::super::doc::forms::relation_types_apart(
                            &t.says, &wanted,
                        ) =>
                    {
                        with.push(t.proof)
                    }
                    Route::Built(_) => {
                        return Route::no(
                            "a define an order step adds, in another type",
                        );
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            let equal = split_linarith(&[], with);
            let body = Printed::of(
                TermKind::App {
                    head: Box::new(fact.proof),
                    args: vec![super::super::doc::Arg::Explicit(equal)],
                    explicit: false,
                },
                LeanType::Prop,
            );
            return Route::Built(Proof::Term(Printed::of(
                TermKind::Lambda {
                    letters: vec!["h".to_string()],
                    body: Box::new(body),
                },
                LeanType::Prop,
            )));
        }
        let mut facts = Vec::new();
        let mut split = Vec::new();
        let read = part
            .uses
            .iter()
            .map(|f| (f, false))
            .chain(part.split.iter().map(|f| (f, true)));
        for (f, apart) in read {
            match self.order_fact(f, w) {
                Route::Built(t) if apart => split.push(t),
                Route::Built(t) => facts.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A define's equation the step reads written out, in a wider type
        // than the claim and every other fact, `(e : ℚ) = p / d` beside `0
        // < e` and `e ≠ 1` in ℤ, ties its letter to a value none of them
        // holds, and would take them to that type, where the letter is no
        // longer whole: it is left out.
        let claim_in = number_type(&wanted);
        let others = facts
            .iter()
            .chain(&split)
            .filter(|f| !f.define)
            .map(|f| number_type(&f.says))
            .fold(claim_in, |a, b| a.max(b));
        facts.retain(|f| !f.define || number_type(&f.says) <= others);
        // The widest type among the claim and the facts.
        let mut widest = claim_in;
        for f in facts.iter().chain(&split) {
            match (number_type(&f.says), widest) {
                (Some(t), Some(u)) => widest = Some(t.max(u)),
                (None, None) => {}
                _ => {
                    return Route::no(
                        "an order step's facts in types other than numbers",
                    )
                }
            }
        }
        let widened = |f: OrderFactTerm| self.fact_in_type(f, widest, w);
        let stated: Vec<&Printed> = std::iter::once(&wanted)
            .chain(facts.iter().chain(&split).map(|f| &f.says))
            .collect();
        let ties = reciprocals(&stated);
        let mut added = Vec::new();
        for f in facts {
            match widened(f) {
                Route::Built(t) => added.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        added.extend(ties);
        let mut apart = Vec::new();
        for f in split {
            match widened(f) {
                Route::Built(t) => apart.push(t),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let linear = split_linarith(&apart, added);
        let narrower = match (claim_in, widest) {
            (Some(c), Some(u)) if c != u => Some(u),
            _ => None,
        };
        if let Some(to) = narrower {
            if part.weakened.is_some() {
                return Route::no(
                    "a disequality weakened from an order in a wider type",
                );
            }
            let says = match w.closed_formula(node, to) {
                Route::Built(s) => s,
                Route::Declined(d) => return Route::Declined(d),
            };
            let proof = match linear.kind {
                TermKind::By(proof) => *proof,
                _ => Proof::By(Tactic::Exact(linear)),
            };
            // A claim of ℚ is taken back from ℝ by ℚ's cast lemmas
            // (`real_to_rat`).
            if rat_crossing(&wanted, &says) {
                return match real_to_rat(proof, &wanted, says) {
                    Some(p) => Route::Built(p),
                    None => Route::no("a claim of ℚ taken from ℝ by no relation lemma"),
                };
            }
            // `exact_mod_cast` takes the claim back where `norm_cast` moves
            // every cast of both statements (the cast table).
            if !(super::super::casts::norm_cast_moves_all(&says)
                && super::super::casts::norm_cast_moves_all(&wanted))
            {
                return Route::no("an order step's claim in a narrower type than norm_cast takes it to");
            }
            return Route::Built(Proof::By(super::super::tactics::exact_mod_cast(
                super::super::tactics::bracket(shown(says, proof)),
            )));
        }
        let weak = |lemma: &str| {
            Printed::applied(
                lemma,
                Source::Mathlib,
                vec![linear.clone()],
                LeanType::Prop,
            )
        };
        Route::Built(match part.weakened {
            Some(Weakened::Below) => Proof::Term(weak("ne_of_lt")),
            Some(Weakened::Above) => Proof::Term(weak("ne_of_gt")),
            None => match linear.kind {
                TermKind::By(proof) => *proof,
                _ => Proof::Term(linear),
            },
        })
    }

    /// A fact an order step adds, from where the checker found it
    /// (`OrderFact`): the term that proves it, and what Lean states it as.
    pub(super) fn order_fact(
        &self,
        fact: &crate::checker::record::OrderFact,
        w: &Writer,
    ) -> Route<OrderFactTerm> {
        use crate::checker::record::OrderFact;
        let (proof, says, node) = match fact {
            OrderFact::Line(at) => match self.line_says(at) {
                Route::Built((proof, says)) => (proof, says, at.written.clone()),
                Route::Declined(d) => return Route::Declined(d),
            },
            // A function the header lets on a domain: its equation at the
            // argument the step applies it to, `hD1 _ ha : q a = a + 1`, the
            // membership from where the record found it (`applied_domains`).
            OrderFact::Define(label) if self.header_function_named(label).is_some() => {
                return self.header_equation_at(label, w)
            }
            OrderFact::Define(label) => {
                let lines =
                    self.trees.get(label).map(Vec::as_slice).unwrap_or_default();
                let [line] = lines else {
                    return Route::no("a define an order step adds, not one equation");
                };
                let Some(name) = &line.name else {
                    return Route::no(
                        "a define an order step adds, with no name in Lean",
                    );
                };
                let says = match self.line_statement(&line.cited()) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                (super::super::tactics::hyp(name), says, line.node.clone())
            }
            // A define's kind is a line of its letter, `n ∈ ℕ`, proved by
            // the order Lean names beside it (`kinded_witness`).
            OrderFact::Kind {
                define,
                implied,
                written,
            } => {
                let Some([kind]) =
                    self.trees.get(&format!("{define} kind")).map(Vec::as_slice)
                else {
                    return Route::no("a define's kind Lean names no line of");
                };
                let implies = match w.formula(written) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let proof = match self.implied_proof(&kind.cited(), *implied, &implies)
                {
                    Route::Built(proof) => proof,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Lean states the kind of the letter, as its line does, `0 <
                // n`, where the page's fact is of the define's value.
                match self.line_statement(&kind.cited()) {
                    Route::Built(says) => (proof, says, kind.node.clone()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            OrderFact::Requires {
                line,
                implied: None,
            } => {
                let Some(step) = self.step_now.get().map(|i| &self.thm.steps[i]) else {
                    return Route::no("a requires line outside a step");
                };
                let name = format!("r{}_{}", step.line, line + 1);
                let Some([said]) = self.trees.get(&name).map(Vec::as_slice) else {
                    return Route::no(
                        "a requires line above, not one sentence in Lean",
                    );
                };
                let says = match self.line_statement(&said.cited()) {
                    Route::Built(s) => s,
                    Route::Declined(d) => return Route::Declined(d),
                };
                (super::super::tactics::hyp(&name), says, said.node.clone())
            }
            OrderFact::Requires {
                implied: Some(_), ..
            } => {
                return Route::no(
                    "what a requires line above implies, in an order step",
                );
            }
            // The member's fact is its guard, `h_i : 0 < i` of `intro i
            // h_i` over ℕ, which is what the membership says of i.
            OrderFact::Member { implied, written } => {
                let guards: Vec<String> = self
                    .intros_now
                    .borrow()
                    .iter()
                    .filter(|n| n.starts_with("h_"))
                    .cloned()
                    .collect();
                let [guard] = guards.as_slice() else {
                    return Route::no(
                        "a member's fact where the claim opens no one member",
                    );
                };
                let crate::citing::Implication::SystemFact { lemma } = implied else {
                    return Route::no("a member's fact other than its system's bound");
                };
                let proof = match system_fact_field(lemma) {
                    Some(None) => super::super::tactics::hyp(guard),
                    Some(Some(field)) => {
                        fields(super::super::tactics::hyp(guard), &[field])
                    }
                    None => {
                        return Route::no("a member's fact its guard does not give")
                    }
                };
                match w.formula(written) {
                    Route::Built(says) => (proof, says, written.clone()),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        };
        // A line Lean states under the binders the claim is opened under,
        // a requires line said "for all x ∈ [0, 1]" as its claim is, is
        // read at them, `r1 x h_x`; linear arithmetic adds relations, not a
        // "for all" of them.
        let read_at = read_at_intros(&proof, &says, &self.intros_now.borrow());
        let ((proof, says), at_intros) = match read_at {
            Some(read) => (read, true),
            None if matches!(
                says.kind,
                super::super::doc::TermKind::Quantified { .. }
            ) =>
            {
                return Route::no("a \"for all\" an order step adds as a whole");
            }
            None => ((proof, says), false),
        };
        Route::Built(OrderFactTerm {
            proof,
            says,
            node,
            widens: !at_intros && !matches!(fact, OrderFact::Kind { .. }),
            define: matches!(fact, OrderFact::Define(_)),
        })
    }

    /// The equation of a function the header lets, `label`, at the one
    /// argument the step applies it to (`applied_domains`): `hD1 _ ha`,
    /// saying `q a = a + 1`, ha the membership from where the record found
    /// it. Declined where the step applies it at no argument or at several.
    fn header_equation_at(&self, label: &str, w: &Writer) -> Route<OrderFactTerm> {
        use super::super::doc::TermKind;
        let Some(step) = self.step_now.get().map(|i| &self.thm.steps[i]) else {
            return Route::no("a define an order step adds outside a step");
        };
        let at: Vec<&crate::checker::record::AppliedDomain> = self
            .rec
            .applied_domains
            .get(&step.just.line)
            .map(|all| all.iter().filter(|a| a.label == label).collect())
            .unwrap_or_default();
        let [applied] = at.as_slice() else {
            return Route::no(
                "a function the header lets, applied at other than one argument",
            );
        };
        let Some(hyp) = self.header_function_named(label) else {
            return Route::no(
                "a define an order step adds, no function the header lets",
            );
        };
        let Some(said) = self.header_equations.get(&hyp) else {
            return Route::no("a function the header lets, with no equation in Lean");
        };
        // `∀ j : ℤ, 0 < j → q j = j + 1` at the argument.
        let TermKind::Quantified {
            letter,
            letter_ty,
            body,
            ..
        } = &bare_term(said).kind
        else {
            return Route::no("a function the header lets, said for no argument");
        };
        let arg = match letter_ty {
            super::super::doc::LeanType::Num(n) => {
                match w.number_fixed(&applied.arg, *n) {
                    Route::Built(a) => a,
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::no("a function the header lets on other than numbers"),
        };
        // The body past the guard, `q a = a + 1`: the quantifier holds the
        // guard apart from it.
        let statement = body
            .substituted(&std::collections::BTreeMap::from([(letter.clone(), arg)]));
        let domain = match self.domain_proof(&applied.said, None) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let proof =
            super::terms::hyp_applied(&hyp, vec![super::terms::elided_term(), domain]);
        // The equation as the page writes it: the application the step
        // reads, and the define's rule at its argument.
        let node = match self.header_equation_node(label, &applied.arg) {
            Some(n) => n,
            None => {
                return Route::no("a function the header lets, read on no page line")
            }
        };
        Route::Built(OrderFactTerm {
            proof,
            says: statement,
            node,
            widens: true,
            define: true,
        })
    }

    /// Each function the header lets that a step citing an item applies, at
    /// each argument the record found its domain said for
    /// (`applied_domains`): the define as `put_define` writes it out, and its
    /// equation there, `hD1 _ hH2 : V N = {S ∈ 𝒫 (Set.Icc 1 N) | N ∈ S}`.
    /// Declined where the record found no domain for a header function the
    /// step cites.
    pub(super) fn header_functions_applied(
        &self,
        just: &Justification,
    ) -> Route<Vec<HeaderApplied>> {
        let mut out = Vec::new();
        for label in just
            .refs
            .iter()
            .filter(|r| self.header_function_named(r).is_some())
        {
            let Some(hyp) = self.header_function_named(label) else {
                continue;
            };
            let at: Vec<&crate::checker::record::AppliedDomain> = self
                .rec
                .applied_domains
                .get(&just.line)
                .map(|all| all.iter().filter(|a| a.label == *label).collect())
                .unwrap_or_default();
            if at.is_empty() {
                return Route::no(
                    "a function the header lets, applied where no domain is recorded",
                );
            }
            let Some(define) = self.header_define(label, &hyp) else {
                return Route::no("a function the header lets, read on no page line");
            };
            for applied in at {
                // At a sum's index, under the sum: each term the sum adds by
                // the equation at its index, whose range the record found
                // inside the domain, `Finset.sum_congr rfl (by intro k h;
                // exact hD1 k (…))`, k's fact from its place in the range.
                if let crate::checker::record::DomainSaid::SumRange = applied.said {
                    out.push(HeaderApplied {
                        define: define.clone(),
                        equation: sum_term_by_term(&hyp, &applied.arg.text),
                    });
                    continue;
                }
                let domain = match self.domain_proof(&applied.said, None) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                out.push(HeaderApplied {
                    define: define.clone(),
                    equation: super::terms::hyp_applied(
                        &hyp,
                        vec![super::terms::elided_term(), domain],
                    ),
                });
            }
        }
        Route::Built(out)
    }

    /// The define of a function the header lets, `label`, as a citation
    /// writes it out (`CitedDefine`): its name, letter and rule as the page
    /// reads them, its equation the binder `hyp`.
    fn header_define(&self, label: &str, hyp: &str) -> Option<CitedDefine> {
        let d = self.thm.defines.iter().find(|d| d.label == label)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&d.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let crate::corpus::RuleText::Term(body_text) = &def.body else {
            return None;
        };
        let body = self
            .rec
            .page
            .entries()
            .find(|(key, _)| key.line == d.line && key.text == *body_text)
            .map(|(_, node)| node)?;
        Some(CitedDefine {
            name: Node::name(crate::formula::Sort::none(), &def.name),
            value: body.clone(),
            proof: hyp.to_string(),
            param: Some(param.name.clone()),
        })
    }

    /// The equation of the function the header define `label` lets, at
    /// `arg`, as the page writes it: the application the page reads, q(a),
    /// equal to the define's rule with its letter given `arg`, a + 1. None
    /// where the define or the application reads on no line of the page.
    fn header_equation_node(&self, label: &str, arg: &Node) -> Option<Node> {
        let d = self.thm.defines.iter().find(|d| d.label == label)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&d.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let crate::corpus::RuleText::Term(body_text) = &def.body else {
            return None;
        };
        let body = self
            .rec
            .page
            .entries()
            .find(|(key, _)| key.line == d.line && key.text == *body_text)
            .map(|(_, node)| node)?;
        let application = self.rec.page.entries().find_map(|(_, node)| {
            node.walk().into_iter().find(|n| {
                matches!(
                    (n.notation(), n.children.as_slice()),
                    (crate::notations::APPLICATION, [f, a])
                        if f.is_name() && *f.text == def.name && a.spelt_alike(arg)
                )
            })
        })?;
        let put = crate::matching::Binding::from([(
            crate::formula::symbol::Symbol::of(&param.name),
            arg.clone(),
        )]);
        let rule = crate::matching::substitute_apart_by(
            body,
            &put,
            &self.sources.checked.grammar.binders(),
        );
        Some(crate::formula::page::made(
            self.writer.grammar,
            crate::notations::EQUALS,
            vec![application.clone(), rule],
        ))
    }

    /// `join`: sentence `k` of the claim, `node`, from where the checker
    /// found each of its parts (`CheckedTheorem::joined`), each part the
    /// line that says it, in `⟨…⟩` as the sentence joins them.
    pub(super) fn join_proof(
        &self,
        line: usize,
        k: usize,
        node: &Node,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let Some(parts) = self.rec.joined.get(&line).and_then(|j| j.get(k)) else {
            return Route::no("a join the checker placed no parts of");
        };
        let mut left = parts.iter();
        let term = match self.joined_term(node, &mut left, w) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        match left.next() {
            None => Route::Built(super::super::doc::Proof::Term(term)),
            Some(_) => Route::no("a join recorded with more parts than its claim"),
        }
    }

    /// The proof of `node`, a sentence of a join or a part of one, taking
    /// its parts joined by "and" from `parts` left to right: each the line
    /// that says it, read at the names the claim is opened under where
    /// Lean states it under them.
    pub(super) fn joined_term<'p>(
        &self,
        node: &Node,
        parts: &mut impl Iterator<Item = &'p FirstAt>,
        w: &Writer,
    ) -> Route<Printed> {
        if let Some((left, right)) = w.and_sides(node) {
            let mut items = Vec::new();
            for child in [left, right] {
                match self.joined_term(child, parts, w) {
                    Route::Built(t) => items.push(t),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            return Route::Built(super::super::expr::anonymous(items));
        }
        // a = b = c: its links, each a part, as the checker reads a chain
        // (`page::chain_links`) and the writer joins them.
        if let Some(links) = crate::formula::page::chain_links(w.grammar, node) {
            let mut items = Vec::new();
            for link in &links {
                match self.joined_term(link, parts, w) {
                    Route::Built(t) => items.push(t),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            return Route::Built(super::super::expr::anonymous(items));
        }
        let Some(at) = parts.next() else {
            return Route::no("a join recorded with fewer parts than its claim");
        };
        let wanted = match w.formula(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A part Lean's types make true, `A ∈ ℂ` of a letter in ℂ, is
        // `True`, and its line is written nowhere.
        if wanted.is_truth() {
            return Route::Built(Printed::constant(
                "trivial",
                super::super::doc::Source::Core,
                super::super::doc::LeanType::Prop,
            ));
        }
        let (proof, says) = match self.line_says(at) {
            Route::Built(found) => found,
            Route::Declined(d) => return Route::Declined(d),
        };
        let (proof, says) = read_at_intros(&proof, &says, &self.intros_now.borrow())
            .unwrap_or((proof, says));
        if super::super::doc::forms::relation_types_apart(&says, &wanted) {
            return Route::no(
                "a part of a join Lean states in another type than its line",
            );
        }
        Route::Built(proof)
    }

    /// `antisymmetry`: `le_antisymm` of the line that says the claim's left
    /// side is at most its right and the line that says the converse, as
    /// the checker paired them (`CheckedTheorem::antisymmetric`).
    pub(super) fn antisymmetry_proof(
        &self,
        line: usize,
        node: &Node,
        w: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::{LeanType, Proof, Source};
        let Some(rec) = self.rec.antisymmetric.get(&line) else {
            return Route::no("an antisymmetry step the checker paired no lines for");
        };
        let wanted = match w.formula(node) {
            Route::Built(s) => s,
            Route::Declined(d) => return Route::Declined(d),
        };
        let mut proofs = Vec::new();
        for at in [&rec.below, &rec.above] {
            let (proof, says) = match self.line_says(at) {
                Route::Built(found) => found,
                Route::Declined(d) => return Route::Declined(d),
            };
            if super::super::doc::forms::relation_types_apart(&says, &wanted) {
                return Route::no(
                    "an antisymmetry step's line in another type than its claim",
                );
            }
            proofs.push(proof);
        }
        Route::Built(Proof::Term(Printed::applied(
            "le_antisymm",
            Source::Mathlib,
            proofs,
            LeanType::Prop,
        )))
    }

    /// `instantiate`: the "for all" line at the values given, each guard
    /// proved from where the checker found it supplied (`value_guard`), and
    /// an "if" in it applied where the claim is what it gives.
    pub(super) fn instantiate(
        &self,
        just: &Justification,
        k: usize,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let Some(target) = just
            .target
            .as_deref()
            .or(just.refs.first().map(String::as_str))
        else {
            return Route::no("an instantiate of no line");
        };
        // What the check found the step's lines hold, by which a value a
        // line says is an integer is that line's number (`integer_line`).
        *self.held_now.borrow_mut() = self.held_at(just.line);
        let stated = self.stated_claim(just.line, node);
        let claim = match stated {
            Some(printed) => Route::Built(printed),
            None => writer.formula(node),
        };
        // The sentence, or the part of one, of the line the checker found
        // the instance in (`CheckedTheorem::instantiated`).
        let Some(recorded) = self.rec.instantiated.get(&just.line) else {
            return Route::no(format!(
                "an instantiate of {target} the checker read no instance of"
            ));
        };
        let part = match self.line_part(&recorded.at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A "for all" read at the block's letter, with no values given, is
        // the instance itself; with values, they are given to the reading.
        let at_letter = recorded
            .at
            .sentence
            .is_some_and(|k| k >= self.written_sentences(&recorded.at.line));
        if at_letter && just.values.is_empty() {
            let instance = self.line_statement(&part);
            let page = part.node.clone();
            return self.instance_closed(
                node,
                claim,
                part.proof,
                instance,
                None,
                Some(&page),
                recorded,
            );
        }
        let part = &part;
        let (line, name) = (&part.node, &part.proof);
        // The values as Lean gives them to the line's letters, each with
        // whether a guard's proof follows it.
        let mut given: Vec<(Printed, bool)> = Vec::new();
        let mut args: Vec<Printed> = Vec::new();
        // The values as the page gives them, each to its letter.
        let mut binding = crate::matching::Binding::new();
        let mut body = line;
        while matches!(
            body.notation(),
            crate::notations::FOR_ALL | crate::notations::FOR_ALL_SETS
        ) {
            // For all sets X: the set given it, `∀ X : Set α` taking no
            // guard after it.
            if let [letter, inner] = body.children.as_slice() {
                let Some((_, given_set)) =
                    just.values.pairs().find(|(n, _)| *n == &*letter.text)
                else {
                    return Route::no(format!("no set given {}", letter.text));
                };
                let value = match self.tree(given_set) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match writer.set_term(&value) {
                    Route::Built(p) => {
                        given.push((p.clone(), false));
                        args.push(p);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                binding.insert(crate::formula::symbol::Symbol::of(&letter.text), value);
                body = inner;
                continue;
            }
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            // A letter given no value is read at the block's letter of its
            // type the claim writes and the line does not, as the checker
            // reads it.
            let value = match just.values.pairs().find(|(n, _)| *n == &*letter.text) {
                Some((_, given)) => match self.tree(given) {
                    Route::Built(v) => v,
                    Route::Declined(d) => return Route::Declined(d),
                },
                None => {
                    // The names the line writes free: a letter it binds
                    // itself, as the block's may be named, is not one.
                    let own = crate::matching::free_names(
                        line,
                        &self.sources.checked.grammar.binders(),
                    );
                    // A range's letter is an integer.
                    let ty = if set.notation() == crate::notations::INTEGER_RANGE {
                        Some(super::super::templates::Num::Int)
                    } else {
                        super::super::expr::system_of(set)
                            .map(super::super::expr::letter_type)
                    };
                    // A set's letter is a member of its kind.
                    let member = writer.members_of(set).map(|m| m.letter());
                    // Where several fit, a letter given to another of the
                    // line's letters, the N of `m := N`, is that one's value
                    // and not this one's.
                    let given: Vec<String> = just
                        .values
                        .pairs()
                        .filter_map(|(_, v)| self.tree(v).built())
                        .flat_map(|v| v.names())
                        .collect();
                    let fits = |n: &String| {
                        let has = writer.letters.get(n.as_str());
                        !own.contains(n)
                            && (ty.is_some_and(|t| has == Some(&LetterType::Number(t)))
                                || (member.is_some() && has == member.as_ref()))
                    };
                    let mut at: Vec<String> =
                        node.names().into_iter().filter(|n| fits(n)).collect();
                    if at.len() > 1 {
                        at.retain(|n| !given.contains(n));
                    }
                    // A claim that is itself a "for all" keeps the letters
                    // given no value: the line is read at those given.
                    let [at] = at.as_slice() else {
                        if node.notation() == crate::notations::FOR_ALL {
                            break;
                        }
                        return Route::no(format!("no value for {}", letter.text));
                    };
                    Node::name(letter.sort.clone(), at)
                }
            };
            binding.insert(
                crate::formula::symbol::Symbol::of(&letter.text),
                value.clone(),
            );
            // A member of a set: the value, and that it is in the set.
            if let Some(members) = writer.members_of(set) {
                match writer.element_term(&value, &members) {
                    Route::Built(p) => {
                        given.push((p.clone(), true));
                        args.push(p);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                let Some(guard) = self.value_guard(recorded, &letter.text, &value)
                else {
                    return Route::no(UNSUPPLIED_GUARD);
                };
                args.push(guard);
                body = inner;
                continue;
            }
            // A function or map between sets: it, and that it maps the one
            // into the other.
            if let (crate::notations::FUNCTIONS_FROM, [from, to]) =
                (set.notation(), set.children.as_slice())
            {
                match self.function_given(writer, &value, from, to) {
                    Route::Built(p) => {
                        given.push((p.clone(), true));
                        args.push(p);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                let Some(guard) = self.value_guard(recorded, &letter.text, &value)
                else {
                    return Route::no(UNSUPPLIED_GUARD);
                };
                args.push(guard);
                body = inner;
                continue;
            }
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
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
            // A value of a wider type that a line says is in the letter's,
            // d·s(r) ∈ ℤ of rationals: the number that line gives, as a
            // citation's value is (`letter_given`).
            let fixed = match writer.number_fixed(&value, ty) {
                Route::Declined(d) => match self.integer_line(&value, ty) {
                    Some(line) => {
                        let printed = super::super::tactics::bracket(line.chosen(ty));
                        self.said_used.borrow_mut().push(SaidUsed {
                            line,
                            term: self.writer.grammar.print(&value),
                        });
                        Route::Built(printed)
                    }
                    None => Route::Declined(d),
                },
                built => built,
            };
            match fixed {
                Route::Built(p) => {
                    given.push((p.clone(), guarded));
                    args.push(p);
                    if guarded {
                        match self.value_guard(recorded, &letter.text, &value) {
                            Some(g) => args.push(g),
                            None => return Route::no(UNSUPPLIED_GUARD),
                        }
                    }
                }
                Route::Declined(d) => return Route::Declined(d),
            }
            body = inner;
        }
        let taken_off = recorded.conditions.len();
        let instance = match self.writer.formula(line) {
            Route::Built(l) => lean_instance(&l, &given, taken_off),
            Route::Declined(d) => Route::Declined(d),
        };
        // Each condition the checker took off on the way to the claim, from
        // where it found it supplied, as Lean states it at the values.
        for (k, condition) in recorded.conditions.iter().enumerate() {
            let proof = match &instance {
                Route::Built(i) => {
                    match self.counts_apart(&condition.by, &i.conditions[k]) {
                        Some(met) => met.built(),
                        None => self
                            .supplied_proof(&condition.by, &i.conditions[k], None)
                            .built(),
                    }
                }
                Route::Declined(_) => None,
            };
            match proof {
                Some(p) => args.push(p),
                None => {
                    return Route::no("a condition of an instance no line supplies")
                }
            }
        }
        let instance = instance.map(|i| i.left);
        // What is left of the line once its letters are given and its
        // conditions taken off, at the values, as the step's lines write it.
        let left = (0..taken_off).try_fold(body, |at, _| {
            node_consequent(at).filter(|_| at.notation() != BICONDITIONAL)
        });
        let written = left.and_then(|at| self.written_at_values(at, &binding));
        let page = left.map(|at| self.at_values(at, &binding));
        let applied = Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(name.clone()),
                args: args
                    .into_iter()
                    .map(super::super::doc::Arg::Explicit)
                    .collect(),
                explicit: false,
            },
            ty: Some(super::super::doc::LeanType::Prop),
        };
        let mut proof = super::super::tactics::bracket(applied);
        let (mut instance, mut written, mut page) = (instance, written, page);
        // A claim of several sentences the instance says together, "h(s) ∈ B
        // ∖ R. g(h(s)) = s." of "… and …": the checker met the claim whole
        // with it, and sentence k is its part k, `.1` or `.2`.
        let sentences = self
            .step_now
            .get()
            .map_or(1, |i| self.thm.steps[i].claim.sentences().len());
        if sentences > 1 {
            if let Route::Built(whole) = &instance {
                let parts = super::conversions::conjoined_parts(whole);
                if parts.len() == sentences {
                    instance = Route::Built(parts[k].clone());
                    proof = fields(proof, &projection_path(k, sentences));
                    written = written.and_then(|w| {
                        super::conversions::conjoined_parts(&w).get(k).cloned()
                    });
                    page = None;
                }
            }
        }
        self.instance_closed(
            node,
            claim,
            proof,
            instance,
            written,
            page.as_ref(),
            recorded,
        )
    }

    /// The proof of the claim `node`, which Lean states as `claim`, from
    /// `proof`, an instance of a line that
    /// Lean states as `instance`, by how the checker met the instance with
    /// the claim (`Instantiated::meeting`). Where Lean's statements of the
    /// two differ otherwise, the instance, turned where the checker turned
    /// it, is taken down to the claim's field where it is in ℂ, each
    /// complex operation read as the real one cast
    /// (`spelling::read_from_complex`); and otherwise reaches the claim by
    /// the closer whose Lean fact holds of the two, and is declined where
    /// none does. Before those rows, the instance as the step's lines
    /// write it at the values, `written`, read from the line and met with
    /// the claim, as a citation's is (`read_in_spelling`). Before that, a
    /// power the one writes as an integer power and the other to its
    /// exponent's `toNat` is converted as a citation's is (`forms_converted`),
    /// each exponent's fact from the record, `page` being the instance as a
    /// page formula at its values.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn instance_closed(
        &self,
        node: &Node,
        claim: Route<Printed>,
        proof: Printed,
        instance: Route<Printed>,
        written: Option<Printed>,
        page: Option<&Node>,
        recorded: &crate::checker::record::Instantiated,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::forms;
        let lean = match (&instance, claim.clone()) {
            (Route::Built(says), Route::Built(wanted)) => Some((says.clone(), wanted)),
            _ => None,
        };
        // An instance Lean takes as the claim, once turned where the checker
        // turned it: a function applied worked out, a bound letter renamed, a
        // `set` letter read as its value, the types the same
        // (`forms::one_term_once_set`). `exact` checks just that.
        if let Some((says, wanted)) = &lean {
            let turned = recorded.meeting.turned;
            let facing = match turned {
                true => forms::turned_statement(says),
                false => says.clone(),
            };
            if forms::one_term_once_set(&facing, wanted, &self.set_values()) {
                return Route::Built(super::super::doc::Proof::By(Tactic::Exact(
                    faced(proof, facing_of_turned(turned)),
                )));
            }
        }
        // A value given as the number a line names, p := d·s(r) of `d·s(r) ∈
        // ℤ`, met as written: the step's proof first puts the claim in terms
        // of that number (`specs_in`, `proof_of`), and what is left is the
        // instance with its casts, as a citation so given is closed.
        let met = &recorded.meeting;
        let through_named = !self.specs_in(node, &self.said_used.borrow()).is_empty();
        if through_named
            && met.identities.is_empty()
            && !met.turned
            && !met.permuted
            && !met.respelled
        {
            return Route::Built(super::super::doc::Proof::By(
                super::super::tactics::exact_mod_cast(proof),
            ));
        }
        let met = match (instance, claim) {
            // Lean's statement of the instance is the claim's as Lean
            // writes both, once turned where the checker turned it, or
            // apart only in casts the writer placed; or the checker dropped
            // identity elements, which `simpa only` takes. Any other
            // difference is in the types Lean gives the line's letters, ℝ
            // for a claim in ℚ, which the writer does not name.
            (Route::Built(says), Route::Built(wanted)) => {
                let met = &recorded.meeting;
                let lean_says = match met.turned {
                    true => forms::turned_statement(&says),
                    false => says.clone(),
                };
                let values = self.set_values();
                // Alike as written is alike in one type: `1 ≤ 1/2` in ℝ and
                // in ℚ are written alike and are two statements.
                let two_types = forms::relation_types_apart(&lean_says, &wanted);
                let lean_alike = (forms::written_alike(&lean_says, &wanted)
                    && !two_types)
                    || forms::casts_differ(&lean_says, &wanted, &values).is_some();
                match lean_alike || !met.identities.is_empty() {
                    true => self.met_proof(proof.clone(), &says, &wanted, met),
                    false => None,
                }
            }
            _ => None,
        };
        if let Some(proved) = met {
            return Route::Built(super::super::doc::Proof::By(proved.closer()));
        }
        if let (Some((says, wanted)), Some(page)) = (&lean, page) {
            if let Some(converted) = self.powers_converted_at(
                &[node, page],
                says,
                wanted,
                &proof,
                recorded.meeting.turned,
            ) {
                return Route::Built(converted);
            }
        }
        let read = match (&written, &lean) {
            (Some(written), Some((says, wanted))) => {
                let said = match one_statement(written, says) {
                    true => written,
                    false => says,
                };
                let claim = StepClaim {
                    printed: wanted,
                    stated: false,
                };
                self.read_in_spelling(None, &proof, said, written, claim)
            }
            _ => None,
        };
        if let Some(read) = read {
            return Route::Built(read);
        }
        // The instance turned round where the checker turned it.
        let proof = faced(proof, facing_of_turned(recorded.meeting.turned));
        // An instance in a wider field than the claim's, ℝ for a claim in ℚ,
        // taken down to it by the writer's own conversion (`read_down`).
        let down = lean
            .as_ref()
            .and_then(|(says, wanted)| read_down(&proof, says, wanted));
        if let Some(down) = down {
            return Route::Built(super::super::doc::Proof::By(down));
        }
        // The two in one type, met by the checker: each closer where its
        // Lean fact holds of Lean's statements of them. An equation of
        // numbers whose casts `push_cast` all moves (the cast table) is the
        // instance once pushed in and put by the ring's laws,
        // `linear_combination`. Any other is declined.
        let Some((says, wanted)) = lean else {
            return several_ways(ListReason::CitedUnstated);
        };
        let says = match recorded.meeting.turned {
            true => super::super::doc::forms::turned_statement(&says),
            false => says,
        };
        // An instance that counts a set as some natural number, for a claim
        // that counts it finite (`count_witness_met`).
        if let Some(met) = self.count_witness_met(&proof, &says, &wanted) {
            return Route::Built(met);
        }
        let of_numbers = node.children.iter().all(|c| c.sort.is("number"));
        let pushed = super::super::casts::push_cast_moves_all_in_sides(&says)
            && super::super::casts::push_cast_moves_all_in_sides(&wanted);
        let atoms = same_ring_atoms(&says, &wanted, &self.set_values());
        Route::Built(super::super::doc::Proof::By(match node.notation() {
            EQUALITY if of_numbers && pushed && atoms => {
                ring_combination(&proof, &says, &wanted)
            }
            _ => {
                return several_ways(apart(
                    node,
                    &says,
                    &wanted,
                    &self.set_values(),
                    Some(Facing::Straight),
                ))
            }
        }))
    }

    /// The proof of `wanted`, a finite set's count in ℤ, `(U.ncard : ℤ) =
    /// j`, from `proof` of a statement that counts it as some natural
    /// number, `∃ m : ℕ, S.encard = m ∧ (m : ℤ) = j`
    /// (`Writer::count_equals_number`), S the set the claim counts or the
    /// value of the `set` letter it counts: the number taken out, the
    /// claim's set read as its value, its count in ℕ as the one in ℕ∞ in ℕ
    /// (`Set.ncard_def`), and the number's equation is the claim. None for
    /// any other two statements.
    pub(super) fn count_witness_met(
        &self,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<super::super::doc::Proof> {
        use super::super::doc::{CountForm, TermKind};
        use super::super::tactics as t;
        let TermKind::Quantified {
            quant: super::super::doc::Quant::Exists,
            letter,
            guard: Some(guard),
            body,
            ..
        } = &says.kind
        else {
            return None;
        };
        let counted = |p: &Printed, form: CountForm| match &uncast(p).kind {
            TermKind::Count { set, form: f } if *f == form => Some((**set).clone()),
            _ => None,
        };
        let (g_left, _) = equation_sides(guard)?;
        let (b_left, number) = equation_sides(body)?;
        let (w_left, w_right) = equation_sides(wanted)?;
        let said_set = counted(g_left, CountForm::Extended)?;
        let claim_set = counted(w_left, CountForm::Natural)?;
        let named = matches!(&uncast(b_left).kind, TermKind::Letter(l) if l == letter);
        if !named || uncast(number).untyped() != uncast(w_right).untyped() {
            return None;
        }
        // The claim's set as the statement writes it, or the `set` letter
        // whose value it is, read as that value by the letter's equation.
        let mut rules = Vec::new();
        if claim_set.untyped() != said_set.untyped() {
            let TermKind::Letter(name) = &claim_set.kind else {
                return None;
            };
            let value = self.set_values().get(name)?.clone();
            if value.value.untyped() != said_set.untyped() {
                return None;
            }
            rules.push(t::hyp(&value.equation));
        }
        let (hm, he) = ("hm", "he");
        rules.extend([
            t::lemma("Set.ncard_def"),
            t::hyp(hm),
            t::lemma("ENat.toNat_coe"),
        ]);
        Some(super::super::doc::Proof::By(Tactic::Seq(vec![
            Tactic::Obtain {
                names: vec![letter.clone(), hm.to_string(), he.to_string()],
                says: None,
                from: proof.clone(),
            },
            t::call("rw", vec![t::rules(rules)]),
            Tactic::Exact(t::hyp(he)),
        ])))
    }

    /// The proof of `wanted`, a set's count as some natural number, `∃ m :
    /// ℕ, S.encard = m ∧ (m : ℤ) = j` (`Writer::count_equals_number`), from
    /// `proof` of a line that counts it in ℤ, `(S.ncard : ℤ) = j`, of a set
    /// shown finite: the number is the count in ℕ, which is the one in ℕ∞
    /// (`Set.Finite.cast_ncard_eq`), and the line says it is j. None for any
    /// other two statements, or where `set`, S as the page writes it, is
    /// not shown finite.
    pub(super) fn count_witness_made(
        &self,
        set: &Node,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<Printed> {
        use super::super::doc::{CountForm, TermKind};
        let TermKind::Quantified {
            quant: super::super::doc::Quant::Exists,
            guard: Some(guard),
            body,
            ..
        } = &wanted.kind
        else {
            return None;
        };
        let (g_left, _) = equation_sides(guard)?;
        let (_, number) = equation_sides(body)?;
        let (s_left, s_right) = equation_sides(says)?;
        let (
            TermKind::Count {
                set: owed,
                form: CountForm::Extended,
            },
            TermKind::Count {
                set: said,
                form: CountForm::Natural,
            },
        ) = (&uncast(g_left).kind, &uncast(s_left).kind)
        else {
            return None;
        };
        // The number alike, or alike once a numeral's `toNat` the one side
        // writes is worked out, `2 ^ (0 : ℤ).toNat` beside 2 ^ 0, as
        // `met_proof` works it out.
        let written = uncast(number).untyped() == uncast(s_right).untyped();
        let worked = numerals_worked(uncast(number)).untyped()
            == numerals_worked(uncast(s_right)).untyped();
        if owed.untyped() != said.untyped() || !worked {
            return None;
        }
        let proof = match written {
            true => proof.clone(),
            false => {
                use super::super::templates::Num;
                let mut rules: Vec<&'static str> =
                    super::super::doc::forms::to_nat_rules(body)
                        .into_iter()
                        .collect();
                rules.extend(
                    super::super::casts::NUMERAL_CASTS
                        .iter()
                        .filter(|(from, _, _)| matches!(from, Num::Nat | Num::Int))
                        .map(|(_, _, lemma)| *lemma),
                );
                super::super::tactics::by_term(super::super::doc::Proof::By(
                    super::super::tactics::simpa_only(rules, proof.clone()),
                ))
            }
        };
        let finite = self.shown_finite(set)?;
        let counted = Printed::of(
            TermKind::Count {
                set: said.clone(),
                form: CountForm::Natural,
            },
            super::super::doc::LeanType::Num(super::super::templates::Num::Nat),
        );
        let equal = Printed::applied(
            "Eq.symm",
            super::super::doc::Source::Core,
            vec![cast_ncard_eq(&finite)],
            super::super::doc::LeanType::Prop,
        );
        Some(super::super::expr::anonymous(vec![counted, equal, proof]))
    }

    /// The proof of `claim`, a set's count in ℤ, `(T.ncard : ℤ) = j`, from
    /// `proof` of a statement that counts it in ℕ∞ at a value in ℕ₀,
    /// `T.encard = ((j.toNat : ℕ) : ℕ∞)`, as an item states `|Y| = m` of m
    /// ∈ ℕ₀: its count in ℕ is the one in ℕ∞ in ℕ (`Set.ncard_def`), of
    /// any set, and j its own `toNat` (`count_value_nonneg`). None for any
    /// other two statements.
    pub(super) fn count_value_met(
        &self,
        value: &Node,
        proof: &Printed,
        says: &Printed,
        claim: &Printed,
    ) -> Option<super::super::doc::Proof> {
        use super::super::tactics as t;
        let nonneg = self.count_value_nonneg(value, says, claim)?;
        Some(super::super::doc::Proof::By(t::call(
            "rw",
            vec![t::rules(vec![
                t::lemma("Set.ncard_def"),
                proof.clone(),
                t::lemma("ENat.toNat_coe"),
                Printed::applied(
                    "Int.toNat_of_nonneg",
                    super::super::doc::Source::Mathlib,
                    vec![nonneg],
                    super::super::doc::LeanType::Prop,
                ),
            ])],
        )))
    }

    /// Of a statement `says` that counts a set in ℕ∞ at a value in ℕ₀,
    /// `T.encard = ((j.toNat : ℕ) : ℕ∞)`, and a claim that counts it in ℤ,
    /// `(T.ncard : ℤ) = j`, the proof that j is at 0 or above, as the page
    /// says (`nonneg_proof` of `value`, j as the page writes it): what
    /// `count_value_met` takes j's `toNat` off by. None for any other two
    /// statements.
    pub(super) fn count_value_nonneg(
        &self,
        value: &Node,
        says: &Printed,
        claim: &Printed,
    ) -> Option<Printed> {
        count_value_shape(says, claim)?;
        self.nonneg_proof(value, &[])
    }

    /// The proof of `wanted`, a set's count in ℕ∞ at a value in ℕ₀,
    /// `S.encard = ((j.toNat : ℕ) : ℕ∞)`, from `proof` of a line that counts
    /// it in ℤ, `(S.ncard : ℤ) = j`: the count in ℕ∞ as the one in ℕ of a set
    /// shown finite (`Set.Finite.cast_ncard_eq`), j as that count by the
    /// line, and its `toNat` taken off (`Int.toNat_natCast`). None for any
    /// other two statements, or where `set`, S as the page writes it, is not
    /// shown finite.
    pub(super) fn count_value_made(
        &self,
        set: &Node,
        proof: &Printed,
        says: &Printed,
        wanted: &Printed,
    ) -> Option<super::super::doc::Proof> {
        use super::super::tactics as t;
        count_value_shape(wanted, says)?;
        let finite = self.shown_finite(set)?;
        // The line's count taken to ℕ, `S.ncard = j.toNat`, and the goal's
        // count rewritten by it alone: j may stand inside S as well,
        // `{1, …, m}` counted as m, which rewriting j would change.
        let to_nat = Printed::applied(
            "congrArg",
            super::super::doc::Source::Core,
            vec![t::lemma("Int.toNat"), t::bracket(proof.clone())],
            super::super::doc::LeanType::Prop,
        );
        let at = TacticArg::At(vec![super::super::doc::Location::Hypothesis(
            "h".to_string(),
        )]);
        Some(super::super::doc::Proof::By(t::on_h(
            &to_nat,
            vec![
                t::call(
                    "rw",
                    vec![t::rules(vec![t::lemma("Int.toNat_natCast")]), at],
                ),
                t::call(
                    "rw",
                    vec![TacticArg::Rules(vec![
                        t::backwards(cast_ncard_eq(&finite)),
                        t::forwards(t::hyp("h")),
                    ])],
                ),
            ],
        )))
    }

    /// The defines among the lines a step cites, each as its equation says
    /// it: the checker reads such a step with them written out.
    pub(super) fn cited_defines(&self, refs: &[String]) -> Vec<CitedDefine> {
        let mut out: Vec<CitedDefine> = refs
            .iter()
            .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
            .filter(|r| !self.witnessed.contains(*r))
            .flat_map(|r| self.trees.get(r).into_iter().flatten())
            .filter_map(|line| match line.node.children.as_slice() {
                [name, value] if line.node.notation() == EQUALITY && name.is_name() => {
                    Some(CitedDefine {
                        name: name.clone(),
                        value: value.clone(),
                        proof: line.name.clone()?,
                        param: None,
                    })
                }
                _ => None,
            })
            .collect();
        out.extend(refs.iter().filter_map(|r| self.cited_function_define(r)));
        out
    }

    /// A define of a function of one argument `param` on page line `line`,
    /// as the checker reads it apart: the set the argument runs over and
    /// the value. The set is a number system or a range, or else a set of
    /// numbers, X of X ⊆ ℤ; the value is what the line reads besides the set
    /// and the argument, a value that is itself a set of numbers, {|x| : x ∈
    /// 𝒫{1, …, k}}, not taken for the set.
    pub(super) fn function_read(
        &self,
        line: usize,
        param: &str,
    ) -> Route<FunctionRead> {
        let read: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line)
            .map(|(_, node)| node)
            .collect();
        let argument = |n: &Node| n.is_name() && *n.text == *param;
        let Some(domain) = read
            .iter()
            .copied()
            .find(|n| system_or_range(n))
            .or_else(|| {
                read.iter()
                    .copied()
                    .find(|n| !argument(n) && self.numbers_set(n))
            })
            // A set of other members, H of `for c ∈ H` a subgroup's
            // elements: the define is a map on their type. The domain
            // names no argument, which the rule, a set itself perhaps,
            // g[B ∖ f[X]] of `for X ⊆ A`, does.
            .or_else(|| {
                read.iter().copied().find(|n| {
                    !argument(n)
                        && !n.names().iter().any(|m| *m == *param)
                        && self.writer.set_members(n).is_some()
                })
            })
        else {
            return Route::left_out(
                "a define of a function on other than a number system",
            );
        };
        let bodies: Vec<&Node> = read
            .iter()
            .copied()
            .filter(|n| !std::ptr::eq(*n, domain) && !argument(n))
            .collect();
        // A value that is the argument itself, f(n) = n, is read once with it.
        let identity = read.iter().copied().find(|n| argument(n));
        let body = match (bodies.as_slice(), identity) {
            ([body], _) => *body,
            ([], Some(arg)) => arg,
            _ => {
                return Route::left_out(
                    "a define whose value the checker did not read as one term",
                )
            }
        };
        Route::Built(FunctionRead {
            domain: domain.clone(),
            body: body.clone(),
        })
    }

    /// Whether a term is a set of numbers as the writer writes it, X of X ⊆
    /// ℤ.
    pub(super) fn numbers_set(&self, n: &Node) -> bool {
        matches!(
            self.writer.set_members(n),
            Some(super::super::expr::Members::Numbers(_))
        )
    }

    /// A define of a function of one argument a step cites by its label,
    /// q(j) = F(j)²: its name, its body, its argument and the name of the
    /// line Lean's `set` gives it; None for any other reference.
    pub(super) fn cited_function_define(&self, label: &str) -> Option<CitedDefine> {
        let line = self
            .thm
            .defines
            .iter()
            .find(|d| d.label == label && d.line > self.thm.conclusion_line)?;
        let Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return None;
        };
        let [param] = def.params.as_slice() else {
            return None;
        };
        let body = self.function_read(line.line, &param.name).built()?.body;
        let proof = self.named.get(label)?.first()?.clone();
        Some(CitedDefine {
            name: Node::name(crate::formula::Sort::none(), &def.name),
            value: body,
            proof,
            param: Some(param.name.clone()),
        })
    }

    /// A line with a cited define put in: its name for its value, or each
    /// application q(a) of a function's for its body at a.
    pub(super) fn put_define(&self, node: &Node, d: &CitedDefine) -> Node {
        let Some(param) = &d.param else {
            return put_for(node, &d.name, &d.value);
        };
        if let (crate::notations::APPLICATION, [f, a]) =
            (node.notation(), node.children.as_slice())
        {
            if f.is_name() && f.text == d.name.text {
                let a = self.put_define(a, d);
                let put = crate::matching::Binding::from([(
                    crate::formula::symbol::Symbol::of(param),
                    a,
                )]);
                return crate::matching::substitute_apart_by(
                    &d.value,
                    &put,
                    &self.sources.checked.grammar.binders(),
                );
            }
        }
        if node.children.is_empty() {
            return node.clone();
        }
        node.with_children(
            node.children
                .iter()
                .map(|c| self.put_define(c, d))
                .collect(),
        )
    }
}

/// A term with its casts and brackets taken off, `((S.ncard : ℕ) : ℤ)` as
/// `S.ncard`.
fn uncast(p: &Printed) -> &Printed {
    use super::super::doc::TermKind;
    match &p.kind {
        TermKind::Cast { inner, .. } | TermKind::Paren(inner) => uncast(inner),
        _ => p,
    }
}

/// Whether `extended` counts a set in ℕ∞ at a value in ℕ₀, `S.encard =
/// ((j.toNat : ℕ) : ℕ∞)`, and `natural` the same set in ℤ at the same
/// value, `(S.ncard : ℤ) = j`: the two forms of one count the writer
/// meets (`count_value_met`, `count_value_made`). None otherwise.
pub(super) fn count_value_shape(extended: &Printed, natural: &Printed) -> Option<()> {
    use super::super::doc::{CountForm, TermKind};
    let (e_left, e_right) = equation_sides(extended)?;
    let (n_left, n_right) = equation_sides(natural)?;
    let counted = |p: &Printed, form: CountForm| match &uncast(p).kind {
        TermKind::Count { set, form: f } if *f == form => Some((**set).clone()),
        _ => None,
    };
    let e_set = counted(e_left, CountForm::Extended)?;
    let n_set = counted(n_left, CountForm::Natural)?;
    let TermKind::ToNat(j) = &uncast(e_right).kind else {
        return None;
    };
    (e_set.untyped() == n_set.untyped()
        && uncast(j).untyped() == uncast(n_right).untyped())
    .then_some(())
}

/// The proof of `wanted`, a set's count in ℕ∞ at a value in ℕ₀, `S.encard
/// = ((j.toNat : ℕ) : ℕ∞)`, from `proof` of a statement that counts it as
/// some natural number, `∃ m : ℕ, S.encard = m ∧ (m : ℤ) = j`: the count is
/// that number, which is j, whose `toNat` is the number again
/// (`Int.toNat_natCast`). Of any set. None for any other two statements.
pub(super) fn witness_to_value(
    proof: &Printed,
    says: &Printed,
    wanted: &Printed,
) -> Option<super::super::doc::Proof> {
    use super::super::doc::{CountForm, TermKind};
    use super::super::tactics as t;
    let TermKind::Quantified {
        quant: super::super::doc::Quant::Exists,
        letter,
        guard: Some(guard),
        body,
        ..
    } = &says.kind
    else {
        return None;
    };
    let (g_left, _) = equation_sides(guard)?;
    let (b_left, number) = equation_sides(body)?;
    let (w_left, w_right) = equation_sides(wanted)?;
    let counted = |p: &Printed| match &uncast(p).kind {
        TermKind::Count {
            set,
            form: CountForm::Extended,
        } => Some((**set).clone()),
        _ => None,
    };
    let TermKind::ToNat(j) = &uncast(w_right).kind else {
        return None;
    };
    let named = matches!(&uncast(b_left).kind, TermKind::Letter(l) if l == letter);
    if !named
        || counted(g_left)?.untyped() != counted(w_left)?.untyped()
        || uncast(number).untyped() != uncast(j).untyped()
    {
        return None;
    }
    let (hm, he) = ("hm", "he");
    Some(super::super::doc::Proof::By(Tactic::Seq(vec![
        Tactic::Obtain {
            names: vec![letter.clone(), hm.to_string(), he.to_string()],
            says: None,
            from: proof.clone(),
        },
        t::call(
            "rw",
            vec![TacticArg::Rules(vec![
                t::forwards(t::hyp(hm)),
                t::backwards(t::hyp(he)),
                t::forwards(t::lemma("Int.toNat_natCast")),
            ])],
        ),
    ])))
}

/// The term with each `toNat` of a term with no letter, a numeral's, taken
/// off: what `Int.reduceToNat` works out, `(0 : ℤ).toNat` as 0.
fn numerals_worked(p: &Printed) -> Printed {
    use super::super::doc::TermKind;
    if let TermKind::ToNat(inner) = &p.kind {
        if !inner.lettered() {
            return numerals_worked(inner);
        }
    }
    let mut out = p.clone();
    for child in out.children_mut() {
        *child = numerals_worked(child);
    }
    out
}

/// A sum of a function the header lets, `hyp` its equation, said term by
/// term by that equation at the sum's index `index`: `Finset.sum_congr rfl
/// (by intro k h; exact hD1 k (by simp only [Finset.mem_Icc] at h ⊢;
/// omega))`, the index's fact read off its place in the range.
fn sum_term_by_term(hyp: &str, index: &str) -> Printed {
    use super::super::doc::Proof;
    use super::super::tactics as t;
    let k = super::super::names::letter(index);
    let in_domain = t::by_term(Proof::By(Tactic::Seq(vec![
        t::simp_only(
            false,
            None,
            vec![t::forwards(t::lemma("Finset.mem_Icc"))],
            Some(t::at_h(true)),
        ),
        t::call("omega", vec![]),
    ])));
    let term = t::by_term(Proof::By(Tactic::Seq(vec![
        Tactic::Intro(vec![k.clone(), "h".to_string()]),
        Tactic::Exact(super::terms::hyp_applied(hyp, vec![t::hyp(&k), in_domain])),
    ])));
    Printed::applied(
        "Finset.sum_congr",
        super::super::doc::Source::Mathlib,
        vec![
            Printed::constant(
                "rfl",
                super::super::doc::Source::Core,
                super::super::doc::LeanType::Prop,
            ),
            term,
        ],
        super::super::doc::LeanType::Prop,
    )
}

/// The two sides of an equation as Lean writes it; None for any other
/// statement.
pub(super) fn equation_sides(p: &Printed) -> Option<(&Printed, &Printed)> {
    use super::super::doc::TermKind;
    match &p.kind {
        TermKind::Infix { op, lhs, rhs } if op.symbol == "=" => Some((lhs, rhs)),
        TermKind::Paren(inner) => equation_sides(inner),
        _ => None,
    }
}
