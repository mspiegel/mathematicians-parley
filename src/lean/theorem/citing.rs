//! Proof methods: calculations and cited items.

use super::*;

impl<'a> Proof<'a> {
    /// `calculation`: the chain as Lean's `calc`, every term in one type,
    /// each link proved by its reason.
    pub(super) fn calculation(
        &self,
        just: &Justification,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let Some(Ok(chain)) = crate::corpus::proof::chain(just, &self.thm.path) else {
            return Route::no("a calculation whose lines do not cut");
        };
        let mut terms = vec![match self.tree(&chain.start) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        }];
        for line in &chain.lines {
            match self.tree(&line.term) {
                Route::Built(n) => terms.push(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A chain that counts ∅ beside a set, |S| = |∅|: ∅ is a set of what
        // S holds (`expr::counted_beside_empty`).
        let hinted;
        let writer = match terms
            .iter()
            .find_map(|a| terms.iter().find_map(|b| writer.counted_beside_empty(a, b)))
        {
            Some(m) if writer.empty_of.is_none() => {
                let mut w = writer.with_letters(writer.letters.clone());
                w.empty_of = Some(m);
                hinted = w;
                &hinted
            }
            _ => writer,
        };
        let ChainPrinted {
            printed,
            at,
            of_sets,
            of_counts,
        } = match chain_printed(writer, &terms) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The claim, the first term and the last, is stated in its own
        // least type; a chain worked out in a wider one moves the goal there
        // first, as `qify` or `rify` does.
        let of_numbers = !of_sets && !of_counts;
        let mut own = super::super::templates::Num::Int;
        for t in [terms.first(), terms.last()].into_iter().flatten() {
            if !of_numbers {
                break;
            }
            if let Route::Built(n) = writer.carrier(t) {
                own = own.max(n);
            }
        }
        // The chain is worked in `at`, its first term told the type where
        // nothing in it fixes one; a claim in a narrower type, 3^q = 2^p in
        // ℤ beside ln and exp in ℝ, is moved up to it first.
        // A claim of numerals alone stated in the chain's type already, from
        // the line it is reached from, has nowhere to move.
        let claim_now = self.claim_now.borrow().clone();
        let stated_at = claim_now
            .and_then(|c| self.claim_as_stated(just.line, &c))
            .as_ref()
            .and_then(super::super::doc::forms::relation_type);
        let moved = of_numbers
            && own < at
            && stated_at != Some(super::super::doc::LeanType::Num(at));
        // `qify` and `rify` move the casts of the whole goal, a set's
        // condition under its binder too, `(d.ncard : ℤ) = m` of a set the
        // claim counts, which the chain's terms write in ℤ: such a chain is
        // built as it is written and met with the claim by moving the casts
        // of both alike (`exact_mod_cast`).
        let builds_sets = printed.iter().any(|p| {
            p.walk().iter().any(|n| {
                matches!(
                    &n.kind,
                    super::super::doc::TermKind::Bound {
                        form: super::super::doc::BoundForm::SetOf
                            | super::super::doc::BoundForm::SetOfMember { .. },
                        ..
                    }
                )
            })
        });
        let met_after = moved && builds_sets;
        let mut block: Vec<Tactic> = match (moved && !met_after, at) {
            (true, super::super::templates::Num::Rat) => {
                vec![super::super::tactics::call("qify", vec![])]
            }
            (true, super::super::templates::Num::Real) => {
                vec![super::super::tactics::call("rify", vec![])]
            }
            _ => Vec::new(),
        };
        let mut links: Vec<super::super::doc::tactic::CalcLink> = Vec::new();
        let single = chain.lines.len() == 1;
        for (k, line) in chain.lines.iter().enumerate() {
            let (relation, modulus) = match self.link_relation(line, writer) {
                Route::Built(joined) => joined,
                Route::Declined(d) => return Route::Declined(d),
            };
            let row = CalcRow {
                index: k,
                line,
                relation: &relation,
                modulus: &modulus,
                terms: &terms,
                printed: &printed,
            };
            let proof = match self.row_proof(row, at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            // A chain of one link is that link, and its proof the step's:
            // Lean's calc would read the line after a lone link as another.
            if single {
                return Route::Built(proof);
            }
            links.push(super::super::doc::tactic::CalcLink {
                relation,
                term: printed[k + 1].clone(),
                modulus,
                proof,
            });
        }
        block.push(Tactic::Calc {
            first: printed[0].clone(),
            links,
        });
        if met_after {
            use super::super::tactics as t;
            return Route::Built(super::super::doc::Proof::Block(vec![
                t::name_h(&t::by_term(super::super::doc::Proof::Block(block))),
                t::exact_mod_cast(t::hyp("h")),
            ]));
        }
        Route::Built(super::super::doc::Proof::Block(block))
    }

    /// A calculation's row that is what the cited line says where the
    /// checker found it (`link_places`), that sentence or part as the line
    /// states it, met with the row as Lean writes it as a cited item's
    /// hypothesis is met with its line (`said_proof`): as it stands, turned
    /// round, or across casts, a line in ℤ read in the chain's ℚ, one in ℚ in
    /// the chain's ℝ. A count Lean may hold in ℕ∞ where the chain takes it in
    /// ℤ, `V.encard = 2` of an assumption, is met only from a line whose
    /// statement the writer wrote (`store`).
    fn row_placed(&self, row: CalcRow<'_>) -> Option<Printed> {
        let CalcRow {
            index: k,
            line,
            relation,
            modulus,
            terms,
            printed,
        } = row;
        let at = self.rec.link_places.get(&line.line)?;
        let stated = self.line_part(at).built()?.says.is_some();
        let (proof, says) = self.line_says(at).built()?;
        let row = calc_row(relation, modulus.as_ref(), &printed[k], &printed[k + 1])?;
        if !stated && (item_counts(&says) || item_counts(&row)) {
            return None;
        }
        // A count in ℕ∞ on one side, in ℤ on the other.
        if let Some(p) =
            self.counted_between(&proof, &says, &row, &[&terms[k], &terms[k + 1]])
        {
            return Some(p);
        }
        let meeting = self.rec.link_meetings.get(&line.line);
        self.said_proof(proof, says, &row, meeting).built()
    }

    /// A calculation's row that writes a power as the integer power where the
    /// line has it to its exponent's `toNat`, or the other way: converted as
    /// a citation's is, from the sentence the checker found the row in
    /// (`link_places`).
    fn row_converted(&self, row: CalcRow<'_>) -> Option<super::super::doc::Proof> {
        let CalcRow {
            index: k,
            line,
            relation,
            terms,
            printed,
            ..
        } = row;
        let at = self.rec.link_places.get(&line.line)?;
        let found = self.line_part(at).built()?;
        let (proof, says) = self.line_says(at).built()?;
        let op = super::super::doc::Op::of(relation)?;
        let row = Printed::infix(
            op,
            printed[k].clone(),
            printed[k + 1].clone(),
            super::super::doc::LeanType::Prop,
        );
        self.powers_converted_at(
            &[&terms[k], &terms[k + 1], &found.node],
            &says,
            &row,
            &proof,
            false,
        )
    }

    /// A calculation's row that cites a define `define` names, proved by
    /// unfolding it alone, or with the casts that leaves pushed; None where
    /// the define is not the whole of the row's proof.
    fn row_by_define(
        &self,
        row: CalcRow<'_>,
        cite: &str,
        define: Option<&String>,
    ) -> Option<super::super::doc::Proof> {
        let CalcRow {
            index: k,
            line,
            printed,
            ..
        } = row;
        // Whether the row, or the line it cites, takes an integer
        // to ℕ, an item's 2^(d·e).toNat: a define is then not put
        // in alone.
        let line_to_nat = self
            .trees
            .get(cite)
            .and_then(|t| t.first())
            .and_then(|s| self.line_statement(&s.cited()).built())
            .is_some_and(|p| p.has_to_nat());
        let to_nat = [&printed[k], &printed[k + 1]]
            .iter()
            .any(|p| p.has_to_nat())
            || line_to_nat;
        // A row the define makes true, as the checker met its two
        // sides with the define written out (`define_links`): the
        // define's equation, and then the work its meeting leaves,
        // or the casts Lean writes on the row.
        let met = self.rec.define_links.get(&line.line);
        // Two sides Lean writes alike once each `set` letter is
        // read as its value: `simp only [hD]` puts the values in
        // and closes the `x = x` left, whatever `toNat` or names
        // the row writes.
        let values = self.set_values();
        let alike_set = super::super::doc::forms::alike_once_set(
            &printed[k],
            &printed[k + 1],
            &values,
        );
        match (define, met, self.named_specs.is_empty(), to_nat) {
            (Some(h), _, _, _) if alike_set => Some(super::super::doc::Proof::By(
                unfolded_by(std::slice::from_ref(h), true, false),
            )),
            // A row writing `toNat`, or citing a line that
            // does, whose sides differ only in casts once the
            // `set` letters are read as their values: Lean's
            // casts, which `push_cast` moves once the
            // define is put in.
            (Some(h), Some(met), true, to_nat)
                if !to_nat
                    || super::super::doc::forms::casts_differ(
                        &printed[k],
                        &printed[k + 1],
                        &values,
                    )
                    .is_some() =>
            {
                let cast = self.unfolds_to_casts(&printed[k], &printed[k + 1]);
                Some(super::super::doc::Proof::By(unfolded_by(
                    std::slice::from_ref(h),
                    met.as_ref().is_some_and(unfolds_alone) && !cast,
                    false,
                )))
            }
            _ => None,
        }
    }

    /// What a chain line joins its term to the one before by: the relation,
    /// and for a congruence the modulus as Lean writes it.
    fn link_relation(
        &self,
        line: &crate::corpus::proof::ChainLine,
        writer: &Writer,
    ) -> Route<(String, Option<Printed>)> {
        Route::Built(match line.relation.as_str() {
            r @ ("=" | "<" | ">" | "≤" | "≥") => (r.to_string(), None),
            "≡" => {
                let Some(modulus) = &line.modulus else {
                    return Route::no("a congruence with no modulus");
                };
                let modulus = match self.tree(modulus) {
                    Route::Built(m) => m,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match writer.number_fixed(&modulus, super::super::templates::Num::Int) {
                    Route::Built(m) => ("≡".to_string(), Some(m)),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            other => return Route::no(format!("a calculation joined by {other}")),
        })
    }

    /// The proof of one row of a calculation, worked in the type `at`: by
    /// the reason the row gives, by the line or define it cites, by real
    /// arithmetic, or by arithmetic.
    fn row_proof(
        &self,
        row: CalcRow<'_>,
        at: super::super::templates::Num,
    ) -> Route<super::super::doc::Proof> {
        let CalcRow {
            index: k,
            line,
            relation,
            terms,
            printed,
            ..
        } = row;
        Route::Built(match &line.reason {
            Some(r) => {
                let Ok(by) = &r.by else {
                    return Route::no("a calculation line whose reason does not read");
                };
                let fact = match self.tree(&r.fact) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let reason = Reason {
                    just: by,
                    cited: self.rec.cited_requires.get(&r.line),
                };
                self.worked_in.set(Some(at));
                *self.row_stated.borrow_mut() = super::super::doc::Op::of(relation)
                    .map(|op| {
                        Printed::infix(
                            op,
                            printed[k].clone(),
                            printed[k + 1].clone(),
                            super::super::doc::LeanType::Prop,
                        )
                    });
                let proof = self.proof_of(reason, 0, &fact);
                self.worked_in.set(None);
                *self.row_stated.borrow_mut() = None;
                match proof {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            // A row citing a define, S(1) = Σ(j = 1 to 1) j(j + 1) by
            // D1, unfolds it and pushes in the casts that leaves; a
            // header's function, its equation guarded by its domain, at
            // an argument linear arithmetic shows is in it.
            None if let Some(cite) = line.cited() => match self.row_citing(row, cite) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            },
            // A row the page works out by real arithmetic, = 3·ln(2).
            None if line.cite == crate::corpus::Method::RealArithmetic.as_str() => {
                match super::super::reals::real_link(
                    &self.writer,
                    self.sources.targets,
                    &terms[k],
                    &terms[k + 1],
                    at,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            None => super::super::doc::Proof::By(super::super::tactics::call(
                "norm_num",
                vec![],
            )),
        })
    }

    /// The proof of a calculation's row that cites a line or a label: the
    /// define it unfolds, the line it is read from, or the cited line used
    /// across the casts the chain's type puts on it.
    pub(super) fn row_citing(
        &self,
        row: CalcRow<'_>,
        cite: &str,
    ) -> Route<super::super::doc::Proof> {
        let CalcRow {
            index: k,
            line,
            relation,
            terms,
            printed,
            ..
        } = row;
        Route::Built({
            let define = self
                .thm
                .defines
                .iter()
                .any(|d| d.label == cite)
                .then(|| self.named.get(cite).and_then(|n| n.first()))
                .flatten();
            // A row of a step that names whole numbers, citing a line
            // in the page's forms: both taken to ℚ, each named number
            // put as its term, and the line used.
            let named = self.named.get(cite).and_then(|n| n.first());
            let in_named = match (named, self.named_specs.is_empty()) {
                (Some(name), false) => match in_named_forms(
                    &self.named_specs,
                    name,
                    self.rec.link_facings.get(&line.line).copied(),
                    relation == "≡",
                ) {
                    Route::Built(t) => Some(t),
                    Route::Declined(d) => return Route::Declined(d),
                },
                _ => None,
            };
            let by_define = self.row_by_define(row, cite, define);
            let mut ways: Vec<Tactic> = match define {
                Some(h) => unfolded(std::slice::from_ref(h)),
                None => Vec::new(),
            };
            // A "for all" line read at the row's letter, as a line
            // cited inside a block is: 5.7's a·f(a) ≡ 1 at the
            // block's a, as it stands or turned round.
            let names: std::collections::BTreeSet<String> = terms[k]
                .names()
                .into_iter()
                .chain(terms[k + 1].names())
                .collect();
            let read: Vec<super::super::algebra::Cited> = self
                .trees
                .get(cite)
                .into_iter()
                .flatten()
                .filter(|s| s.node.notation() == crate::notations::FOR_ALL)
                .filter_map(|s| self.at_recorded_letter(&s.cited(), &names))
                .collect();
            // The one such line, the way the checker found the row
            // faces it (`link_facings`).
            let at_letter =
                match (read.as_slice(), self.rec.link_facings.get(&line.line)) {
                    ([at], Some(facing)) => Some(super::super::doc::Proof::By(
                        Tactic::Exact(faced(at.proof.clone(), *facing)),
                    )),
                    _ => None,
                };
            for at in read {
                for facing in [Facing::Straight, Facing::Turned] {
                    ways.push(Tactic::Exact(faced(at.proof.clone(), facing)));
                }
            }
            // In the named numbers' forms, the line used the way the
            // record says the row faces it: the row's proof.
            let named_decided = in_named
                .clone()
                .filter(|_| self.rec.link_facings.contains_key(&line.line))
                .map(super::super::doc::Proof::By);
            ways.extend(in_named);
            // The row is what the cited line says where the checker
            // found it (`link_places`), that sentence or part as the
            // line states it, met with the row as Lean writes it as
            // a cited item's hypothesis is met with its line
            // (`said_proof`): as it stands, turned round, or across
            // casts, a line in ℤ read in the chain's ℚ, one in ℚ in
            // the chain's ℝ.
            // A count Lean may hold in ℕ∞ where the chain takes it
            // in ℤ, `V.encard = 2` of an assumption: met only from a
            // line whose statement the writer wrote (`store`).
            let placed = self.row_placed(row);
            // An equation whose two sides Lean writes alike once a
            // define is written out in both, `T(1) = 1(1 + 1)/2`:
            // `rfl`. Not a row of numerals worked out, which in a
            // contradiction may be false.
            let as_it_stands = (relation == "="
                && bare_term(&printed[k]).untyped()
                    == bare_term(&printed[k + 1]).untyped())
            .then(|| {
                Printed::constant(
                    "rfl",
                    super::super::doc::Source::Core,
                    super::super::doc::LeanType::Prop,
                )
            });
            match (as_it_stands, by_define, placed) {
                (Some(truth), _, _) => super::super::doc::Proof::Term(truth),
                (None, Some(proof), _) => proof,
                (None, None, Some(proved)) => super::super::doc::Proof::Term(proved),
                (None, None, None) => {
                    match (self.row_converted(row), at_letter, named_decided) {
                        (Some(proof), _, _)
                        | (None, Some(proof), _)
                        | (None, None, Some(proof)) => proof,
                        (None, None, None) => {
                            match ways_proof(ListReason::RowRead, ways) {
                                Route::Built(p) => p,
                                Route::Declined(d) => return Route::Declined(d),
                            }
                        }
                    }
                }
            }
        })
    }

    /// Each sentence of the lines `refs` names, each conjunction taken apart
    /// into its parts, with the Lean term that proves each part.
    pub(super) fn cited_parts(
        &self,
        refs: &[String],
    ) -> Vec<super::super::algebra::Cited> {
        let mut out = Vec::new();
        for r in refs {
            for s in self.trees.get(r).into_iter().flatten() {
                conjuncts(
                    &s.node,
                    s.proof.clone(),
                    s.says.clone(),
                    &mut out,
                    &self.writer,
                );
            }
        }
        out
    }

    /// Where the item's set letter `name` is the domain of one of its maps,
    /// the domain of the map the citation gives for it, as Lean writes it;
    /// None where the letter is no map's domain.
    pub(super) fn given_domain(
        &self,
        sentence: &Sentence,
        name: &str,
        binding: &crate::matching::Binding,
    ) -> Option<Route<super::super::expr::Printed>> {
        let (map, _) = sentence.domains.iter().find(|(_, d)| {
            matches!(&d.kind, super::super::doc::TermKind::Letter(l) if *l == super::super::names::letter(name))
        })?;
        let given = binding.get(&crate::formula::symbol::Symbol::of(map));
        Some(match given {
            // The domain stands bracketed as an argument does.
            Some(g) if g.is_name() => match self.writer.domain_of(&g.text) {
                Some(d) if d.prec() < super::super::expr::MAX => {
                    let ty = d.ty.clone();
                    Route::Built(super::super::expr::Printed {
                        kind: super::super::doc::TermKind::Paren(Box::new(d)),
                        ty,
                    })
                }
                Some(d) => Route::Built(d),
                None => Route::no(format!("{}, whose domain no line gives", g.text)),
            },
            // A map given by its values, x ↦ c, is given on all its type.
            Some(g) if &*g.notation_name() == "property-of" => {
                Route::Built(super::super::expr::Printed::head(
                    "Set.univ",
                    super::super::doc::Source::Mathlib,
                ))
            }
            _ => Route::left_out(format!(
                "a map's domain where its map {map} is given no letter"
            )),
        })
    }

    /// The type each of an item's type variables is taken at where a
    /// citation gives its things numbers, x ∈ {u, w} cited of 1 and 2: the
    /// least that holds every number given them. From ℕ: a set of naturals
    /// given for a set of things, S ⊆ ℕ, is of naturals, and a number given
    /// raises it to ℤ at least.
    pub(super) fn things_given(
        &self,
        binders: &[Binder],
        binding: &crate::matching::Binding,
    ) -> ThingsGiven {
        use super::super::expr::Members;
        let mut given = ThingsGiven::default();
        for b in binders {
            let Binder::Letter { page, ty, .. } = b else {
                continue;
            };
            let Some(value) = binding.get(&crate::formula::symbol::Symbol::of(page))
            else {
                continue;
            };
            match ty {
                // A term of natural letters, b·d, is a natural; any other
                // number is an integer at least.
                LetterType::Member(Members::Things(var))
                    if self.writer.is_number(value) =>
                {
                    let of_letters = value.walk().iter().any(|m| m.is_name());
                    if of_letters && self.writer.natural(value) {
                        continue;
                    }
                    if let Route::Built(c) = self.writer.carrier(value) {
                        given.raise(*var, c);
                    }
                }
                // A set of things given a set of numbers, X := ℝ, sets the
                // things' type at least to that set's.
                LetterType::Set(Members::Things(var)) => {
                    match self.writer.set_members(value) {
                        Some(Members::Numbers(n)) => {
                            given.raise(*var, n);
                            given.numbers.insert(*var);
                        }
                        Some(m @ Members::Sets(_)) => {
                            given.others.insert(*var, m);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }
        // A map given by its values, n ↦ 9ⁿ, gives what its body is with
        // n of the type its domain's things are taken at, ℚ of n in ℤ.
        for b in binders {
            let Binder::Letter {
                page,
                ty:
                    LetterType::Map {
                        from: Members::Things(from),
                        to: Members::Things(to),
                    },
                ..
            } = b
            else {
                continue;
            };
            let value = binding.get(&crate::formula::symbol::Symbol::of(page));
            let Some(value) = value.filter(|v| &*v.notation_name() == "property-of")
            else {
                continue;
            };
            let [body] = value.children.as_slice() else {
                continue;
            };
            let takes = given
                .at
                .get(from)
                .copied()
                .unwrap_or(super::super::templates::Num::Nat);
            let mut letters = self.writer.letters.clone();
            letters.insert(value.text.to_string(), LetterType::Number(takes));
            if let Route::Built(c) = self.writer.with_letters(letters).carrier(body) {
                given.raise(*to, c);
            }
        }
        // Things the citation gives nothing are what ∅ holds where the
        // lines say: the integers of ∏(x ∈ ∅) x in the base of an induction
        // on the parts of a set of integers.
        if let Some(held) = &self.writer.empty_of {
            let vars: std::collections::BTreeSet<usize> = binders
                .iter()
                .filter_map(|b| match b {
                    Binder::Letter { ty, .. } => Some(ty.lean_type()),
                    _ => None,
                })
                .flat_map(|ty| things_of_type(&ty))
                .collect();
            for var in vars {
                let told = given.numbers.contains(&var)
                    || given.others.contains_key(&var)
                    || given.at.contains_key(&var);
                match held {
                    _ if told => {}
                    Members::Numbers(n) => {
                        given.numbers.insert(var);
                        given.raise(var, *n);
                    }
                    other => {
                        given.others.insert(var, other.clone());
                    }
                }
            }
        }
        given
    }

    /// The item applied to what the citation gives it, and what it then
    /// says: the theorem with each letter given its value, and each
    /// hypothesis given by the line cited that says it as Lean writes both;
    /// declined where no line does.
    pub(super) fn instance_of(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
        claim: Option<&Node>,
        cited: &crate::checker::record::Cited,
    ) -> Route<Instance> {
        let mut given: std::collections::BTreeMap<String, super::super::expr::Printed> =
            std::collections::BTreeMap::new();
        let things = self.things_given(&sentence.binders, binding);
        // The type an item's general letters take: the least that holds the
        // claim and every value given them, a field's at least where the
        // item divides.
        let general = match sentence.general {
            Some(g) => {
                let least = if g.field {
                    super::super::templates::Num::Rat
                } else {
                    super::super::templates::Num::Int
                };
                let mut at = self.worked_in.get().map_or(least, |w| w.max(least));
                let numbers: Vec<&Node> = claim
                    .into_iter()
                    .flat_map(|c| c.children.iter())
                    .filter(|c| self.writer.is_number(c))
                    .collect();
                for n in numbers {
                    match self.writer.carrier(n) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                // A term the claim puts in a hole of a fixed type, ⌊A/B⌋ in
                // ℝ's, is of that type.
                if let Some(c) = claim {
                    at = at.max(self.held_in(c));
                }
                for b in &sentence.binders {
                    let Binder::Letter {
                        page,
                        ty,
                        general: true,
                        ..
                    } = b
                    else {
                        continue;
                    };
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        continue;
                    };
                    match self.given_type(value, ty, &things) {
                        Route::Built(c) => at = at.max(c),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Some(at)
            }
            None => None,
        };
        let asked = InstanceAsked {
            sentence,
            binding,
            claim,
            things: &things,
            general,
        };
        let mut args = Vec::new();
        for b in &sentence.binders {
            match b {
                Binder::Letter {
                    name,
                    page,
                    ty,
                    general: in_general,
                } => {
                    let p = match self.letter_given(&asked, name, page, ty, *in_general)
                    {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    given.insert(name.clone(), p.clone());
                    args.push(super::super::doc::Arg::Named {
                        name: name.clone(),
                        value: p,
                    });
                }
                // A hypothesis the checker found a line or a requires line
                // supplies (`Cited::supplied`), found by where the item
                // writes it (`Supplied::at`), a letter's number system
                // among them: that line by its name, met with the
                // hypothesis as Lean asks it at the values given, as it
                // stands or by its casts (`supplied_proof`).
                Binder::Fact { at, says, .. } => {
                    // As the statement is, in the type the citation gives
                    // the item's general letters.
                    let wanted =
                        super::super::doc::forms::substituted_all(says, &given);
                    let wanted = match general {
                        Some(at) => {
                            wanted.with_general(super::super::doc::LeanType::Num(at))
                        }
                        None => wanted,
                    };
                    let proof = lean_truth(&wanted).or_else(|| match at {
                        Some(StatedAt::Hypothesis(at)) => cited
                            .supplied
                            .iter()
                            .find(|s| s.at.as_ref() == Some(at))
                            .and_then(|s| {
                                self.supplied_hypothesis(s, &wanted, binding).built()
                            }),
                        // The citing proof's define of the same recursion,
                        // whose hypothesis states the rules alike.
                        Some(StatedAt::Recursion(theirs)) => cited
                            .recursions
                            .get(theirs)
                            .map(|ours| super::super::tactics::hyp(&line_name(ours))),
                        None => None,
                    });
                    match proof {
                        Some(p) => args.push(proof_arg(p)),
                        None => {
                            return Route::no(
                                "a cited item's hypothesis no line the checker found supplies",
                            )
                        }
                    }
                }
            }
        }
        // A type variable the item's sentence holds and none of its letters
        // does, the α of |(∅ : Set α)| = 0, is given by name: no argument
        // tells Lean what it is. It is what ∅ holds where the lines say.
        let lettered: std::collections::BTreeSet<usize> = sentence
            .binders
            .iter()
            .filter_map(|b| match b {
                Binder::Letter { ty, .. } => Some(ty.lean_type()),
                _ => None,
            })
            .flat_map(|ty| things_of_type(&ty))
            .collect();
        if let Some(held) = &self.writer.empty_of {
            for var in things_in(&sentence.prop) {
                if !lettered.contains(&var) {
                    args.insert(
                        0,
                        super::super::doc::Arg::Named {
                            name: super::super::expr::things_name(var),
                            value: super::super::expr::Printed::of(
                                super::super::doc::TermKind::Letter(
                                    held.letter().lean_type().text(),
                                ),
                                super::super::doc::LeanType::Universe,
                            ),
                        },
                    );
                }
            }
        }
        let decl = super::super::expr::Printed::head(
            &sentence.decl,
            super::super::doc::Source::Item(module_of_decl(&sentence.decl)),
        );
        let head = if args.is_empty() {
            decl
        } else {
            super::super::expr::Printed {
                kind: super::super::doc::TermKind::Paren(Box::new(
                    super::super::expr::Printed {
                        kind: super::super::doc::TermKind::App {
                            head: Box::new(decl),
                            args,
                            explicit: false,
                        },
                        ty: Some(super::super::doc::LeanType::Prop),
                    },
                )),
                ty: Some(super::super::doc::LeanType::Prop),
            }
        };
        let term = fields(head, &sentence.part);
        let statement = sentence.prop.substituted(&given);
        let statement = match general {
            Some(at) => statement.with_general(super::super::doc::LeanType::Num(at)),
            None => statement,
        };
        Route::Built(Instance { term, statement })
    }

    /// What a cited item's letter `name` is given: the value the citation
    /// gives it, written as Lean writes a letter of its kind, or, where the
    /// citation gives it none, what Lean is left to fill.
    pub(super) fn letter_given(
        &self,
        asked: &InstanceAsked<'_>,
        name: &str,
        page: &str,
        ty: &LetterType,
        in_general: bool,
    ) -> Route<Printed> {
        let InstanceAsked {
            binding,
            claim,
            things,
            general,
            ..
        } = *asked;
        let things_at = |var: &usize| {
            let least = self
                .worked_in
                .get()
                .unwrap_or(super::super::templates::Num::Nat);
            things.at.get(var).map_or(least, |n| least.max(*n))
        };
        let Some(value) = binding.get(&crate::formula::symbol::Symbol::of(page)) else {
            return self.letter_unvalued(asked, name, page, ty);
        };
        // The value of a define that names its number, m/p of
        // `let r = m/p, a positive integer`, is that number, r.
        let value = self
            .witness_letters
            .iter()
            .find(|w| crate::matching::alike_top(&w.value, value, self.sources.ctx))
            .map_or(value, |w| &w.letter);
        match (ty, general.filter(|_| in_general)) {
            (LetterType::Number(_), Some(at)) => self.writer.number_fixed(value, at),
            // A value of a wider type that a line says is in the
            // letter's, A + B ∈ ℚ of reals: the number that line
            // gives.
            (LetterType::Number(n), None) => {
                match self.writer.number_fixed(value, *n) {
                    Route::Declined(d) => match self.integer_line(value, *n) {
                        Some(line) => {
                            let printed =
                                super::super::tactics::bracket(line.chosen(*n));
                            self.said_used.borrow_mut().push(SaidUsed {
                                line,
                                term: self.writer.grammar.print(value),
                            });
                            Route::Built(printed)
                        }
                        None => Route::Declined(d),
                    },
                    built => built,
                }
            }
            // A property given by what it says of t, `fun t : α
            // => …`, t a member of what the property is of.
            (LetterType::Property(members), _) => {
                // Of things the citation gives numbers, the
                // numbers at the type the things are taken at.
                // Of things given sets, a set of them; of sets of
                // things, sets of what is given for those.
                let put = things.put(members, &things_at);
                let (of, of_type) = (put.letter(), put.member_type());
                match (&*value.notation_name(), value.children.as_slice()) {
                    ("property-of", [body]) => {
                        let mut letters = self.writer.letters.clone();
                        letters.insert(value.text.to_string(), of);
                        let inner = self.writer.with_letters(letters);
                        inner.formula(body).map(|b| {
                            lambda(
                                &super::super::names::letter(&value.text),
                                of_type,
                                b,
                            )
                        })
                    }
                    _ if value.is_name() => Route::Built(super::super::tactics::hyp(
                        &super::super::names::letter(&value.text),
                    )),
                    _ => Route::no("a property given by other than what it says"),
                }
            }
            // A function given for a function letter, of the
            // same types.
            // A function given by its values, k ↦ t, a sum's
            // term: `fun k : ℤ => t`, t in what it gives.
            (LetterType::Function { from, to }, given)
                if &*value.notation_name() == "property-of" =>
            {
                // A function into the general type gives the
                // type chosen for it.
                let gives = given.unwrap_or(*to);
                match value.children.as_slice() {
                    [body] => {
                        let mut letters = self.writer.letters.clone();
                        letters
                            .insert(value.text.to_string(), LetterType::Number(*from));
                        let mut inner = self.writer.with_letters(letters);
                        inner.wholes.shift_remove(&*value.text);
                        // k ↦ 2^k given for a sum's term stands for
                        // the sum's index the claim runs it over,
                        // in ℕ₀ from 0, so 2^k is written as the
                        // claim's sum writes it.
                        let index = claim.and_then(|c| {
                            super::super::expr::index_letter_system(c, &value.text)
                        });
                        if let (super::super::templates::Num::Int, Some(system)) =
                            (*from, index)
                        {
                            inner.introduce(&value.text, system);
                        }
                        inner.number_fixed(body, gives).map(|b| {
                            lambda(
                                &super::super::names::letter(&value.text),
                                super::super::doc::LeanType::Num(*from),
                                b,
                            )
                        })
                    }
                    _ => Route::no("a function by its values of other than one body"),
                }
            }
            (LetterType::Function { from, to }, given) => {
                match self.writer.function_type(value) {
                    Route::Built(t) if t == (*from, given.unwrap_or(*to)) => {
                        Route::Built(self.writer.function_printed(value))
                    }
                    // A function that takes the letter's numbers
                    // and gives numbers within its type, t of ℤ
                    // into ℤ for f of ℕ into ℝ: t between casts.
                    Route::Built((takes, gives))
                        if *from <= takes && gives <= given.unwrap_or(*to) =>
                    {
                        let wanted = given.unwrap_or(*to);
                        Route::Built(mapped_through(
                            self.writer.function_printed(value),
                            super::super::doc::LeanType::Num(*from),
                            takes,
                            gives,
                            wanted,
                        ))
                    }
                    Route::Built(_) => {
                        Route::no("a function given for a letter of other types")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            (LetterType::Statement, _) => self.writer.formula(value),
            // A thing given a number: the number, at the type
            // the things are taken at here.
            (LetterType::Member(super::super::expr::Members::Things(var)), _)
                if self.writer.is_number(value) =>
            {
                self.writer.number_fixed(value, things_at(var))
            }
            // A set of things given a set of numbers: the set at
            // the type the things are taken at here.
            (LetterType::Set(super::super::expr::Members::Things(var)), _)
                if matches!(
                    self.writer.set_members(value),
                    Some(super::super::expr::Members::Numbers(_))
                ) =>
            {
                self.writer.numbers_at(value, things_at(var))
            }
            _ => {
                self.given_to_things(ty, general.filter(|_| in_general), value, things)
            }
        }
    }

    /// What a cited item's letter is given where the citation gives it no
    /// value. A set: a map's domain, the X of `f : X → W`, is the domain of
    /// what f is given, within which its images are taken; the Z a map goes
    /// into is all of its type, which every map goes into; anything else is
    /// left to Lean.
    fn letter_unvalued(
        &self,
        asked: &InstanceAsked<'_>,
        name: &str,
        page: &str,
        ty: &LetterType,
    ) -> Route<Printed> {
        Route::Built(
            match (ty, self.given_domain(asked.sentence, name, asked.binding)) {
                (LetterType::Set(_), Some(Route::Built(d))) => d,
                (LetterType::Set(_), Some(Route::Declined(d))) => {
                    return Route::Declined(d)
                }
                (LetterType::Set(_), None) => super::super::expr::Printed::head(
                    "Set.univ",
                    super::super::doc::Source::Mathlib,
                ),
                // A function of a recursion the file lets, F of
                // D1, is the citing theorem's F, which the same
                // define lets.
                (LetterType::Function { .. }, _)
                    if self.writer.letters.get(page) == Some(ty) =>
                {
                    super::super::expr::Printed::letter(
                        super::super::names::letter(page),
                        ty.lean_type(),
                    )
                }
                _ => super::super::expr::Printed::of(
                    super::super::doc::TermKind::Elided,
                    ty.lean_type(),
                ),
            },
        )
    }

    /// What a citation gives a cited item's letter of things, a set of
    /// things or a map of things, the kinds `letter_given` has no rule for:
    /// the value written as Lean writes a letter of that kind, at the types
    /// the things are taken at here.
    fn given_to_things(
        &self,
        ty: &LetterType,
        given: Option<super::super::templates::Num>,
        value: &Node,
        things: &ThingsGiven,
    ) -> Route<Printed> {
        let things_at = |var: &usize| {
            let least = self
                .worked_in
                .get()
                .unwrap_or(super::super::templates::Num::Nat);
            things.at.get(var).map_or(least, |n| least.max(*n))
        };
        let printed = match (ty, given) {
            // `letter_given` has a rule for each of these, whatever the
            // value, before it comes here.
            (
                LetterType::Number(_)
                | LetterType::Property(_)
                | LetterType::Function { .. }
                | LetterType::Statement,
                _,
            ) => unreachable!("a letter `letter_given` has a rule for"),
            // A map of things given by its values on numbers,
            // n ↦ 9ⁿ: `fun n : ℤ => 9 ^ n`, taking and giving
            // numbers at the types its two sides' things are
            // taken at here.
            (
                LetterType::Map {
                    from: super::super::expr::Members::Things(from),
                    to: super::super::expr::Members::Things(to),
                },
                _,
            ) if &*value.notation_name() == "property-of" => {
                match value.children.as_slice() {
                    [body] => {
                        let mut letters = self.writer.letters.clone();
                        letters.insert(
                            value.text.to_string(),
                            LetterType::Number(things_at(from)),
                        );
                        let inner = self.writer.with_letters(letters);
                        inner.number_fixed(body, things_at(to)).map(|b| {
                            lambda(
                                &super::super::names::letter(&value.text),
                                super::super::doc::LeanType::Num(things_at(from)),
                                b,
                            )
                        })
                    }
                    _ => Route::no("a map by its values of other than one body"),
                }
            }
            // A map from things into numbers given by its
            // values, x ↦ x·c for t : X → ℤ: `fun x : ℤ => x *
            // c`, x a member of what the things are taken at
            // here, its value a number of t's type.
            (
                LetterType::Map {
                    from: from @ super::super::expr::Members::Things(_),
                    to: super::super::expr::Members::Numbers(to),
                },
                given,
            ) if &*value.notation_name() == "property-of" => {
                let put = things.put(from, &things_at);
                let gives = given.unwrap_or(*to);
                match value.children.as_slice() {
                    [body] => {
                        let mut letters = self.writer.letters.clone();
                        letters.insert(value.text.to_string(), put.letter());
                        let inner = self.writer.with_letters(letters);
                        inner.number_fixed(body, gives).map(|b| {
                            lambda(
                                &super::super::names::letter(&value.text),
                                put.member_type(),
                                b,
                            )
                        })
                    }
                    _ => Route::no("a map by its values of other than one body"),
                }
            }
            // A function of numbers given for a map of things
            // into numbers, f for u : X → K: f itself where it
            // gives the numbers asked, else f's value cast up.
            (
                LetterType::Map {
                    from: from @ super::super::expr::Members::Things(_),
                    to: super::super::expr::Members::Numbers(to),
                },
                given,
            ) if self.writer.function_type(value).built().is_some() => {
                let wanted = given.unwrap_or(*to);
                let put = things.put(from, &things_at);
                match self.writer.function_type(value) {
                    Route::Built((_, gives)) if gives == wanted => {
                        Route::Built(self.writer.function_printed(value))
                    }
                    Route::Built((takes, gives)) if gives < wanted => {
                        Route::Built(mapped_through(
                            self.writer.function_printed(value),
                            put.member_type(),
                            takes,
                            gives,
                            wanted,
                        ))
                    }
                    Route::Built(_) => {
                        Route::no("a function given for a map into a narrower type")
                    }
                    Route::Declined(d) => Route::Declined(d),
                }
            }
            // A listed set whose members give no type, {∅},
            // given for a set of things that another letter
            // gives sets: a set of those.
            (LetterType::Set(super::super::expr::Members::Things(var)), _)
                if things.others.contains_key(var)
                    && self.writer.members_of(value).is_none() =>
            {
                self.writer.listed_as(value, &things.others[var])
            }
            // ∅ given for a member, the x := ∅ of |{x}| = 1 for
            // |{∅}|: with the type the writer gives ∅ inside
            // {∅} (`Writer::sets_of_nothing`), which ∅ alone
            // does not give Lean.
            (LetterType::Member(super::super::expr::Members::Things(_)), _)
                if &*value.notation_name() == "empty-set" =>
            {
                match self.writer.sets_of_nothing(std::slice::from_ref(value)) {
                    Some(set) => Route::Built(Printed::cast(
                        Printed::constant(
                            "∅",
                            super::super::doc::Source::Core,
                            set.member_type(),
                        ),
                        set.member_type(),
                    )),
                    None => self.writer.set_term(value),
                }
            }
            // A set, a member or a map given for one: the term
            // as the writer writes a set's.
            (
                LetterType::Set(_) | LetterType::Member(_) | LetterType::Map { .. },
                _,
            ) => self.writer.set_term(value),
            // A group given for a group, or a subgroup for a
            // subgroup: its Lean name, the type or the
            // `Subgroup G` itself, not the set it stands for.
            (LetterType::Group | LetterType::Subgroup(_), _) => Route::Built(
                super::super::tactics::hyp(&super::super::names::letter(&value.text)),
            ),
            // The identity is no binder: `1` of the group.
            (LetterType::Identity(_), _) => {
                Route::no("an identity given as a letter of an item")
            }
        };
        printed
    }

    /// The type a value given a general letter is in: a number's own, a
    /// function by its values k ↦ t the type of t with k of the type the
    /// function takes, and a function letter's what it gives.
    pub(super) fn given_type(
        &self,
        value: &Node,
        ty: &LetterType,
        things: &ThingsGiven,
    ) -> Route<super::super::templates::Num> {
        match (ty, value.children.as_slice()) {
            (LetterType::Function { from, .. }, [body])
                if &*value.notation_name() == "property-of" =>
            {
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), LetterType::Number(*from));
                self.writer.with_letters(letters).carrier(body)
            }
            (LetterType::Function { .. }, _) => {
                self.writer.function_type(value).map(|(_, to)| to)
            }
            // A map of things into numbers given by its values, x ↦ x·c: the
            // type of x·c with x a number of the type the things are given;
            // given a function, what the function gives.
            (
                LetterType::Map {
                    from: super::super::expr::Members::Things(var),
                    ..
                },
                [body],
            ) if &*value.notation_name() == "property-of" => {
                // Things given things, x ↦ c of a set of the theorem's
                // things: x one of them.
                let x = match things.at.get(var) {
                    Some(takes) => LetterType::Number(*takes),
                    None => {
                        LetterType::Member(super::super::expr::Members::Things(*var))
                    }
                };
                let mut letters = self.writer.letters.clone();
                letters.insert(value.text.to_string(), x);
                self.writer.with_letters(letters).carrier(body)
            }
            // Given a map letter into numbers, t : X → ℤ, what it gives.
            (LetterType::Map { .. }, _) => {
                match self.writer.letters.get(&*value.text) {
                    Some(LetterType::Map {
                        to: super::super::expr::Members::Numbers(n),
                        ..
                    }) if value.is_name() => Route::Built(*n),
                    _ => self.writer.function_type(value).map(|(_, to)| to),
                }
            }
            // A set given for a `Set K` letter: the type of its numbers.
            (LetterType::Set(_), _) => match self.writer.set_members(value) {
                Some(super::super::expr::Members::Numbers(n)) => Route::Built(n),
                _ => Route::no(format!(
                    "{} is no set of numbers",
                    self.writer.grammar.print(value)
                )),
            },
            _ => self.writer.carrier(value),
        }
    }

    /// The item a reason cites, in Lean.
    pub(super) fn cited_item<'r>(&self, reason: Reason<'r>) -> Route<(&Item, &'r Cited)>
    where
        'a: 'r,
    {
        let Some(cited) = reason.cited else {
            return Route::no("a citation the checker did not read");
        };
        match self.sources.items.get(&cited.item) {
            Some(item) => Route::Built((item, cited)),
            None => Route::no(format!("{} has no Lean form", cited.item)),
        }
    }

    /// Sentence `k` of a claim citing a phrase's define, which Lean writes
    /// out as its meaning in the claim and the lines alike: read backward,
    /// the claim's parts each from where the checker found it
    /// (`Cited::unfolded`, `unfolded_proof`), `⟨s7, s6⟩`; read forward,
    /// the line the reading starts from (`Cited::firsts`), the part of its
    /// "and" that met the claim projected (`Concluded::part`), `s12.1`, and
    /// met with the claim as a hypothesis is with its line (`said_proof`).
    /// None where the record gives neither, or a witness's facts must be put
    /// in scope first.
    pub(super) fn phrase_proof(
        &self,
        cited: &crate::checker::record::Cited,
        refs: &[String],
        k: usize,
        node: &Node,
    ) -> Option<Printed> {
        let wanted = self.writer.formula(node).built()?;
        let concluded = cited.concluded.get(k)?;
        // A witness bound by the line cited: that line says the meaning
        // whole (`witness_bound_by_line`).
        if concluded.way == crate::citing::Way::Backward
            && self.witness_bound_by_line(cited, refs)
        {
            return self.first_proof(cited, &wanted);
        }
        if concluded.way == crate::citing::Way::Backward {
            let parts = cited.unfolded.get(k)?.as_ref()?;
            let mut known = Vec::new();
            return self
                .unfolded_proof(&wanted, parts.iter().collect(), &mut known)
                .filter(|_| known.is_empty());
        }
        cited.firsts.iter().find_map(|by| {
            let (proof, says) = self.line_proof(by).built()?;
            // The part of the definition's right side the claim is
            // (`Concluded::part`), projected from the line as Lean states the
            // meaning, `s12.1`; the whole line where the claim, as Lean
            // states it, has as many parts as the line, the right side's
            // parts Lean leaves out, "where W is a set", left out of both.
            let parts = conjoined_parts(&says);
            let whole = parts.len() == conjoined_parts(&wanted).len();
            let (proof, says) = match concluded.part.filter(|_| !whole) {
                Some(part) => {
                    let at = parts.get(part)?.clone();
                    (fields(proof, &projection_path(part, parts.len())), at)
                }
                None => (proof, says),
            };
            self.said_proof(proof, says, &wanted, None).built()
        })
    }

    /// The term a citation gives, taken to the part of the item's sentence
    /// the claim is, with what it says. A claim that is itself the "and",
    /// read as its parts, is the whole; a sentence of the claim that one part
    /// of the "and" the reading gives met, "for all d …" of "p > 1 and for
    /// all d …", is that part as the checker's matcher met it
    /// (`Concluded::part`), its projection; and a claim that is one part of
    /// what that part gives read at the values, a property applied taken as
    /// its body (`Cited::within`), is the part of the "and" its body is.
    fn projected_reading(
        &self,
        asked: Projection<'_>,
        term: Printed,
        says: Option<Printed>,
    ) -> Route<ProjectedReading> {
        let Projection {
            node,
            iff,
            sentence,
            part,
            cited,
            k,
        } = asked;
        let whole = self.writer.is_and(node);
        // What the reading gives: a definition's right side, a theorem's
        // sentence; its "and" is taken apart as its tree nests it.
        let read = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right,
            _ => &sentence.says,
        };
        let mut says = says;
        let path = match (whole, part) {
            (false, Some(at)) => match leaf_path(read, at, &self.writer) {
                Some(path) => Some(path),
                None => {
                    return Route::no(
                        "a reading whose \"and\" has fewer parts than the part the claim met",
                    )
                }
            },
            _ => None,
        };
        let term = match &path {
            Some(path) => {
                says = says.and_then(|s| along(&s, path));
                projected(term, path)
            }
            None => term,
        };
        let term = match (cited.within.get(k).copied().flatten(), &says) {
            (Some(j), Some(s)) => {
                // The part read at the values, its property applied as its
                // body (`at_values`), and the path to its part j there.
                let part = match &path {
                    Some(path) => node_along(read, path, &self.writer),
                    None => Some(read),
                };
                let inner = part
                    .map(|p| self.at_values(p, &cited.binding))
                    .and_then(|at| leaf_path(&at, j, &self.writer));
                let Some(inner) = inner else {
                    return Route::no(
                        "a property's body whose \"and\" has fewer parts than the part the claim met",
                    );
                };
                says = along(&super::super::doc::forms::beta_reduced(s), &inner);
                projected(term, &inner)
            }
            _ => term,
        };
        Route::Built(ProjectedReading { term, says, path })
    }

    /// The differences between a cited item and the claim that are an integer
    /// power on one side and the natural power to its exponent's `toNat` on
    /// the other: each integer power whose exponent the record shows at least
    /// 0 (`nonneg_proof`) rewritten as the natural one, as `forms_converted`
    /// rewrites it, and what is left compared. An integer power of a natural
    /// number cast up, `a ^ (k : ℤ)`, is the natural power `a ^ k` with no
    /// fact asked (`zpow_natCast`). `found` is what differs before this.
    fn compare_powers(
        &self,
        found: Vec<super::super::doc::forms::FormDifference>,
        (compared, claim_read): (&Printed, &Printed),
        counted: &[Printed],
        (cited, sentence, node): (&crate::checker::record::Cited, &Sentence, &Node),
    ) -> PowerForms {
        use super::super::doc::forms;
        let templates = self.writer.templates;
        let widen = |head: &str, at| templates.same_function_at(head, at);
        let mut found = found;
        let mut powered: Vec<NonNegative> = Vec::new();
        let mut cast_powers = false;
        let mut bound: Vec<forms::BoundPower> = Vec::new();
        let natural_casts = forms::casts_natural_exponent(compared)
            || forms::casts_natural_exponent(claim_read);
        let apart = |d: &forms::FormDifference| match d {
            forms::FormDifference::ToNat { .. } => true,
            forms::FormDifference::Cast { .. } => natural_casts,
            _ => false,
        };
        if found.iter().any(apart) {
            cast_powers = natural_casts;
            let mut zpow = forms::integer_exponents(compared);
            zpow.extend(forms::integer_exponents(claim_read));
            powered = self
                .exponents_shown_whole(cited, sentence, node)
                .into_iter()
                .filter(|w| zpow.iter().any(|e| forms::alike(e, &w.exponent)))
                .collect();
            // A power under a sum whose exponent names its letter,
            // at least 0 only for each letter in the sum's range
            // (`bound_rewrite`), where the other side takes that
            // exponent to ℕ.
            let apart_at: Vec<&Printed> = found
                .iter()
                .filter_map(|d| match d {
                    forms::FormDifference::ToNat { term, .. } => Some(term),
                    _ => None,
                })
                .collect();
            bound = forms::bound_integer_powers(compared)
                .into_iter()
                .chain(forms::bound_integer_powers(claim_read))
                .filter(|b| range_lower(&b.over).is_some())
                .filter(|b| apart_at.iter().any(|t| forms::alike(t, &b.exponent)))
                .collect();
            if !powered.is_empty() || cast_powers || !bound.is_empty() {
                let exponents: Vec<Printed> = powered
                    .iter()
                    .map(|w| w.exponent.clone())
                    .chain(bound.iter().map(|b| b.exponent.clone()))
                    .collect();
                let read = |t: &Printed| {
                    forms::with_natural_powers(
                        &forms::with_natural_counts(t, counted),
                        &exponents,
                    )
                };
                found = forms::differences(&read(compared), &read(claim_read), &widen);
            }
        }
        PowerForms {
            found,
            powered,
            cast_powers,
            bound,
        }
    }

    /// How the item a citation gives, its letters given their values, says
    /// what the claim says. `way` is how the citation reads the item's
    /// sentence, and `instance` the item applied to what the citation gives.
    pub(super) fn compare_forms(
        &self,
        reason: Reason,
        (k, node): (usize, &Node),
        cited: &crate::checker::record::Cited,
        sentence: &Sentence,
        (way, instance): (Way, &Instance),
    ) -> FormComparison {
        // An item read as written says what the claim says: where the two
        // write one term in different forms, the build reports it. The
        // sets whose counts differ only in form are converted.
        let mut counted: Vec<Printed> = Vec::new();
        // The sets the two count, each with why it is finite.
        let mut finite: Vec<ShownFinite> = Vec::new();
        // The exponents whose powers differ only in form, each with why it is
        // at least 0, converted alike.
        let mut powered: Vec<NonNegative> = Vec::new();
        // Whether an integer power of a natural number cast up is converted
        // to the natural power alike.
        let mut cast_powers = false;
        // The powers under a sum whose exponent names its letter, converted
        // for each letter in its range.
        let mut bound: Vec<super::super::doc::forms::BoundPower> = Vec::new();
        // The rewrites of the identity elements the checker dropped meeting
        // the reading with the claim (`Cited::meetings`).
        let mut identities: Vec<&'static str> = Vec::new();
        // Whether a numeral's `toNat` is left once a reading is worked out.
        let mut numeral_to_nat = false;
        // A line that is the item's equation turned round, compared turned
        // back and closed by the equation's `symm`.
        let mut turned = false;
        // An item whose statement, its letters given, Lean writes as it
        // writes the line, up to what Lean takes as one term (a function
        // applied worked out, a bound letter renamed, a `set` letter read
        // as its value, `forms::alike_once_set`), closes the line by
        // `exact` alone. Two that are alike but for casts are not enough:
        // an item over any ring given ℤ writes `n ^ (2 : ℤ)`, which ℤ has
        // no power for, and the comparison keeps casts.
        let mut agrees = false;
        // An item that is the line once the identity elements the checker
        // dropped are dropped from both (`Cited::meetings`), with nothing else
        // apart: closed by those rewrites, as a conversion of them alone.
        let mut by_identities = false;
        // What the reading gives, as Lean states it at the citation's values:
        // the sentence as written, or the side a forward reading reaches.
        let compared = match way {
            Way::AsWritten => Some(instance.statement.clone()),
            Way::Forward => consequent(&instance.statement),
            Way::Backward => None,
        };
        if let Some(compared) = compared {
            if let Some(claim) = self.claim_as_stated(reason.just.line, node) {
                let templates = self.writer.templates;
                let widen = |head: &str, at| templates.same_function_at(head, at);
                use super::super::doc::forms;
                // Which way the item's equation faces the claim, as the
                // checker met them (`Cited::facings`).
                turned = matches!(
                    cited.facings.get(k).copied().flatten(),
                    Some(Facing::Turned)
                );
                let claim = match turned {
                    true => forms::turned(&claim),
                    false => claim,
                };
                // The identity elements the checker dropped meeting the two,
                // x − 0 read as x (`Cited::meetings`), dropped from both as
                // the conversion's rewrites drop them, and compared so.
                identities = cited
                    .meetings
                    .get(k)
                    .cloned()
                    .flatten()
                    .map(|m| m.identities.iter().filter_map(identity_lemma).collect())
                    .unwrap_or_default();
                identities.sort_unstable();
                identities.dedup();
                // With functions given as values applied first, as `simp`
                // reads them: (fun k => x ^ (m + 1 - k)) 0 is x ^ (m + 1 - 0).
                let (compared, claim_read) = match identities.is_empty() {
                    true => (compared, claim.clone()),
                    false => (
                        forms::with_identities_dropped(
                            &forms::beta_reduced(&compared),
                            &identities,
                        ),
                        forms::with_identities_dropped(
                            &forms::beta_reduced(&claim),
                            &identities,
                        ),
                    ),
                };
                numeral_to_nat = leaves_numeral_to_nat(&compared)
                    || leaves_numeral_to_nat(&claim_read);
                let mut found = forms::differences(&compared, &claim_read, &widen);
                for d in &found {
                    if let forms::FormDifference::Count {
                        item_set, line_set, ..
                    } = d
                    {
                        for set in [item_set, line_set] {
                            if !counted.contains(set) {
                                counted.push(set.clone());
                            }
                        }
                    }
                }
                // A count is converted only of a set shown finite
                // (`finite_counted`): one not shown so has no count in ℕ to
                // be taken to, and its difference stays. Both rewritten as
                // `forms_converted` rewrites them, what is left is what the
                // conversion leaves.
                if !counted.is_empty() {
                    finite = self.finite_counted(cited, sentence, node);
                    counted.retain(|s| finite.iter().any(|f| forms::alike(&f.set, s)));
                }
                if !counted.is_empty() {
                    found = forms::differences(
                        &forms::with_natural_counts(&compared, &counted),
                        &forms::with_natural_counts(&claim_read, &counted),
                        &widen,
                    );
                }
                PowerForms {
                    found,
                    powered,
                    cast_powers,
                    bound,
                } = self.compare_powers(
                    found,
                    (&compared, &claim_read),
                    &counted,
                    (cited, sentence, node),
                );
                // `exact` takes the two as written: not stated in two known
                // types, which the comparison, reading a count's relation in
                // ℕ, does not ask. An item's type variable is Lean's to fill.
                let known = |t: &Printed| {
                    forms::relation_type(t).filter(|ty| things_of_type(ty).is_empty())
                };
                let two_types = matches!(
                    (known(&compared), known(&claim)),
                    (Some(a), Some(b)) if a != b
                );
                agrees = found.is_empty()
                    && !two_types
                    && !turned
                    && counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && identities.is_empty()
                    && !claim.is_truth()
                    && forms::one_term_once_set(&compared, &claim, &self.set_values());
                by_identities = found.is_empty()
                    && !two_types
                    && counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && !identities.is_empty()
                    && !claim.is_truth();
                // An identity element Lean writes cast up, `((1 : ℤ) : ℚ)`,
                // taken to the numeral first, so its rewrite meets it.
                if by_identities {
                    identities.extend(forms::cast_unit_lemmas(&compared));
                    identities.extend(forms::cast_unit_lemmas(&claim_read));
                    identities.sort_unstable();
                    identities.dedup();
                }
                for d in found {
                    self.forms.borrow_mut().push(FormNote {
                        page_line: reason.just.line,
                        item: cited.item.clone(),
                        difference: d,
                    });
                }
            }
        }
        FormComparison {
            counted,
            finite,
            powered,
            cast_powers,
            bound,
            identities,
            numeral_to_nat,
            turned,
            agrees,
            by_identities,
        }
    }

    /// Sentence `k` of a claim, by the item its reason cites.
    pub(super) fn citation(
        &self,
        reason: Reason,
        k: usize,
        node: &Node,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A phrase's define cited, `D1 n := 6, from 2`: the phrase is
        // written out as its meaning in the claim and in the lines alike, so
        // the claim is what the lines it cites say, in the claim's own
        // words, and the definition, whose two sides are one, adds nothing.
        let phrase = super::super::items::record_of(self.sources.checked, &cited.item)
            .is_some_and(|r| {
                r.phrase.is_some() && r.kind == crate::corpus::RecordKind::Definition
            });
        if phrase {
            return match self.phrase_proof(cited, &reason.just.refs, k, node) {
                Some(p) => Route::Built(Proof::Term(p)),
                None => {
                    Route::no("a phrase's define cited where no line says the claim")
                }
            };
        }
        let Some(concluded) = cited.concluded.get(k) else {
            return Route::no("a claim sentence no conclusion of the item gives");
        };
        let Some(sentence) = item.sentences.get(concluded.sentence) else {
            return Route::no("a conclusion the item does not have in Lean");
        };
        let instance =
            match self.instance_of(sentence, &cited.binding, Some(node), cited) {
                Route::Built(i) => i,
                Route::Declined(d) => return Route::Declined(d),
            };
        let FormComparison {
            counted,
            finite,
            powered,
            cast_powers,
            bound,
            identities,
            numeral_to_nat,
            turned,
            agrees,
            by_identities,
        } = self.compare_forms(
            reason,
            (k, node),
            cited,
            sentence,
            (concluded.way, &instance),
        );
        let statement = instance.statement.clone();
        let inst = instance.term;
        let iff = sentence.says.notation() == BICONDITIONAL;
        let implication = matches!(sentence.says.notation(), CONDITIONAL | IMPLICATION);
        // What the term the reading gives says, as Lean has it: the sentence,
        // or the side a forward reading reaches.
        let says = match concluded.way {
            Way::AsWritten => Some(statement.clone()),
            Way::Forward => consequent(&statement),
            Way::Backward => None,
        };
        // The claim as Lean states it (`claim_as_stated`), and whether a line
        // states it so (`stated_form`).
        let stated = self.stated_form(reason.just.line, node);
        let claim_lean = self.claim_as_stated(reason.just.line, node);
        let premise = || match self.premise(cited, &statement) {
            Some(p) => Route::Built(p),
            None => Route::no("a premise of a cited sentence no line says"),
        };
        let term = match concluded.way {
            Way::AsWritten => inst,
            Way::Forward if iff => match premise() {
                Route::Built(p) => forwards_of(inst, p),
                Route::Declined(d) => return Route::Declined(d),
            },
            Way::Forward if implication => match premise() {
                Route::Built(p) => applied_to(inst, p),
                Route::Declined(d) => return Route::Declined(d),
            },
            Way::Forward => {
                return Route::no("a forward reading of a sentence that is no ↔ or if")
            }
            Way::Backward => {
                return self.definition_backwards(Backwards {
                    reason,
                    k,
                    node,
                    cited,
                    sentence,
                    statement: &statement,
                    inst,
                    claim_lean: &claim_lean,
                    stated: stated.is_some(),
                });
            }
        };
        let ProjectedReading { term, says, path } = match self.projected_reading(
            Projection {
                node,
                iff,
                sentence,
                part: concluded.part,
                cited,
                k,
            },
            term,
            says,
        ) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A define the step cites is written out first, as for algebra.
        let defines = self.cited_defines(&reason.just.refs);
        // An item that says a natural power of an integer is one gives the
        // claim nothing to read where the claim's exponent is an integer
        // the page shows not negative, 2^(n − 1); the writer gives the
        // witness.
        // The part of the item's sentence the reading gives, the sentence as
        // written or the side a forward reading reaches, and of it the part
        // of an "and" the step takes, at the citation's values, written as
        // the step's lines are (`docs/LEAN.md`, a citation). Kept where it is
        // spelt otherwise than Lean's statement of that part, which
        // the reading of the item then reads as it
        // (`spelling::read_as_written`).
        let given = match concluded.way {
            Way::AsWritten => Some(&sentence.says),
            Way::Forward => node_consequent(&sentence.says),
            Way::Backward => None,
        };
        let as_written = match (given, &path) {
            (Some(given), Some(path)) => node_along(given, path, &self.writer),
            (given, None) => given,
            (None, Some(_)) => None,
        }
        .and_then(|part| self.written_at_values(part, &cited.binding));
        // Where the two are one statement (`one_statement`), the writer's
        // copy, whose terms carry the types Lean's statement of an item over
        // any ring leaves to Lean, is what the closer compares with the
        // claim.
        let alike = match (&as_written, &says) {
            (Some(w), Some(s)) => one_statement(w, s),
            _ => false,
        };
        let says = match (&as_written, says) {
            (Some(w), Some(_)) if alike => Some(w.clone()),
            (_, s) => s,
        };
        let read_as_written = match (&as_written, &says, &claim_lean) {
            (Some(written), Some(said), Some(claim))
                if counted.is_empty()
                    && powered.is_empty()
                    && !cast_powers
                    && bound.is_empty()
                    && !agrees =>
            {
                let claim = StepClaim {
                    printed: claim,
                    stated: stated.is_some(),
                };
                self.read_in_spelling(Some(cited), &term, said, written, claim)
            }
            _ => None,
        };
        let conversion = Conversion {
            finite: &finite,
            whole: &powered,
            bound: &bound,
            cast_powers,
            identities: &identities,
            numeral_to_nat,
        };
        let closed = match read_as_written {
            _ if !counted.is_empty()
                || !powered.is_empty()
                || cast_powers
                || !bound.is_empty() =>
            {
                forms_converted(&term, &conversion, turned)
            }
            _ if agrees => Proof::By(Tactic::Exact(term)),
            // The item read in the step's spelling and met with the claim
            // (`docs/LEAN.md`, a citation); the recorded identities where
            // they are all that stands apart; the closer's rules where
            // neither holds.
            Some(read) => read,
            None if by_identities => forms_converted(&term, &conversion, turned),
            None => match self.closer(
                node,
                claim_lean.as_ref().map(|printed| StepClaim {
                    printed,
                    stated: stated.is_some(),
                }),
                term,
                says.as_ref(),
                HowMet {
                    facing: cited.facings.get(k).copied().flatten(),
                    meeting: cited.meetings.get(k).and_then(Option::as_ref),
                },
                cited_bridge(
                    cited,
                    sentence,
                    &Cites::of(
                        node,
                        says.as_ref(),
                        claim_lean.as_ref(),
                        &self.set_values(),
                    ),
                ),
            ) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        // The goal alone: each line the item is given puts the defines in
        // itself, where it is passed (`supplied_proof`).
        let goal = RewriteAt {
            at: super::super::doc::Location::Goal,
            said: vec![node.clone()],
            stated: self.writer.formula(node).built().into_iter().collect(),
        };
        Route::Built(haves_then(
            written_out(&defines, &[goal], &self.writer),
            closed,
        ))
    }

    /// The claim a definition's sentence is read backwards for: the
    /// definition's left side, which its right side gives by the sentence's
    /// `mpr`, given the witness the checker found.
    pub(super) fn definition_backwards(
        &self,
        asked: Backwards<'_>,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        let Backwards {
            reason,
            k,
            node,
            cited,
            sentence,
            statement,
            inst,
            claim_lean,
            stated,
        } = asked;
        let witness = match self.witnesses(statement, cited, k, &reason.just.refs) {
            Route::Built(w) => w,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A claim a requires line above already states, "0 ≤ b − c"
        // for "b − c ∈ ℕ₀", is that line: tried first, as it is
        // quick and the others may search long.
        // A natural given as an integer's `toNat`, put back by `▸`,
        // which the goal guides in an `exact`; where the claim is in
        // a wider type than the item, the term stated by a `have`
        // and cast to it.
        let by_to_nat = inst.names("Int.toNat_of_nonneg");
        let mpr = Printed {
            kind: super::super::doc::TermKind::App {
                head: Box::new(Printed {
                    kind: super::super::doc::TermKind::Field {
                        inner: Box::new(t::bracket(inst)),
                        field: "mpr".to_string(),
                    },
                    ty: None,
                }),
                args: vec![super::super::doc::Arg::Explicit(witness)],
                explicit: false,
            },
            ty: None,
        };
        // The definition's left side as Lean states it at the
        // citation's values, where it is the claim up to what Lean
        // takes as the same term: a function applied worked out,
        // `(fun n => x n + C) n` as `x n + C`, a bound letter
        // renamed, a `set` letter read as its value
        // (`forms::alike_once_set`), the `toNat` of a natural number
        // cast up that number (`forms::one_term_once_set`). The
        // reading proves the claim as it stands, which the term's
        // type checks by definitional equality.
        let left = left_side(statement);
        let values = self.set_values();
        let as_claimed = match (&left, claim_lean) {
            (Some(left), Some(claim)) => {
                super::super::doc::forms::one_term_once_set(left, claim, &values)
            }
            _ => false,
        };
        if as_claimed && !by_to_nat {
            return Route::Built(Proof::Term(mpr));
        }
        // The definition's left side at the citation's values, as the
        // step's lines write it, read from the reading and met with
        // the claim, as a sentence read forwards is.
        let written = node_antecedent(&sentence.says)
            .and_then(|part| self.written_at_values(part, &cited.binding));
        let read = match (&written, &left, claim_lean) {
            (Some(written), Some(left), Some(claim)) if !by_to_nat => {
                let said = match one_statement(written, left) {
                    true => written,
                    false => left,
                };
                let claim = StepClaim {
                    printed: claim,
                    stated,
                };
                self.read_in_spelling(Some(cited), &mpr, said, written, claim)
            }
            _ => None,
        };
        if let Some(read) = read {
            return Route::Built(read);
        }
        // An item over any ring or any set, taken at ℤ or ℕ, states
        // a membership in its general terms, where the claim of an
        // integer states its own fact: the Lean facts the record
        // gives (`cited_bridge`).
        let at = Cites::of(node, left.as_ref(), claim_lean.as_ref(), &values);
        match (cited_bridge(cited, sentence, &at), by_to_nat) {
            (Some(CitedBridge::Rules(rules)), false) => {
                return Route::Built(Proof::By(t::simpa_only(rules, mpr)))
            }
            (Some(CitedBridge::Cast), false) => {
                return Route::Built(Proof::By(t::exact_mod_cast(mpr)))
            }
            _ => {}
        }
        let mut ways = vec![
            t::steps(vec![t::call("assumption", vec![]), t::call("done", vec![])]),
            Tactic::Exact(mpr.clone()),
        ];
        if by_to_nat {
            ways.push(t::on_h(&mpr, vec![t::exact_mod_cast(t::hyp("h"))]));
        }
        ways_proof(ListReason::DefinitionBackwards, ways)
    }

    /// The proof of the right side of a definition a step folds, the `k`th
    /// sentence the citation concludes: its parts as the checker took them
    /// apart at the citation's values (`Cited::unfolded`), each proved where
    /// the checker found it supplied (`unfolded_proofs`); or the side whole,
    /// by the line the checker read it from (`Cited::firsts`), as Lean has
    /// it in `statement`, the definition at the citation's values, where a
    /// witness is a letter the line cited binds. Declined where no line
    /// says it.
    pub(super) fn witnesses(
        &self,
        statement: &Printed,
        cited: &crate::checker::record::Cited,
        k: usize,
        refs: &[String],
    ) -> Route<Printed> {
        let lean_body = right_side(statement);
        let whole = || match self.shown_by_line(cited, lean_body.as_ref(), &[]) {
            Some(p) => Route::Built(p),
            None => {
                Route::no("a definition's right side no line the checker found says")
            }
        };
        if self.witness_bound_by_line(cited, refs) {
            return whole();
        }
        let (Some(Some(parts)), Some(lean)) = (cited.unfolded.get(k), &lean_body)
        else {
            return whole();
        };
        // What a line said of a witness the page wrote as a fraction that
        // is an integer, put in scope where the witness's facts are proved.
        let mut known = Vec::new();
        match self.unfolded_proof(lean, parts.iter().collect(), &mut known) {
            Some(proof) => Route::Built(proof),
            None => whole(),
        }
    }

    /// Whether a witness the citation gives is a letter bound by a line it
    /// cites, the k of its "there is k": no value in scope, so the line says
    /// the definition's right side whole.
    pub(super) fn witness_bound_by_line(
        &self,
        cited: &crate::checker::record::Cited,
        refs: &[String],
    ) -> bool {
        let bound_here: std::collections::BTreeSet<String> = self
            .cited_parts(refs)
            .iter()
            .filter(|c| c.node.notation() == crate::notations::THERE_IS)
            .filter_map(|c| c.node.children.first())
            .filter(|l| l.is_name())
            .map(|l| l.text.to_string())
            .collect();
        cited
            .bound
            .values()
            .any(|v| v.is_name() && bound_here.contains(v.text.as_str()))
    }

    /// The proof of `lean`, Lean's statement of a definition's right side or
    /// of a "there is"'s body at its witness, from `parts`, the checker's
    /// parts of the same (`Cited::unfolded`), taken in order, one to each
    /// statement Lean joins by "and". Where the page asks more parts than
    /// Lean states, a membership of a number system that is a Lean type, x
    /// ∈ ℝ, is one Lean does not state, and is left out. None where the two
    /// do not then take the same number of parts, or a "there is" meets no
    /// "there is" of Lean's.
    pub(super) fn unfolded_proof(
        &self,
        lean: &Printed,
        mut parts: Vec<&Unfolded>,
        known: &mut Vec<Tactic>,
    ) -> Option<Printed> {
        let wanted = lean_conjuncts(lean);
        while parts.len() > wanted {
            let at = parts.iter().position(|p| type_membership(p))?;
            parts.remove(at);
        }
        if parts.len() != wanted {
            return None;
        }
        let mut parts = parts.into_iter();
        let proof = self.unfolded_tree(lean, &mut parts, known)?;
        parts.next().is_none().then_some(proof)
    }

    /// The proof of `lean`, its statements joined by "and" each proved by the
    /// next of `parts`: a fact from where the checker found it supplied, as
    /// Lean states it; a "there is" by its witness, its guard where Lean
    /// writes one, an integer's of ℕ or ℕ₀ or a member's of a set, and its
    /// body at the witness (`unfolded_proof`), the membership the first of
    /// the body's parts where Lean writes it there.
    pub(super) fn unfolded_tree<'u>(
        &self,
        lean: &Printed,
        parts: &mut impl Iterator<Item = &'u Unfolded>,
        known: &mut Vec<Tactic>,
    ) -> Option<Printed> {
        let lean = super::super::doc::forms::beta_reduced(&unparenthesized(lean));
        if let super::super::doc::TermKind::Infix { op, lhs, rhs } = &lean.kind {
            if op.symbol == "∧" {
                let left = self.unfolded_tree(lhs, parts, known)?;
                let right = self.unfolded_tree(rhs, parts, known)?;
                return Some(joined(vec![left], right));
            }
        }
        match parts.next()? {
            Unfolded::Fact { by, .. } => self.unfolded_fact(&lean, by, known),
            Unfolded::Witness {
                value,
                member,
                body,
            } => {
                let Unfolded::Fact { fact, by } = member.as_ref() else {
                    return None;
                };
                let [_, set] = fact.children.as_slice() else {
                    return None;
                };
                let system = super::super::expr::system_of(set);
                let term = match system {
                    Some(s) => {
                        let w = self
                            .witness(value, super::super::expr::letter_type(s))
                            .built()?;
                        known.extend(w.known);
                        w.term
                    }
                    // A witness in a set: a number at its own type or a
                    // member as the writer writes one.
                    None => match self.writer.carrier(value) {
                        Route::Built(at) if self.writer.is_number(value) => {
                            self.writer.number_fixed(value, at).built()?
                        }
                        _ => self.writer.set_term(value).built()?,
                    },
                };
                let (guard, at) = exists_at(Some(&lean), &term);
                let at = at?;
                let mut proofs = vec![term];
                let mut inner: Vec<&Unfolded> = body.iter().collect();
                match guard {
                    Some(guard) => proofs.push(self.unfolded_fact(&guard, by, known)?),
                    None => inner.insert(0, member),
                }
                let body = self.unfolded_proof(&at, inner, known)?;
                Some(joined(proofs, body))
            }
        }
    }

    /// The proof of one fact of a definition's right side, `wanted` as Lean
    /// states it at the citation's values: from where the checker found it
    /// supplied, after the tactics `known` that put a witness's facts in
    /// scope; None where no line supplies it or the line says it otherwise
    /// than Lean asks.
    pub(super) fn unfolded_fact(
        &self,
        wanted: &Printed,
        by: &SuppliedBy,
        known: &[Tactic],
    ) -> Option<Printed> {
        match self.supplied_proof(by, wanted, None).built() {
            Some(p) => Some(after_known(known, p)),
            None => self.with_known(by, wanted, known),
        }
    }

    /// The proof of `wanted`, a relation of a number a line names, after
    /// the tactics `known` that put its spec in scope as `this`, `(c : ℚ) =
    /// (N − 1)/2`, from the line `by` names stating the number's term in a
    /// wider type, `(N : ℚ) = 2·((N − 1)/2) + 1`: the goal moved into the
    /// line's type (`qify`, `rify`), the number put back as its term by the
    /// spec (`rw [this]`), and met with the line by `linarith only`. None
    /// where no tactic is known first, the relation is no equation or order,
    /// or the line is in no wider type.
    pub(super) fn with_known(
        &self,
        by: &SuppliedBy,
        wanted: &Printed,
        known: &[Tactic],
    ) -> Option<Printed> {
        use super::super::doc::{forms, LeanType};
        use super::super::tactics as t;
        use super::super::templates::Num;
        if known.is_empty()
            || !matches!(relation_symbol(wanted)?, "=" | "<" | "≤" | ">" | "≥")
        {
            return None;
        }
        let (proof, says) = self.line_proof(by).built()?;
        let into = match (forms::relation_type(&says)?, forms::relation_type(wanted)?) {
            (LeanType::Num(Num::Rat), LeanType::Num(Num::Int)) => "qify",
            (LeanType::Num(Num::Real), LeanType::Num(Num::Int | Num::Rat)) => "rify",
            _ => return None,
        };
        // The number put back as its term, from the number to the term,
        // which leaves the line's own statement.
        let mut tactics = known.to_vec();
        tactics.push(t::call(into, vec![]));
        tactics.push(t::call("rw", vec![t::rules(vec![t::hyp("this")])]));
        tactics.push(t::call(
            "linarith",
            vec![TacticArg::Only, t::rules(vec![proof])],
        ));
        Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(
            tactics,
        ))))
    }

    /// A witness of a "there is" over `ty`: the value as Lean computes it
    /// there, or, for a value the page writes as a fraction that a line
    /// says is an integer, the integer that line gives, with what it says
    /// of it put in scope where the witness's facts are proved.
    pub(super) fn witness(
        &self,
        value: &Node,
        ty: super::super::templates::Num,
    ) -> Route<Witness> {
        match self.writer.number_fixed(value, ty) {
            Route::Built(p) => Route::Built(Witness {
                term: p,
                known: None,
            }),
            Route::Declined(d) => match self.integer_line(value, ty) {
                Some(line) => Route::Built(Witness {
                    term: line.chosen(ty),
                    known: Some(Tactic::Fact(Printed::applied(
                        "Classical.choose_spec",
                        super::super::doc::Source::Core,
                        vec![line.proof],
                        super::super::doc::LeanType::Prop,
                    ))),
                }),
                None if ty == super::super::templates::Num::Int => {
                    match self.named_witness(value) {
                        Route::Built(w) => Route::Built(w),
                        Route::Declined(_) => Route::Declined(d),
                    }
                }
                None => Route::Declined(d),
            },
        }
    }

    /// A witness in ℤ of a term Lean computes wider, m² of an m a line the
    /// step names puts in ℕ: the whole number the step's lines name
    /// (`whole_witness`), chosen from the proof that there is one, and that
    /// proof's spec put in scope where the witness's facts are proved.
    pub(super) fn named_witness(&self, value: &Node) -> Route<Witness> {
        use super::super::doc::{LeanType, Op, Proof};
        use super::super::tactics as t;
        let Some(i) = self.step_now.get() else {
            return Route::no("a witness outside a step");
        };
        let Some(letters) = self.rec.introduced.get(i) else {
            return Route::no("a step the checker's record has no letters for");
        };
        let facts = self.step_facts(i);
        // The witness stands inside a term, so its proof is one line.
        let proof = match self.whole_witness(value, letters, &facts) {
            Route::Built(p) => on_one_line(p),
            Route::Declined(d) => return Route::Declined(d),
        };
        let at = match self.writer.carrier(value) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        };
        let written = match self.writer.number_fixed(value, at) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        let ty = self.writer.num_type(at);
        let letter = super::super::expr::witness_letter(value);
        let says = Printed::of(
            super::super::doc::TermKind::Quantified {
                quant: super::super::doc::Quant::Exists,
                letter: letter.clone(),
                letter_ty: LeanType::Num(super::super::templates::Num::Int),
                guard: None,
                body: Box::new(Printed::infix(
                    Op::EQUALS,
                    Printed::cast(t::hyp(&letter), ty),
                    written,
                    LeanType::Prop,
                )),
                bounded: false,
            },
            LeanType::Prop,
        );
        let name = "named_witness".to_string();
        let have = have_bracketed(Tactic::Have {
            name: name.clone(),
            says,
            proof: Box::new(proof),
        });
        let chosen = Printed::applied(
            "Classical.choose",
            super::super::doc::Source::Core,
            vec![t::hyp(&name)],
            LeanType::Num(super::super::templates::Num::Int),
        );
        let spec = Printed::applied(
            "Classical.choose_spec",
            super::super::doc::Source::Core,
            vec![t::hyp(&name)],
            LeanType::Prop,
        );
        let term = t::bracket(t::by_term(Proof::By(Tactic::Seq(vec![
            have.clone(),
            Tactic::Exact(chosen),
        ]))));
        Route::Built(Witness {
            term,
            known: Some(Tactic::Seq(vec![have, Tactic::Fact(spec)])),
        })
    }

    /// A line the step names saying a term is an integer, `(N − 1)/2 ∈ ℤ`,
    /// or that it is in a range, where `value` is that term as Lean writes
    /// it, with its Lean name and what it says beside the equation; None
    /// where no line says so. Lean states that line as `∃ m : ℤ, (m : ℚ) =
    /// …`, so the integer is the witness it gives.
    pub(super) fn integer_line(
        &self,
        value: &Node,
        ty: super::super::templates::Num,
    ) -> Option<SaidLine> {
        // Lean states each as `∃ m : T, ↑m = x` of a term wider than T, of ℤ,
        // ℚ and ℝ, and of ℕ and ℕ₀ as `∃ m : ℤ, 0 ≤ m ∧ ↑m = x`, whose
        // witness is an integer too.
        let at = self.writer.carrier(value).built()?;
        let systems: Vec<super::super::expr::System> = match ty {
            super::super::templates::Num::Int => vec![
                super::super::expr::System::Type(ty),
                super::super::expr::System::NonNegative,
                super::super::expr::System::Positive,
            ],
            super::super::templates::Num::Rat | super::super::templates::Num::Real => {
                vec![super::super::expr::System::Type(ty)]
            }
            _ => return None,
        };
        let wanted = self.writer.number(value, at).built()?.untyped();
        // Whether the check found a line the reason names stating the term
        // in that system (`held`): such a line is the one taken. A range is
        // no statement of a system, and its integer is Lean's way of
        // writing the line.
        let asked = match ty {
            super::super::templates::Num::Int => crate::rules::System::Z,
            super::super::templates::Num::Rat => crate::rules::System::Q,
            _ => crate::rules::System::R,
        };
        let stated = matches!(
            self.held(value, asked),
            Some(crate::checker::record::LinesHold::Stated { .. })
        );
        // The latest such line the step names, or part of an "and".
        let named = self.named_now.borrow();
        let mut parts = Vec::new();
        for (key, lines) in &self.trees {
            if !named.as_ref().is_some_and(|n| n.contains(key)) {
                continue;
            }
            for s in lines {
                conjuncts(
                    &s.node,
                    s.proof.clone(),
                    s.says.clone(),
                    &mut parts,
                    &self.writer,
                );
            }
        }
        parts.iter().rev().find_map(|c| {
            let [term, set] = c.node.children.as_slice() else {
                return None;
            };
            if c.node.notation() != crate::notations::MEMBERSHIP {
                return None;
            }
            // A range of a wider term, k ∈ {1, …, n} of a real k, is its
            // integer with the range, `∃ m : ℤ, ↑m = k ∧ m ∈ …`
            // (`wide_range_member`).
            let beside = match super::super::expr::system_of(set) {
                Some(s) if stated && systems.contains(&s) => match s {
                    super::super::expr::System::Type(_) => Beside::Nothing,
                    _ => Beside::Order,
                },
                None if ty == super::super::templates::Num::Int
                    && wide_range_member(&self.writer, &c.node) =>
                {
                    Beside::Range
                }
                _ => return None,
            };
            let same = self.writer.number(term, at).built().map(|p| p.untyped())
                == Some(wanted.clone());
            same.then(|| SaidLine {
                proof: c.proof.clone(),
                beside,
            })
        })
    }

    /// `obtain`: the witnesses of a "there is" an item gives, named as the
    /// claim names them.
    /// The "there is" an `obtain` takes its witnesses from: a line of the
    /// page it names, or a sentence of the item it cites.
    pub(super) fn obtained_from(&self, i: usize) -> Route<Obtained> {
        let step = &self.thm.steps[i];
        if self.rec.cited[i].is_none() && step.just.obtained_from.is_none() {
            // The sentence, or the part of one, of the lines named that
            // says "there is".
            // A "for all" line is read at the block's letter, as the checker
            // reads it.
            let mut names = std::collections::BTreeSet::new();
            for s in step.claim.sentences() {
                if let Some(n) = self.rec.page.get(&s) {
                    names.extend(n.names());
                }
            }
            names.retain(|n| !step.just.obtained.contains(n));
            return match self
                .cited_parts(&step.just.from)
                .into_iter()
                .map(|c| self.at_recorded_letter(&c, &names).unwrap_or(c))
                .find(|c| {
                    c.node.notation() == crate::notations::THERE_IS
                        || &*c.node.notation_name() == "there-is-some"
                }) {
                Some(c) => Route::Built(Obtained {
                    term: c.proof,
                    says: c.node,
                    binding: crate::matching::Binding::new(),
                    lean: None,
                }),
                None => Route::no("an obtain from no line that says \"there is\""),
            };
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(at) = cited.obtained else {
            return Route::no("an obtain that takes no sentence of its item");
        };
        let before: usize = match self.sources.checked.library.groups.get(&cited.item) {
            Some(Some(groups)) => {
                groups[..cited.group].iter().map(|g| g.gives.len()).sum()
            }
            _ => 0,
        };
        let Some(sentence) = item.sentences.get(before + at) else {
            return Route::no("an obtain of a sentence the item does not have in Lean");
        };
        let mut binding = cited.binding.clone();
        for (k, v) in &cited.written {
            binding.entry(*k).or_insert_with(|| v.clone());
        }
        let (inst, statement) = match self.instance_of(sentence, &binding, None, cited)
        {
            Route::Built(i) => (i.term, i.statement),
            Route::Declined(d) => return Route::Declined(d),
        };
        // A definition's right side is the "there is"; a theorem's sentence
        // is one.
        let iff = sentence.says.notation() == BICONDITIONAL;
        let says = match (iff, sentence.says.children.as_slice()) {
            (true, [_, right]) => right.clone(),
            _ => sentence.says.clone(),
        };
        // At the citation's values, a property given applied where the
        // sentence applies it: P(d) of set-builder is "there are m, n with
        // d = a·m + b·n".
        let says =
            read_at_values(&says, &binding, &self.sources.checked.grammar.binders());
        // A definition read forwards from the line that says its left side.
        let term = match iff {
            true => match self.premise(cited, &statement) {
                Some(p) => forwards_of(inst, p),
                None => {
                    return Route::no("a premise of a cited definition no line says")
                }
            },
            false => inst,
        };
        // The "there is" as Lean states it: the sentence, or the side of a
        // definition the forward reading reaches.
        let lean = match iff {
            true => consequent(&statement),
            false => Some(statement),
        };
        Route::Built(Obtained {
            term,
            says,
            binding,
            lean,
        })
    }
}
