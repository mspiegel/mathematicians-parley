//! Proof methods: a recorded substitution written out.

use super::*;

impl<'a> Proof<'a> {
    /// `substitute`: the claim is a line, or the left side of a calculation's
    /// link, with a term put for another by an equation, which a line says
    /// or arithmetic works out.
    /// A substitution as the checker recorded it (`CheckedTheorem::
    /// substituted`): what the equation is put into, written with each place
    /// it is put at as one fresh letter of the type the term put for has
    /// there, the motive; and the equation's proof, turned where the record
    /// puts its left side for its right. Put into a line, `Eq.subst` along
    /// the motive takes the line to the claim; put into a side of the claim
    /// `t = t′`, `congrArg` of the motive is the claim, turned where the side
    /// is its right. Either is closed by `exact_mod_cast`, as a numeral put
    /// where the claim writes it in a wider type is written with its cast.
    /// Declined where the record has none. A row of a `substitute` step
    /// (`SubstitutedInto::RowAbove`) is put into the row above as into a
    /// line, its change proved by its reason; a step's own equation from no
    /// line, by its proof (`GivenEquation`). A putting that meets the claim
    /// turned round (`Meeting::turned`), `b ≡ c` of the claim `c ≡ b`, turns
    /// the goal first, `symm`, and proves it as written.
    pub(super) fn substituted_by_record(
        &self,
        line: usize,
        sentence: Option<usize>,
        claim: &Node,
        row: Option<&GivenEquation>,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        let turned = self
            .substitution_record(line, sentence, row.is_some_and(|r| r.above.is_some()))
            .is_some_and(|r| r.meeting.turned);
        let proof = self.substituted_as_written(line, sentence, claim, row, writer);
        match turned {
            false => proof,
            true => proof.map(|p| {
                let rest = match p {
                    Proof::Term(t) => Tactic::Exact(t),
                    Proof::By(t) => t,
                    Proof::Block(ts) => Tactic::Seq(ts),
                };
                Proof::By(Tactic::Seq(vec![
                    super::super::tactics::call("symm", vec![]),
                    rest,
                ]))
            }),
        }
    }

    /// What closes a recorded putting: the identity elements it leaves and
    /// the claim drops, and the casts back the step names. A putting that
    /// makes the claim only turned round, or with a listed set's members in
    /// another order (`Substituted::meeting`), is no motive's: the claim is
    /// not the line with the equation put in. Another spelling of the same
    /// notation, `0 < x` of `x > 0`, is one Lean writes alike or unfolds
    /// (`Meeting::respelled`). `natural_put_whole` is whether a natural
    /// number is put for a letter written by its `toNat`.
    pub(super) fn put_closing(
        &self,
        rec: &crate::checker::record::Substituted,
        [was, now]: [&Node; 2],
        (line, claim): (usize, &Node),
        cast_to_nat: bool,
        natural_put_whole: bool,
    ) -> Route<PutClosing> {
        let m = &rec.meeting;
        if m.permuted || m.renamed {
            return Route::no("a putting that meets the claim other than as written");
        }
        // The identity elements the putting leaves and the claim drops, as
        // the record names them, `1·x` as `x` by `one_mul`.
        let dropped: Option<Vec<&'static str>> =
            m.identities.iter().map(identity_lemma).collect();
        let Some(mut dropped) = dropped else {
            return Route::no("an identity element dropped that no lemma names");
        };
        // A natural number put for a letter written by its `toNat` leaves
        // the `toNat` of its cast, which is it.
        if natural_put_whole {
            dropped.push("Int.toNat_natCast");
        }
        // Dropped with the casts pushed, as rewrites `push_cast` takes beside
        // its own: a numeral put where the claim has it in a wider type is
        // cast, `((1 : ℤ) : ℝ) * x`, which `one_mul` meets only as `1 * x`,
        // and `push_cast` may drop the identity itself.
        // Where a side holds a cast of a `toNat`, the casts back of the
        // whole numbers the step names (`Writer::whole_back`), which take
        // `((2^p − 1).toNat : ℤ)` in the goal to the integer the line says.
        let backs: Vec<Printed> = [was, now]
            .iter()
            .filter_map(|n| self.writer.whole_back(n))
            .collect();
        Route::Built(PutClosing {
            cast_to_nat,
            dropped,
            backs,
            wanted: self.claim_as_stated(line, claim),
        })
    }

    /// How the places a recorded putting is made at are written: which of
    /// the exponents stay natural numbers, which are said whole, which are
    /// integers. `writer` is the step's, which knows how the lines and the
    /// claim write the terms where a natural number is wanted; `knowing` adds
    /// what the step's lines bound.
    pub(super) fn put_exponents(
        &self,
        rec: &crate::checker::record::Substituted,
        [left, right]: [&Node; 2],
        [was, now]: [&Node; 2],
        writer: &Writer,
        knowing: &Writer,
    ) -> PutExponents {
        use super::super::expr::NaturalForm;
        // A side holding a cast of a `toNat`, `((2^p − 1).toNat : ℤ)`, which
        // `push_cast` moves only knowing the term is not negative: what the
        // motive makes is the claim as it stands, closed with no cast moved.
        // A `toNat` with no cast over it, an exponent's `2 ^ m.toNat`, is a
        // term like any other.
        let cast_to_nat = [left, right].iter().any(|side| {
            self.writer
                .formula(side)
                .built()
                .or_else(|| {
                    self.writer
                        .number(side, super::super::templates::Num::Int)
                        .built()
                })
                .is_some_and(|p| casts_a_to_nat(&p))
        });
        // A place that is an exponent is written by what the page says of
        // its term, `(−1)^m.toNat` of m said a whole number. Where the page
        // says so of the term put for and of the term put, and neither is a
        // natural-number letter written as it stands, the motive's letter is
        // said whole as well (`Writer::wholes`), and its exponent is written
        // as theirs are; any other exponent declines.
        let exponent = rec
            .put
            .places
            .iter()
            .any(|p| place_is_exponent(&rec.start, p));
        let form = |n: &Node| writer.natural_form(n);
        // An equation of natural numbers put at exponents, φ(n) = |S| put in
        // a^φ(n), or at a count of a finite set, |{a}| = 1 put in |{a}| ≤
        // |A|: Lean writes either as a natural number, so the equation is put
        // there in ℕ, stated so first (`e_nat`), and the motive's letter is
        // of ℕ.
        let natural_place = |p: &Vec<usize>| {
            place_is_exponent(&rec.start, p)
                || at_path(&rec.start, p)
                    .is_some_and(|n| self.writer.finite_count(n).is_some())
        };
        let natural_exponent = !rec.put.places.is_empty()
            && rec.put.places.iter().all(natural_place)
            && form(was) == NaturalForm::AsItIs
            && natural_form_named(knowing, now) != NaturalForm::Integer;
        // Else the motive's letter is written as Lean writes the exponents
        // at both its values (`Writer::natural_form`): as its `toNat` where
        // both are, a numeral put counting so, since its `toNat` works out
        // (`Int.reduceToNat`), and a natural number put, the `toNat` of its
        // cast, which is it (`Int.toNat_natCast`); else an integer, its power
        // an integer one, converted to the claim's after (`int_exponent`,
        // `powers_converted_at`), each exponent's fact from the record. A
        // difference put for a whole letter, p − 1 for k, leaves it an
        // integer.
        let natural_put = form(now) == NaturalForm::AsItIs
            && now.notation() != crate::notations::NUMERAL;
        let now_to_nat = form(now) == NaturalForm::ToNat
            || now.notation() == crate::notations::NUMERAL
            || natural_put;
        let whole_was = exponent
            && !natural_exponent
            && form(was) == NaturalForm::ToNat
            && now_to_nat;
        PutExponents {
            cast_to_nat,
            natural_exponent,
            natural_put,
            whole_was,
            int_exponent: exponent && !natural_exponent && !whole_was,
        }
    }

    /// A putting at no place: the line it is put into is the claim once the
    /// theorem's outside defines are written out, as Lean has both
    /// (`Substituted::put`).
    fn put_at_no_place(
        &self,
        rec: &crate::checker::record::Substituted,
        line: usize,
        claim: &Node,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use crate::checker::record::SubstitutedInto;
        let SubstitutedInto::Line(at) = &rec.into else {
            return Route::no("a putting at no place into no line");
        };
        let (proof, says) = match self.line_says(at) {
            Route::Built(both) => both,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(wanted) = self.claim_as_stated(line, claim) else {
            return Route::no("a claim Lean states no form of");
        };
        match self.proof_meeting(proof, &says, &wanted) {
            Some(proved) => Route::Built(Proof::By(Tactic::Exact(proved.term()))),
            None => Route::no(
                "a line put at no place that Lean states otherwise than the claim",
            ),
        }
    }

    /// The equation a recorded putting uses, facing as the record puts it:
    /// the line's part the record names, turned where the line says it the
    /// other way round; a row's change, which its reason proves as the record
    /// writes it.
    pub(super) fn putting_equation(
        &self,
        rec: &crate::checker::record::Substituted,
        row: Option<&GivenEquation>,
    ) -> Route<PuttingEquation> {
        // Which way the equation's proof is used: as the record puts it, the
        // side put for on the left.
        let put_facing = |as_said: bool| match as_said != rec.put.turned {
            true => Facing::Straight,
            false => Facing::Turned,
        };
        match (&rec.from, row) {
            (Some(from), _) => {
                let part = match self.line_part(from) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // Which way round the line says the recorded equation
                // (`Substituted::line_facing`).
                let as_said = rec.line_facing != Some(Facing::Turned);
                let equation = faced(part.proof.clone(), put_facing(as_said));
                Route::Built(PuttingEquation { part, equation })
            }
            (None, Some(row)) => {
                let equation = faced(row.change.proof.clone(), put_facing(true));
                Route::Built(PuttingEquation {
                    part: row.change.clone(),
                    equation,
                })
            }
            (None, None) => Route::no("an equation the record takes from no line"),
        }
    }

    /// `substituted_by_record` of a putting that makes the claim as written,
    /// or turned round where the goal is turned already. `writer` is the
    /// step's, which knows what the step's lines say of its terms.
    pub(super) fn substituted_as_written(
        &self,
        line: usize,
        sentence: Option<usize>,
        claim: &Node,
        row: Option<&GivenEquation>,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::LeanType;
        use super::super::tactics as t;
        use crate::checker::record::SubstitutedInto;
        let found = self.substitution_record(
            line,
            sentence,
            row.is_some_and(|r| r.above.is_some()),
        );
        let Some(rec) = found else {
            return Route::no("a substitution the checker recorded no way of");
        };
        // Put at no place: the line is the claim once the theorem's outside
        // defines are written out, as Lean has both (`Substituted::put`).
        if rec.put.places.is_empty() {
            return self.put_at_no_place(rec, line, claim);
        }
        let [left, right] = rec.equation.children.as_slice() else {
            return Route::no("a recorded equation of no two sides");
        };
        let (was, now) = match rec.put.turned {
            false => (left, right),
            true => (right, left),
        };
        let PuttingEquation { part, equation } = match self.putting_equation(rec, row) {
            Route::Built(found) => found,
            Route::Declined(d) => return Route::Declined(d),
        };
        // A term put for that is no number, a set or a group's element: the
        // motive's letter is of its type, and there are no casts to move.
        if let Some(letter_ty) = self.member_letter(was) {
            let put = PutTerms { was, now };
            return self
                .substituted_members(rec, letter_ty, put, equation, row, line, claim);
        }
        // The step's writer knowing what its lines bound, its requires lines
        // among them, which an equation stated in ℕ may use, φ(p) = (p − 1).toNat
        // of the requires line p − 1 ∈ ℕ₀.
        let lines: Vec<Node> = self
            .step_now
            .get()
            .map(|i| self.step_facts(i).into_iter().map(|c| c.node).collect())
            .unwrap_or_default();
        let knowing = writer.knowing(&lines);
        let PutExponents {
            cast_to_nat,
            natural_exponent,
            natural_put,
            whole_was,
            int_exponent,
        } = self.put_exponents(rec, [left, right], [was, now], writer, &knowing);
        let whole_letter = |w: &mut Writer, letter: &str| {
            if whole_was {
                w.wholes.insert(
                    letter.to_string(),
                    super::super::expr::System::NonNegative,
                );
            }
        };
        // The motive's letter, of the type the equation's proof states it
        // in, the claim's where the line is widened to it, else the type
        // the term put for has where it stands; and fresh to what it is put
        // into.
        let stated = self
            .line_statement(&part)
            .built()
            .as_ref()
            .and_then(super::super::doc::forms::relation_type)
            .and_then(|t| match t {
                LeanType::Num(n) => Some(n),
                _ => None,
            });
        let ty = match (stated, self.writer.carrier(was)) {
            (Some(n), _) => n,
            (None, Route::Built(n)) => n,
            (None, Route::Declined(d)) => return Route::Declined(d),
        };
        let (ty, equation, in_nat) = match natural_exponent {
            false => (ty, equation, None),
            true => match self.nat_equation(was, now, &equation, &knowing) {
                Route::Built(have) => (
                    super::super::templates::Num::Nat,
                    t::hyp("e_nat"),
                    Some(have),
                ),
                Route::Declined(d) => return Route::Declined(d),
            },
        };
        // What every way out states before its proof: `e_nat`, and `e_w`
        // where the equation is widened (`haves_then`).
        let haves: Vec<Tactic> = in_nat.into_iter().collect();
        let Some(letter) = self.motive_letter(&rec.start) else {
            return Route::no("no fresh letter for a substitution's motive");
        };
        let marked = mark_places(
            &rec.start,
            &rec.put.places,
            &Node::name(was.sort.clone(), letter),
        );
        let mut letters = self.writer.letters.clone();
        letters.insert(letter.to_string(), LetterType::Number(ty));
        let mut inner = self.writer.with_letters(letters);
        whole_letter(&mut inner, letter);
        self.motive_knows(&mut inner, letter, was, now);
        // The motive's letter standing in a slot of whole numbers in a wider
        // type, a range's member, is written as the whole number it is
        // (`Writer::wide_in_slot`), `∃ m : ℤ, (m : ℚ) = t ∧ P m`, where the
        // line Lean writes is so too, the slot's whole numbers. Where the
        // line holds the term as the integer it is, `w ≡ w % p` of a power
        // the step names by its integer, the letter is an integer, as the
        // slot's members are.
        let slot = self.writer.wide_in_slot(&rec.start).map(|(_, whole)| whole);
        let ty = match inner.wide_in_slot(&marked).is_some() && slot.is_none() {
            true => super::super::templates::Num::Int,
            false => ty,
        };
        let closing = match self.put_closing(
            rec,
            [was, now],
            (line, claim),
            cast_to_nat,
            whole_was && natural_put,
        ) {
            Route::Built(closing) => closing,
            Route::Declined(d) => return Route::Declined(d),
        };
        let putting = Putting {
            rec,
            row,
            line,
            claim,
            was,
            now,
            ty,
            equation,
            haves,
            letter,
            marked,
            inner,
            slot,
            int_exponent,
            whole_was,
        };
        match &rec.into {
            SubstitutedInto::Line(_) | SubstitutedInto::RowAbove => {
                self.putting_into_line(putting, &closing)
            }
            SubstitutedInto::ClaimSide(side) if int_exponent => {
                self.putting_into_claim_by_int_exponent(putting, &closing, side)
            }
            SubstitutedInto::ClaimSide(side) => {
                self.putting_into_claim_side(putting, &closing, side)
            }
        }
    }

    /// The putting made into a line, or into the row above: the equation put
    /// into that line by a motive over the places it is put at.
    pub(super) fn putting_into_line(
        &self,
        p: Putting<'_, 'a>,
        k: &PutClosing,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::{LeanType, Proof};
        use super::super::tactics as t;
        use crate::checker::record::SubstitutedInto;
        let Putting {
            rec,
            row,
            line,
            claim,
            was,
            now,
            ty,
            equation,
            mut haves,
            letter,
            marked,
            slot,
            int_exponent,
            whole_was,
            ..
        } = p;
        let close = |term: Printed| k.close(term);
        let close_as = |term: Printed, says: Option<Printed>| k.close_as(term, says);
        let in_arithmetic =
            |path: &Vec<usize>| self.place_in_formula_type(&rec.start, path);
        let whole_letter = |w: &mut Writer, letter: &str| {
            if whole_was {
                w.wholes.insert(
                    letter.to_string(),
                    super::super::expr::System::NonNegative,
                );
            }
        };
        let into = match (&rec.into, row) {
            (SubstitutedInto::Line(at), _) => match self.put_into_line(at) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            },
            (
                _,
                Some(GivenEquation {
                    above: Some(above), ..
                }),
            ) => above.clone(),
            _ => return Route::no("a row's substitution with no row above"),
        };
        // The type the line writes the term put for in. A term of
        // the line's arithmetic, a side or a part of a sum, product or
        // power's base, is written in the line's type, `2^k · 2` in a
        // line of ℚ; any other, a function's argument, in its own,
        // `factorial (4 − 2)` in ℤ, which is the equation's.
        let line_type = match self
            .line_statement(&into)
            .built()
            .as_ref()
            .and_then(super::super::doc::forms::relation_type)
        {
            Some(LeanType::Num(n)) => Some(n),
            _ => None,
        };
        // Each place's type: the line's for one in its arithmetic,
        // its own for any other; places of one type take one motive.
        let types: std::collections::BTreeSet<super::super::templates::Num> = rec
            .put
            .places
            .iter()
            .map(|p| match in_arithmetic(p) {
                true => line_type.unwrap_or(ty),
                false => ty,
            })
            .collect();
        let place_type = match types.into_iter().collect::<Vec<_>>().as_slice() {
            [one] => *one,
            // Places of two types, a function's argument in the
            // equation's own and a term of the line's arithmetic in its
            // wider one: the equation put in twice, at the argument as
            // it is, then widened (`e_w`) at the arithmetic of what
            // that makes.
            [own_type, wide] if *own_type == ty && Some(*wide) == line_type => {
                if int_exponent || slot.is_some() {
                    return Route::no(
                        "a substitution at places written in different types",
                    );
                }
                let wide = *wide;
                let (own, arith): (Vec<Vec<usize>>, Vec<Vec<usize>>) = rec
                    .put
                    .places
                    .iter()
                    .cloned()
                    .partition(|p| !in_arithmetic(p));
                let named = Node::name(was.sort.clone(), letter);
                let stage =
                    |start: &Node,
                     places: &[Vec<usize>],
                     at: super::super::templates::Num| {
                        let mut letters = self.writer.letters.clone();
                        letters.insert(letter.to_string(), LetterType::Number(at));
                        self.writer
                            .with_letters(letters)
                            .formula(&mark_places(start, places, &named))
                            .map(|body| lambda(letter, LeanType::Num(at), body))
                    };
                let first_motive = match stage(&rec.start, &own, ty) {
                    Route::Built(m) => m,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let between = crate::matching::put_at_places(&rec.start, &own, now);
                let second_motive = match stage(&between, &arith, wide) {
                    Route::Built(m) => m,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match self.equation_widened(rec, was, now, ty, wide, &equation) {
                    Route::Built(have) => haves.push(have),
                    Route::Declined(d) => return Route::Declined(d),
                }
                let subst = |motive: Printed, eq: Printed, line: Printed| {
                    applied(
                        "Eq.subst",
                        vec![
                            super::super::doc::Arg::Named {
                                name: "motive".to_string(),
                                value: motive,
                            },
                            super::super::doc::Arg::Explicit(eq),
                            super::super::doc::Arg::Explicit(line),
                        ],
                    )
                };
                let first = subst(first_motive, equation, into.proof);
                let second = subst(second_motive, t::hyp("e_w"), first);
                return Route::Built(haves_then(haves, close(second)));
            }
            _ => {
                return Route::no("a substitution at places written in different types")
            }
        };
        // A line in a narrower type than the equation, `F (j + 1) =
        // G j` of ℤ for an equation of ℝ, is stated in the equation's
        // type first (`widened_to`); in a wider, the equation is
        // stated in the line's type, as `widened` states it.
        let (into, place_type) = match place_type < ty {
            false => (into, place_type),
            true => {
                match self.widened_to(
                    &into.node,
                    &into.proof,
                    place_type,
                    ty,
                    &self.writer,
                ) {
                    Route::Built(w) => {
                        haves.extend(w.have);
                        let widened = super::super::algebra::Cited {
                            proof: w.name,
                            says: None,
                            ..into
                        };
                        (widened, ty)
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
        };
        let equation = match place_type > ty {
            false => equation,
            true => {
                match self.equation_widened(rec, was, now, ty, place_type, &equation) {
                    Route::Built(have) => haves.push(have),
                    Route::Declined(d) => return Route::Declined(d),
                }
                t::hyp("e_w")
            }
        };
        let mut letters = self.writer.letters.clone();
        letters.insert(letter.to_string(), LetterType::Number(place_type));
        let mut inner = self.writer.with_letters(letters);
        whole_letter(&mut inner, letter);
        self.motive_knows(&mut inner, letter, was, now);
        let body = match inner.formula(&marked) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // The claim is the motive at the new value only where the two
        // are written in one form: a line of a real term written as
        // the whole number it is, `∃ m : ℤ, (m : ℝ) = t ∧ …`, is not
        // the claim of an integer, `f k ∈ …`.
        // Nor the line it is put into: the motive at the old value
        // is that line.
        // A range member Lean computes wider, said as the integer that
        // is it (`wide_range_member`), made from a line that the
        // integer the equation puts for is in the range, at that
        // member alone: that integer, the equation and the line.
        if wide_range_member(&self.writer, claim) && rec.put.places == [vec![0]] {
            return Route::Built(haves_then(
                haves,
                Proof::By(Tactic::Exact(range_member_made(equation, into.proof))),
            ));
        }
        let claimed = self.claim_as_stated(line, claim);
        let line_said = self.line_statement(&into).built();
        let in_form = |said: &Option<Printed>| {
            said.as_ref().is_some_and(|c| {
                std::mem::discriminant(&c.kind) == std::mem::discriminant(&body.kind)
            })
        };
        // A line of the whole number a term is, `∃ m : ℤ, (m : ℚ) =
        // 2 ^ p ∧ Even m`, put into, where the claim says it of the
        // whole number the new term is, `Even (3 ^ q.toNat)`: what
        // the motive gives is said of that number,
        // `parley_witness_at`.
        let witnessed = match (slot, in_form(&line_said), in_form(&claimed)) {
            (_, true, true) => None,
            (Some(whole), true, false) => Some(whole),
            // A line of the whole number a term is, `∃ m : ℤ, (m : ℝ)
            // = M ∧ m ∈ X`, put into where the equation puts an
            // integer for M, `M = (f a : ℝ)`, and the claim says it of
            // that integer, `f a ∈ X`: the line's m, which is f a by
            // the cast being one to one.
            (None, true, false) => {
                let same = Printed::applied(
                    "Int.cast_injective",
                    super::super::doc::Source::Mathlib,
                    vec![applied_to(
                        fields(t::hyp("hm"), &["trans"]),
                        equation.clone(),
                    )],
                    LeanType::Prop,
                );
                return Route::Built(haves_then(
                    haves,
                    Proof::By(Tactic::Seq(vec![
                        Tactic::Obtain {
                            names: vec![
                                "m".to_string(),
                                "hm".to_string(),
                                "hk".to_string(),
                            ],
                            says: None,
                            from: into.proof.clone(),
                        },
                        t::call("rw", vec![TacticArg::Rules(vec![t::backwards(same)])]),
                        Tactic::Exact(t::hyp("hk")),
                    ])),
                ));
            }
            _ => {
                return Route::no(
                    "a motive written in another form than the claim or the line",
                )
            }
        };
        let motive = lambda(letter, LeanType::Num(place_type), body.clone());
        let put_in = applied(
            "Eq.subst",
            vec![
                super::super::doc::Arg::Named {
                    name: "motive".to_string(),
                    value: motive,
                },
                super::super::doc::Arg::Explicit(equation),
                super::super::doc::Arg::Explicit(into.proof),
            ],
        );
        if let Some(whole) = witnessed {
            if int_exponent {
                return Route::no(
                    "a substitution into an exponent of a whole number's line",
                );
            }
            let w = match inner.number_fixed(now, whole) {
                Route::Built(w) => w,
                Route::Declined(d) => return Route::Declined(d),
            };
            let lemma = match whole {
                super::super::templates::Num::Nat => "parley_witness_at_nat",
                _ => "parley_witness_at",
            };
            // That the witness is the new term: by its casts, or, a
            // whole number the step names (`named_specs`), by the
            // equation that names it.
            let shows =
                match w.names("Classical.choose") && !self.named_specs.is_empty() {
                    false => t::call("norm_cast", vec![]),
                    true => Tactic::Seq(vec![
                        t::push_cast(None),
                        t::simp_only(
                            false,
                            None,
                            self.named_specs.iter().cloned().map(t::forwards).collect(),
                            None,
                        ),
                    ]),
                };
            let said = Printed {
                kind: super::super::doc::TermKind::App {
                    head: Box::new(t::bridge_lemma(lemma, BridgeModule::PowerTactics)),
                    args: vec![
                        super::super::doc::Arg::Explicit(put_in),
                        super::super::doc::Arg::Explicit(w),
                        super::super::doc::Arg::Explicit(t::by_term(Proof::By(shows))),
                    ],
                    explicit: false,
                },
                ty: Some(LeanType::Prop),
            };
            return Route::Built(haves_then(haves, Proof::By(Tactic::Exact(said))));
        }
        let closed = match int_exponent {
            false => {
                let says = inner
                    .number(now, place_type)
                    .built()
                    .map(|n| super::super::doc::forms::substituted(&body, letter, &n));
                close_as(put_in, says)
            }
            // The motive at the new term, its power an integer one,
            // converted to the claim's natural power, the exponent's
            // fact from the record.
            true => {
                let now_written = match inner.number_fixed(now, place_type) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let given = std::collections::BTreeMap::from([(
                    super::super::names::letter(letter),
                    now_written,
                )]);
                let result = body.substituted(&given);
                let met = claimed.as_ref().map(|c| {
                    self.powers_met(
                        &[claim, &rec.start, was, now],
                        &result,
                        c,
                        &put_in,
                        false,
                    )
                });
                match met {
                    Some(PowersMet::Converted(proof)) => *proof,
                    // Nothing left to convert: closed as any other.
                    Some(PowersMet::Alike) => close(put_in),
                    _ => {
                        return Route::no(
                            "a substitution into an exponent of no term said whole",
                        )
                    }
                }
            }
        };
        Route::Built(haves_then(haves, closed))
    }

    /// The putting made into a side of the claim, in an exponent whose term
    /// put for is not said whole: the motive's letter an integer, its power
    /// an integer one, in the calculation's field, and what `congrArg` gives
    /// converted to the claim's natural powers, each exponent's fact from the
    /// record (`powers_converted_at`).
    pub(super) fn putting_into_claim_by_int_exponent(
        &self,
        p: Putting<'_, 'a>,
        k: &PutClosing,
        side: &usize,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::LeanType;
        use super::super::tactics as t;
        let Putting {
            rec,
            line,
            claim,
            was,
            now,
            ty,
            equation,
            haves,
            letter,
            marked,
            inner,
            whole_was,
            ..
        } = p;
        let close = |term: Printed| k.close(term);
        use super::super::doc::Op;
        use super::super::templates::Num;
        let at = match self.writer.carrier(&rec.start) {
            Route::Built(n) => n.max(ty).max(self.worked_in.get().unwrap_or(Num::Int)),
            Route::Declined(d) => return Route::Declined(d),
        };
        // An integer power is a field's.
        if !whole_was && at < Num::Rat {
            return Route::no("a substitution into an exponent of no term said whole");
        }
        let body = match inner.number(&marked, at) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // Told its type where nothing in it fixes one, numerals and
        // the motive's letter alone, as a calculation's first term is.
        let body = match inner.pinned(&marked) {
            true => body,
            false => Printed::cast(t::bracket(body), inner.num_type(at)),
        };
        let (Route::Built(was_written), Route::Built(now_written)) =
            (inner.number_fixed(was, ty), inner.number_fixed(now, ty))
        else {
            return Route::no("a substitution into an exponent of no term said whole");
        };
        let at_value = |v: Printed| {
            body.substituted(&std::collections::BTreeMap::from([(
                super::super::names::letter(letter),
                v,
            )]))
        };
        let (before, after) = (at_value(was_written), at_value(now_written));
        let motive = lambda(letter, LeanType::Num(ty), body.clone());
        let made = applied(
            "congrArg",
            vec![
                super::super::doc::Arg::Explicit(motive),
                super::super::doc::Arg::Explicit(equation),
            ],
        );
        let (made, result) = match side {
            0 => (
                made,
                Printed::infix(Op::EQUALS, before, after, LeanType::Prop),
            ),
            _ => (
                t::symm(t::bracket(made)),
                Printed::infix(Op::EQUALS, after, before, LeanType::Prop),
            ),
        };
        let met = self.claim_as_stated(line, claim).map(|c| {
            self.powers_met(&[claim, &rec.start, was, now], &result, &c, &made, false)
        });
        match met {
            Some(PowersMet::Converted(proof)) => {
                Route::Built(haves_then(haves, *proof))
            }
            // Nothing left to convert: closed as any other.
            Some(PowersMet::Alike) => Route::Built(haves_then(haves, close(made))),
            _ => Route::no("a substitution into an exponent of no term said whole"),
        }
    }

    /// The putting made into a side of the claim, the equation put there by
    /// `congrArg` over the places it is put at.
    pub(super) fn putting_into_claim_side(
        &self,
        p: Putting<'_, 'a>,
        k: &PutClosing,
        side: &usize,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::LeanType;
        use super::super::tactics as t;
        let Putting {
            rec,
            was,
            now,
            ty,
            equation,
            mut haves,
            letter,
            marked,
            whole_was,
            ..
        } = p;
        let close_as = |term: Printed, says: Option<Printed>| k.close_as(term, says);
        let in_arithmetic =
            |path: &Vec<usize>| self.place_in_formula_type(&rec.start, path);
        let whole_letter = |w: &mut Writer, letter: &str| {
            if whole_was {
                w.wholes.insert(
                    letter.to_string(),
                    super::super::expr::System::NonNegative,
                );
            }
        };
        // Written in the wider of the claim side's type and the
        // equation's. An equation in a narrower type put only at
        // places of the side's arithmetic is stated in the wider
        // first, as `widened` states it, and the motive's letter is of
        // the wider: cast inside the motive, it would be pushed onto
        // each division, which `push_cast` spells as `Rat.divInt` on
        // one side and not the other. At a place written in its own
        // type, an index or an exponent, the letter keeps the
        // equation's, and an equation of rationals is not put into a
        // wider field so.
        let at = match self.writer.carrier(&rec.start) {
            Route::Built(n) => n.max(ty),
            Route::Declined(d) => return Route::Declined(d),
        };
        let arithmetic = rec.put.places.iter().all(in_arithmetic);
        if !arithmetic && ty == super::super::templates::Num::Rat && at > ty {
            return Route::no("an equation of rationals put into a wider field");
        }
        let letter_ty = match arithmetic {
            true => at,
            false => ty,
        };
        let equation = match at > ty && arithmetic {
            false => equation,
            true => {
                match self.equation_widened(rec, was, now, ty, at, &equation) {
                    Route::Built(have) => haves.push(have),
                    Route::Declined(d) => return Route::Declined(d),
                }
                t::hyp("e_w")
            }
        };
        let mut letters = self.writer.letters.clone();
        letters.insert(letter.to_string(), LetterType::Number(letter_ty));
        let mut wide = self.writer.with_letters(letters);
        whole_letter(&mut wide, letter);
        self.motive_knows(&mut wide, letter, was, now);
        let body = match wide.number(&marked, at) {
            Route::Built(b) => b,
            Route::Declined(d) => return Route::Declined(d),
        };
        // What `congrArg` makes: the body at each term, the side the
        // equation is put into first.
        let at = |n: &Node| {
            wide.number(n, letter_ty)
                .built()
                .map(|v| super::super::doc::forms::substituted(&body, letter, &v))
        };
        let says = match (at(was), at(now)) {
            (Some(a), Some(b)) => {
                let (l, r) = match side {
                    0 => (a, b),
                    _ => (b, a),
                };
                Some(Printed::infix(
                    super::super::doc::Op::EQUALS,
                    l,
                    r,
                    LeanType::Prop,
                ))
            }
            _ => None,
        };
        let motive = lambda(letter, LeanType::Num(letter_ty), body);
        let made = applied(
            "congrArg",
            vec![
                super::super::doc::Arg::Explicit(motive),
                super::super::doc::Arg::Explicit(equation),
            ],
        );
        let closed = close_as(
            match side {
                0 => made,
                _ => t::symm(t::bracket(made)),
            },
            says,
        );
        Route::Built(haves_then(haves, closed))
    }

    /// The motive's writer `w` told what the lines say of both terms its
    /// letter stands for, `was` and `now`, so that the motive writes the
    /// letter as they are written: finite where the set put for is, so a
    /// count of it is `t.ncard`; at least the lesser of their bounds, √a =
    /// √b of a, b ≥ 0 written with Lean's real root.
    pub(super) fn motive_knows(
        &self,
        w: &mut Writer,
        letter: &str,
        was: &Node,
        now: &Node,
    ) {
        let grammar = self.writer.grammar;
        if let Some(why) =
            crate::citing::finite::finite_by(grammar, &self.writer.finite, was)
        {
            w.finite.insert(letter.to_string(), why);
        }
        if let (Some(a), Some(b)) = (self.writer.least(was), self.writer.least(now)) {
            w.bounds.terms.push(crate::citing::bounds::Bound {
                term: Node::name(was.sort.clone(), letter),
                least: a.min(b),
                said_by: None,
            });
        }
    }

    /// A letter for a substitution's motive, fresh to `start`, what the
    /// equation is put into, and to the letters in scope.
    pub(super) fn motive_letter(&self, start: &Node) -> Option<&'static str> {
        let taken = start.names();
        ["t", "u", "w", "s", "r", "v", "q", "z"]
            .into_iter()
            .find(|l| {
                !taken.iter().any(|n| n == l) && !self.writer.letters.contains_key(*l)
            })
    }

    /// The type of the term a substitution puts for, where it is no number:
    /// a set, by what it holds, or a member of one, a group's element among
    /// them. None for a number, and for a term the writer has no type for.
    pub(super) fn member_letter(&self, was: &Node) -> Option<LetterType> {
        if self.writer.is_number(was) {
            return None;
        }
        self.writer
            .set_members(was)
            .map(LetterType::Set)
            .or_else(|| {
                self.writer
                    .member_kind(was)
                    .filter(|m| !matches!(m, super::super::expr::Members::Numbers(_)))
                    .map(LetterType::Member)
            })
    }

    /// `substituted_by_record` of a term that is no number, `was`, of the
    /// type `letter_ty`: the motive over the places the record names, its
    /// letter of that type. Into a line or the row above, `Eq.subst` of the
    /// equation along it; into a side of the claim, `congrArg` of the
    /// motive, turned for the right side. What it makes meets the claim as
    /// written, respelled, or with a listed set's members in another order;
    /// turned round is `substituted_by_record`'s; a letter renamed or an
    /// identity element dropped declines.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn substituted_members(
        &self,
        rec: &crate::checker::record::Substituted,
        letter_ty: LetterType,
        put: PutTerms,
        equation: Printed,
        row: Option<&GivenEquation>,
        line: usize,
        claim: &Node,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::{Arg, Proof};
        use super::super::tactics as t;
        use crate::checker::record::SubstitutedInto;
        let PutTerms { was, now } = put;
        let m = &rec.meeting;
        if m.renamed || !m.identities.is_empty() {
            return Route::no("a putting that meets the claim other than as written");
        }
        let Some(letter) = self.motive_letter(&rec.start) else {
            return Route::no("no fresh letter for a substitution's motive");
        };
        let marked = mark_places(
            &rec.start,
            &rec.put.places,
            &Node::name(was.sort.clone(), letter),
        );
        let mut letters = self.writer.letters.clone();
        letters.insert(letter.to_string(), letter_ty.clone());
        let mut inner = self.writer.with_letters(letters);
        self.motive_knows(&mut inner, letter, was, now);
        let made = match &rec.into {
            SubstitutedInto::Line(_) | SubstitutedInto::RowAbove => {
                let into = match (&rec.into, row) {
                    (SubstitutedInto::Line(at), _) => match self.put_into_line(at) {
                        Route::Built(p) => p.proof,
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    (
                        _,
                        Some(GivenEquation {
                            above: Some(above), ..
                        }),
                    ) => above.proof.clone(),
                    _ => return Route::no("a row's substitution with no row above"),
                };
                let body = match inner.formula(&marked) {
                    Route::Built(b) => b,
                    Route::Declined(d) => return Route::Declined(d),
                };
                applied(
                    "Eq.subst",
                    vec![
                        Arg::Named {
                            name: "motive".to_string(),
                            value: lambda(letter, letter_ty.lean_type(), body),
                        },
                        Arg::Explicit(equation),
                        Arg::Explicit(into),
                    ],
                )
            }
            // A side that is a number is written as the number it is; a count
            // in ℕ∞, |V|, as Lean counts it (`count_term`), then met with
            // the claim's counts (`counted_between`); any other as the set or
            // member.
            SubstitutedInto::ClaimSide(side) => {
                let counted = self.writer.counts(&rec.start);
                let body = match (self.writer.is_number(&rec.start), counted) {
                    (true, _) => match self.writer.carrier(&rec.start) {
                        Route::Built(at) => inner.number(&marked, at),
                        Route::Declined(d) => Route::Declined(d),
                    },
                    (false, true) => inner.count_term(&marked),
                    (false, false) => inner.set_term(&marked),
                };
                let body = match body {
                    Route::Built(b) => b,
                    Route::Declined(d) => return Route::Declined(d),
                };
                let motive = lambda(letter, letter_ty.lean_type(), body.clone());
                let made = applied(
                    "congrArg",
                    vec![Arg::Explicit(motive), Arg::Explicit(equation)],
                );
                let made = match side {
                    0 => made,
                    _ => t::symm(t::bracket(made)),
                };
                if !counted {
                    made
                } else {
                    // What `congrArg` makes: the motive's body at each term,
                    // `V.encard = {c, d}.encard`, met with the claim's counts.
                    let (Route::Built(at_was), Route::Built(at_now)) =
                        (self.writer.set_term(was), self.writer.set_term(now))
                    else {
                        return Route::no("a set Lean writes no way of");
                    };
                    let forms = super::super::doc::forms::substituted;
                    let (l, r) =
                        (forms(&body, letter, &at_was), forms(&body, letter, &at_now));
                    let (l, r) = match side {
                        0 => (l, r),
                        _ => (r, l),
                    };
                    let says = Printed::infix(
                        super::super::doc::Op::EQUALS,
                        l,
                        r,
                        super::super::doc::LeanType::Prop,
                    );
                    let Some(wanted) = self.claim_as_stated(line, claim) else {
                        return Route::no("a claim Lean states no form of");
                    };
                    let put_in = crate::matching::put_at_places(
                        &rec.start,
                        &rec.put.places,
                        now,
                    );
                    match self.counted_between(
                        &made,
                        &says,
                        &wanted,
                        &[&rec.start, &put_in],
                    ) {
                        Some(p) => p,
                        None => made,
                    }
                }
            }
        };
        // A listed set the putting leaves in another order than the claim's
        // (`Meeting::permuted`): taken in the claim's order (`reordered`).
        match m.permuted {
            false => Route::Built(Proof::Term(made)),
            true => Route::Built(Proof::By(reordered(
                &made,
                rec.start.notation() == crate::notations::EQUALITY,
            ))),
        }
    }

    pub(super) fn substitute(
        &self,
        just: &Justification,
        k: usize,
        claim: &Node,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        use super::super::doc::Proof;
        use super::super::tactics as t;
        // As the checker recorded it, where it did; an equation from no line
        // by its own proof (`equation_given`).
        let given = self.equation_given(just);
        let by_record = self.substituted_by_record(
            just.line,
            Some(k),
            claim,
            given.as_ref().map(|(_, g)| g),
            writer,
        );
        if let Route::Built(proof) = by_record {
            return Route::Built(match given.and_then(|(have, _)| have) {
                Some(have) => haves_then(vec![have], proof),
                None => proof,
            });
        }
        if !just.rows.is_empty() {
            return self.substitute_rows(just, writer);
        }
        // Substituting from a function the header lets by its value: its
        // equation for every x, put in where f is applied.
        if let Some(crate::corpus::skeleton::Source::At(place)) = &just.source {
            if let Some(hyp) = self.header_function_named(place.named()) {
                let everywhere =
                    TacticArg::At(vec![super::super::doc::Location::Everywhere]);
                return Route::Built(Proof::By(Tactic::Seq(vec![
                    t::simp_only(
                        false,
                        None,
                        vec![t::forwards(t::hyp(&hyp))],
                        Some(everywhere),
                    ),
                    t::call("done", vec![]),
                ])));
            }
        }
        let mut haves = Vec::new();
        // The equation put in, as a tree.
        let mut put: Option<Node> = None;
        let equation = match (&just.source, &just.equation) {
            (Some(crate::corpus::skeleton::Source::At(place)), written) => {
                // Of a line saying several things, the equation the step
                // writes, as Lean writes both; else the one that turns the
                // claim's left side into its right, as a calculation's row
                // "= 0² + 0²  substitute D1" puts B = 0 of "A = 0 and B = 0";
                // else its first equation.
                let wanted = written
                    .as_ref()
                    .and_then(|w| self.tree(w).built())
                    .and_then(|n| self.writer.formula(&n).built())
                    .map(|p| p.untyped());
                let parts = self.cited_parts(&[place.named().to_string()]);
                let grammar = &self.sources.checked.grammar;
                // Where the checker recorded the substitution, the
                // equation is the part of the line it found
                // (`Substituted::from`).
                let recorded = self
                    .rec
                    .substituted
                    .get(&just.line)
                    .and_then(|r| r.from.as_ref())
                    .and_then(|at| self.line_part(at).built());
                let chosen = recorded
                    .as_ref()
                    .or_else(|| {
                        parts
                            .iter()
                            .find(|c| {
                                wanted.is_some()
                                    && self
                                        .line_statement(c)
                                        .built()
                                        .map(|p| p.untyped())
                                        == wanted
                            })
                            .or_else(|| {
                                (claim.notation() == crate::notations::EQUALITY)
                                    .then(|| {
                                        parts.iter().find(|c| {
                                            c.node.notation()
                                                == crate::notations::EQUALITY
                                                && makes_claim(&c.node, claim, grammar)
                                        })
                                    })
                                    .flatten()
                            })
                            .or_else(|| {
                                parts.iter().find(|c| {
                                    c.node.notation() == crate::notations::EQUALITY
                                })
                            })
                            .or(parts.first())
                    })
                    .map(|c| (c.node.clone(), c.proof.clone()));
                // Put into a line Lean's types give, `⌊A⌋ ∈ ℤ`, the claim is
                // a membership the equation shows.
                if let Some((line, name)) = &chosen {
                    if let Some(proof) = member_by_equation(
                        &self.writer,
                        line,
                        name,
                        claim,
                        self.sources.ctx,
                    ) {
                        return Route::Built(proof);
                    }
                }
                match chosen.as_ref().map(|(n, p)| (n, p)) {
                    Some((line, name)) => match self.widened(line, name, claim, writer)
                    {
                        Route::Built(w) => {
                            haves.extend(w.have);
                            put = Some(line.clone());
                            w.name
                        }
                        Route::Declined(d) => return Route::Declined(d),
                    },
                    None => {
                        return Route::no(format!(
                            "substitute from {}, which has no Lean name",
                            place.named()
                        ))
                    }
                }
            }
            (_, Some(written)) => {
                let node = match self.tree(written) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                // An equation shown by real arithmetic where it is put, ln(8)
                // = 3·ln(2) (real arithmetic), is the real arithmetic's.
                if !matches!(
                    just.source,
                    Some(crate::corpus::skeleton::Source::RealArithmetic)
                ) {
                    return Route::no("an equation put in that no line states");
                }
                // Of numerals alone, cos(0) = 1, it is said in the type the
                // claim is computed in, where it is put: `Complex.cos 0` in
                // a line of complex numbers.
                let at = claim
                    .children
                    .iter()
                    .filter_map(|c| self.writer.carrier(c).built())
                    .fold(super::super::templates::Num::Int, |a, b| a.max(b));
                // Of no letter of the proof's, cos(0) = 1, whose names are
                // the library's functions only.
                let lettered = node
                    .names()
                    .iter()
                    .any(|n| self.writer.letters.contains_key(n.as_str()));
                let said = match !lettered {
                    true => self.writer.closed_formula(&node, at),
                    false => self.writer.formula(&node),
                };
                // Real arithmetic is written in ℝ; an equation it works out
                // in ℂ is left.
                if at > super::super::templates::Num::Real {
                    return Route::no("real arithmetic of an equation in ℂ");
                }
                let proof = match super::super::reals::real_arithmetic(
                    &self.writer,
                    self.sources.targets,
                    &node,
                ) {
                    Route::Built(p) => p,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match said {
                    Route::Built(p) => t::bracket(shown(p, proof)),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::no("a substitution with no equation to put in"),
        };
        // The line put into, cast up to the claim's type where it is
        // narrower. Of a line saying several things, the one the equation
        // turns into the claim; else the one that says what the claim does,
        // divides where the claim divides; else the first.
        let grammar = &self.sources.checked.grammar;
        let turns = |part: &Node| -> bool {
            let Some([left, right]) = put.as_ref().map(|e| e.children.as_slice())
            else {
                return false;
            };
            let want = grammar.print(claim);
            [(left, right), (right, left)].iter().any(|(from, to)| {
                grammar.print(&put_term(part, from, to, grammar)) == want
            })
        };
        // Where no part turns into the claim with the equation put for every
        // place, the equation is put for some places only, gcd(a, b) ∣ b
        // from b ∣ b, and each part that says what the claim does is offered.
        // A "for all" of the line is judged by what it says at the block's
        // letter, p(x) = (x − a)·q(x) + p(a) of "… for all x ∈ ℂ" at x, and
        // put into by its own name, which the tactic rewrites under the
        // quantifier.
        let at_claim = |node: &Node| -> Node {
            // Only what the line says at the claim's letter is wanted, so
            // its proof is left out.
            let cited = super::super::algebra::Cited {
                node: node.clone(),
                proof: Printed::of(
                    super::super::doc::TermKind::Elided,
                    super::super::doc::LeanType::Prop,
                ),
                says: None,
            };
            self.at_recorded_letter(&cited, &claim.names())
                .map_or_else(|| node.clone(), |at| at.node)
        };
        // Where the checker recorded the substitution into a line, the part
        // of the line it found (`Substituted::into`).
        let recorded_into = self.rec.substituted.get(&just.line).and_then(|r| match &r
            .into
        {
            crate::checker::record::SubstitutedInto::Line(at) => {
                self.line_part(at).built()
            }
            _ => None,
        });
        let unrecorded = || {
            just.into
                .as_ref()
                .and_then(|place| self.trees.get(place.named()))
                .map(|t| {
                    let t: Vec<(&Node, &Printed)> =
                        t.iter().map(|s| (&s.node, &s.proof)).collect();
                    let turned: Vec<_> = t
                        .iter()
                        .copied()
                        .filter(|(n, _)| turns(&at_claim(n)))
                        .take(1)
                        .collect();
                    if !turned.is_empty() {
                        return turned;
                    }
                    let alike: Vec<_> = t
                        .iter()
                        .copied()
                        .filter(|(n, _)| at_claim(n).notation() == claim.notation())
                        .collect();
                    if !alike.is_empty() {
                        return alike;
                    }
                    t.into_iter().take(1).collect()
                })
                .unwrap_or_default()
        };
        let candidates: Vec<(&Node, &Printed)> = match &recorded_into {
            Some(part) => vec![(&part.node, &part.proof)],
            None => unrecorded(),
        };
        let mut into = Vec::new();
        // A line put into that says something of the whole number a term
        // is, `∃ m : ℤ, (m : ℚ) = 2 ^ (p − 1) * 2 ∧ 2 ^ p − 1 ∣ m`, whose
        // term the equation turns into the claim's whole number, 2^p: the
        // line said of that number, the equation showing it is the term.
        let mut witnessed: Vec<Tactic> = Vec::new();
        for (line, name) in &candidates {
            let Some((term, whole)) = self.writer.wide_in_slot(line) else {
                continue;
            };
            let Some(at) = path_to(line, &term).and_then(|p| at_path(claim, &p)) else {
                continue;
            };
            let Route::Built(w) = self.writer.number_fixed(at, whole) else {
                continue;
            };
            let lemma = match whole {
                super::super::templates::Num::Nat => "parley_witness_at_nat",
                _ => "parley_witness_at",
            };
            // The named number is its term by its own equation, which the
            // step names beside the one it puts in (`named_specs`), where
            // the witness is a named number.
            let specs: Vec<super::super::doc::Rule> = match chosen_witnesses(&w)
                .is_empty()
            {
                true => Vec::new(),
                false => self.named_specs.iter().cloned().map(t::forwards).collect(),
            };
            for by in [equation.clone(), negated(equation.clone())] {
                let mut steps = vec![t::push_cast(None)];
                if !specs.is_empty() {
                    steps.push(t::simp_only(false, None, specs.clone(), None));
                }
                steps.push(t::linear_combination(by));
                let shows = Proof::By(Tactic::Seq(steps));
                let applied = Printed {
                    kind: super::super::doc::TermKind::App {
                        head: Box::new(t::bridge_lemma(
                            lemma,
                            BridgeModule::PowerTactics,
                        )),
                        args: [
                            (*name).clone(),
                            t::bracket(w.clone()),
                            super::super::tactics::by_term(shows),
                        ]
                        .into_iter()
                        .map(super::super::doc::Arg::Explicit)
                        .collect(),
                        explicit: false,
                    },
                    ty: Some(super::super::doc::LeanType::Prop),
                };
                witnessed.push(Tactic::Exact(applied));
            }
        }
        for (i, (line, name)) in candidates.into_iter().enumerate() {
            // A "for all" line read at the block's letter, the part of it
            // the equation turns into the claim: line 2's "e(n) ≠ D(f(n),
            // n)" at the block's n, the equation being of that n, which no
            // rewriting under the line's own binder reaches.
            let read = self.at_recorded_letter(
                &super::super::algebra::Cited {
                    node: line.clone(),
                    proof: name.clone(),
                    says: None,
                },
                &claim.names(),
            );
            let mut parts = Vec::new();
            let read = read.filter(|_| line.notation() == crate::notations::FOR_ALL);
            if let Some(at) = &read {
                conjuncts(
                    &at.node,
                    at.proof.clone(),
                    at.says.clone(),
                    &mut parts,
                    &self.writer,
                );
            }
            // Of no part the equation turns into the claim, the whole line at
            // the letter, as a "for all" line cited inside a block is read:
            // 5.7's a·f(a) ≡ 1 at the block's a, which f(a) = 1 then turns
            // into a·1 ≡ 1, the claim a ≡ 1 with its 1 written.
            let whole = read.filter(|_| !parts.iter().any(|p| turns(&p.node)));
            if let Some(part) = parts.iter().find(|p| turns(&p.node)).or(whole.as_ref())
            {
                let at_name = format!("at{i}");
                haves.push(Tactic::Name {
                    name: at_name.clone(),
                    term: part.proof.clone(),
                });
                match self.widened(&part.node, &t::hyp(&at_name), claim, writer) {
                    Route::Built(w) => {
                        haves.extend(w.have);
                        into.push(w.name);
                    }
                    Route::Declined(d) => return Route::Declined(d),
                }
                continue;
            }
            match self.widened(line, name, claim, writer) {
                Route::Built(w) => {
                    haves.extend(w.have);
                    into.push(w.name);
                }
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let mut ways: Vec<Tactic> = Vec::new();
        // A range member Lean computes wider is said as the integer that is
        // it (`wide_range_member`): an equation ↑(f k) = v put into f k ∈
        // {0, …, n − 1} is that integer, its equation and the line.
        if wide_range_member(&self.writer, claim) {
            for line in &into {
                ways.push(Tactic::Exact(range_member_made(
                    equation.clone(),
                    line.clone(),
                )));
            }
        }
        ways.extend(witnessed);
        if ways.is_empty() {
            return Route::no("a substitution the record gives no way of");
        }
        ways_proof(ListReason::Substituted, ways).map(|p| haves_then(haves, p))
    }

    /// A cited "for all" of one letter written at the block's letter the
    /// check read it at (`CheckedTheorem::read_at`): its body with the
    /// letter put in, proved by the line applied to it, `hH2 y`. None where
    /// the line says no such "for all", the check read it at no letter, or
    /// that letter is not among `names`, the letters the claim writes.
    pub(super) fn at_recorded_letter(
        &self,
        cited: &super::super::algebra::Cited,
        names: &std::collections::BTreeSet<String>,
    ) -> Option<super::super::algebra::Cited> {
        let [letter, set, body] = cited.node.children.as_slice() else {
            return None;
        };
        if cited.node.notation() != crate::notations::FOR_ALL || !letter.is_name() {
            return None;
        }
        // A guarded "for all", over ℕ or ℕ₀, asks a proof besides the
        // letter, that it is above 0 or at least 0; one over any other set,
        // ℝ ∖ {5} or B, that the letter is in it.
        let (ty, guarded) = match super::super::expr::system_of(set) {
            Some(system) => (
                LetterType::Number(super::super::expr::letter_type(system)),
                !matches!(system, super::super::expr::System::Type(_)),
            ),
            None => (self.writer.set_members(set)?.letter(), true),
        };
        // The block's letter the check read the line at (`read_at`), where
        // the claim names it.
        let ctx = self.sources.ctx;
        let standard = |n: &Node| crate::matching::standard(n, ctx);
        let said = standard(&cited.node);
        let i = self.step_now.get()?;
        let read_at = self
            .rec
            .read_at
            .get(i)?
            .iter()
            .find(|r| crate::matching::alike_top(&standard(&r.said), &said, ctx))?;
        let at = read_at.letter.text.to_string();
        if !names.contains(&at) || self.writer.letters.get(at.as_str()) != Some(&ty) {
            return None;
        }
        let at = &at;
        let put = crate::matching::Binding::from([(
            letter.text,
            Node::name(letter.sort.clone(), at),
        )]);
        let read = crate::matching::substitute_apart_by(
            body,
            &put,
            &self.sources.checked.grammar.binders(),
        );
        // The guard is the `let` line that puts the letter in the set
        // (`ReadAt::opened_by`), `hK7`; None where Lean names no such line.
        let mut args =
            vec![super::super::tactics::hyp(&super::super::names::letter(at))];
        if guarded {
            args.push(self.line_part(&read_at.opened_by).built()?.proof);
        }
        let at_letter = args.into_iter().fold(cited.proof.clone(), applied_to);
        Some(super::super::algebra::Cited {
            node: read,
            proof: super::super::tactics::bracket(at_letter),
            says: None,
        })
    }

    /// A `membership` claim `t ∈ S` the checker found shown by a cited
    /// equation putting t beside a term in S (`members_shown`,
    /// `ShownBy::Beside`), where Lean writes t in a wider type than S's:
    /// that other side as S's witness, and the equation faced so the
    /// witness is its left side, by `exact_mod_cast`. None where the record
    /// has no such equation, or Lean writes t in S's type already.
    pub(super) fn member_from_record(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Option<super::super::doc::Proof> {
        use crate::checker::record::ShownBy;
        let ShownBy::Beside(beside) = &self.rec.members_shown.get(&just.line)?.by
        else {
            return None;
        };
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        let super::super::expr::System::Type(n) = super::super::expr::system_of(set)?
        else {
            return None;
        };
        if writer.carrier(term).built()? <= n {
            return None;
        }
        // The other side's membership a line states, `∃ m, ↑m = k(k + 1)/2`:
        // its witness carried along the equation faced so the other side is
        // its left, `s3.imp (fun _ h => h.trans s2.symm)`.
        if let Some(stated) = &beside.other_stated {
            let ctx = self.sources.ctx;
            let cited = self.cited_parts(&just.refs);
            let line = cited.iter().find(|c| read_alike(&c.node, stated, ctx))?;
            let equation = cited
                .iter()
                .find(|c| read_alike(&c.node, &beside.equation, ctx))?;
            let to_term = match beside.facing {
                Facing::Turned => equation.proof.clone(),
                Facing::Straight => super::super::tactics::symm(
                    super::super::tactics::bracket(equation.proof.clone()),
                ),
            };
            let carried = Printed::of(
                super::super::doc::TermKind::Lambda {
                    letters: vec!["_".to_string(), "h".to_string()],
                    body: Box::new(applied_to(
                        fields(super::super::tactics::hyp("h"), &["trans"]),
                        to_term,
                    )),
                },
                super::super::doc::LeanType::Prop,
            );
            return Some(super::super::doc::Proof::Term(applied_to(
                fields(line.proof.clone(), &["imp"]),
                carried,
            )));
        }
        let other = &beside.other;
        if !writer.carrier(other).built().is_some_and(|c| c <= n) {
            return None;
        }
        let w = writer.number_fixed(other, n).built()?;
        let equation = self
            .cited_parts(&just.refs)
            .into_iter()
            .find(|c| read_alike(&c.node, &beside.equation, self.sources.ctx))?;
        // The witness is the side that is not the term: the equation as it
        // stands where the term is its right side, turned where its left.
        let faced = match beside.facing {
            Facing::Turned => equation.proof,
            Facing::Straight => super::super::tactics::symm(
                super::super::tactics::bracket(equation.proof),
            ),
        };
        let proof = super::super::tactics::by_term(super::super::doc::Proof::By(
            super::super::tactics::exact_mod_cast(faced),
        ));
        Some(super::super::doc::Proof::Term(
            super::super::expr::anonymous(vec![w, proof]),
        ))
    }

    /// A `membership` claim `t ∈ ℕ₀` or `t ∈ ℕ` of a t Lean writes in ℤ,
    /// which Lean states as its bound, `0 ≤ t` or `0 < t`, as the checker
    /// found it shown (`members_shown`): beside a cited equation, t = u,
    /// the equation put in and u's bound, from the line stating u is in
    /// the system or by the said-once walk, `by rw [s1_6]; exact hIH.2`;
    /// otherwise t's own bound by the walk (`said_bound`). None where the
    /// record has none, or no proof is written for the bound.
    pub(super) fn member_bound(
        &self,
        just: &Justification,
        node: &Node,
    ) -> Option<Printed> {
        use super::super::tactics as t;
        use crate::checker::record::ShownBy;
        use crate::rules::System;
        let [term, set] = node.children.as_slice() else {
            return None;
        };
        if set.notation() != crate::notations::NUMBER_SYSTEMS {
            return None;
        }
        let system = System::of_sign(&set.text)
            .filter(|s| matches!(s, System::N0 | System::N))?;
        // The record keeps a membership shown beside an equation; any other
        // is shown by what the page says once (`ShownBy::Said`).
        let by = self.rec.members_shown.get(&just.line).map(|s| &s.by);
        match by.unwrap_or(&ShownBy::Said) {
            ShownBy::Said => self.said_bound(term, system, &just.refs),
            ShownBy::Beside(beside) => {
                let cited = self.cited_parts(&just.refs);
                let ctx = self.sources.ctx;
                let equation = cited
                    .iter()
                    .find(|c| read_alike(&c.node, &beside.equation, ctx))?;
                // The other side by the line stating it, the closure table's
                // row (`Besides::other_row`), or what the page says once.
                let other = match (&beside.other_stated, &beside.other_row) {
                    (Some(stated), _) => cited
                        .iter()
                        .find(|c| read_alike(&c.node, stated, ctx))?
                        .proof
                        .clone(),
                    (None, Some(row)) => whole_nonneg(&row.op, || {
                        self.said_bound(&row.right, System::N, &just.refs)
                    })?,
                    (None, None) => {
                        self.said_bound(&beside.other, system, &just.refs)?
                    }
                };
                // The equation faced u = t, and u's bound carried along it.
                let to_term = match beside.facing {
                    Facing::Straight => t::symm(t::bracket(equation.proof.clone())),
                    Facing::Turned => equation.proof.clone(),
                };
                let lemma = match system {
                    System::N => "lt_of_lt_of_eq",
                    _ => "le_of_le_of_eq",
                };
                Some(Printed::applied(
                    lemma,
                    super::super::doc::Source::Mathlib,
                    vec![t::bracket(other), to_term],
                    super::super::doc::LeanType::Prop,
                ))
            }
            // The type `Set.MapsTo f X Y` applied to the point's membership
            // of X, which a set-builder or `Set.univ` holds as its bound.
            ShownBy::Typed { map, at } => {
                let ctx = self.sources.ctx;
                let typed = self
                    .cited_parts(&just.refs)
                    .into_iter()
                    .find(|c| read_alike(&c.node, map, ctx))?;
                let [_, domain, _] = map.children.as_slice() else {
                    return None;
                };
                if domain.notation() != crate::notations::NUMBER_SYSTEMS {
                    return None;
                }
                let point = match System::of_sign(&domain.text)? {
                    s @ (System::N0 | System::N) => {
                        self.said_bound(at, s, &just.refs)?
                    }
                    _ => Printed::applied(
                        "Set.mem_univ",
                        super::super::doc::Source::Mathlib,
                        vec![Printed::of(
                            super::super::doc::TermKind::Elided,
                            super::super::doc::LeanType::Prop,
                        )],
                        super::super::doc::LeanType::Prop,
                    ),
                };
                Some(applied_to(typed.proof, point))
            }
            // The define put in, `rw [hD1]`, and the value's own bound.
            ShownBy::Define { value } => {
                let define = just
                    .refs
                    .iter()
                    .filter(|r| self.thm.defines.iter().any(|d| d.label == **r))
                    .find_map(|r| self.named.get(r).and_then(|n| n.first()))?;
                let bound = self.said_bound(value, system, &just.refs)?;
                Some(t::by_term(super::super::doc::Proof::By(Tactic::Seq(vec![
                    t::call(
                        "rw",
                        vec![TacticArg::Rules(vec![t::forwards(t::hyp(define))])],
                    ),
                    Tactic::Exact(bound),
                ]))))
            }
        }
    }

    /// `membership`. A term of a wider type said to be in a number system,
    /// an integer or a real, is one by a cited equation (`member_by_equation`).
    /// Any other membership is what the lines and the letters' types give.
    pub(super) fn membership(
        &self,
        just: &Justification,
        node: &Node,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        // What Lean proves as it stands: `True` of a membership its types
        // give, x ∈ ℝ of a real x; a fact of numerals alone.
        if let Some(p) = writer.formula(node).built().as_ref().and_then(lean_truth) {
            return Route::Built(super::super::doc::Proof::Term(p));
        }
        if let Some(proof) = self.member_from_record(just, node, writer) {
            return Route::Built(proof);
        }
        match self.member_bound(just, node) {
            Some(proof) => Route::Built(super::super::doc::Proof::Term(proof)),
            None => Route::no("a membership the record shows no way to"),
        }
    }

    /// `substitute` in rows: each row the row above with the change its
    /// reason proves put in, the first row the line it cites, and the last
    /// the claim.
    pub(super) fn substitute_rows(
        &self,
        just: &Justification,
        writer: &Writer,
    ) -> Route<super::super::doc::Proof> {
        let Some(Ok(rows)) =
            crate::corpus::proof::substitute_rows(just, &self.thm.path)
        else {
            return Route::no("substitute rows that do not cut");
        };
        let Some(first) = rows.first() else {
            return Route::no("substitute rows with no row");
        };
        let Some(mut above) = self
            .named
            .get(first.cite.trim())
            .and_then(|n| n.first())
            .cloned()
        else {
            return Route::no(format!(
                "a first row citing {}, which has no Lean name",
                first.cite
            ));
        };
        // The row above as Lean has it, its name and statement: the cited
        // line's one sentence, then each row as it is written.
        let mut above_cited: Option<super::super::algebra::Cited> =
            match self.trees.get(first.cite.trim()).map(Vec::as_slice) {
                Some([one]) => Some(one.cited()),
                _ => None,
            };
        let mut haves = Vec::new();
        for (k, row) in rows.iter().enumerate().skip(1) {
            let row_node = match self.tree(&row.formula) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let row_says = match writer.formula(&row_node) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let Some(reason) = &row.reason else {
                return Route::no("a row after the first with no reason");
            };
            let Ok(by) = &reason.by else {
                return Route::no("a row whose reason does not read");
            };
            let change = match self.tree(&reason.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_says = match writer.formula(&change) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            // The change is stated by the `have` below, its counts in the
            // form it writes them (`row_stated`), as a calculation's row is.
            *self.row_stated.borrow_mut() = Some(change_says.clone());
            let proof = self.proof_of(
                Reason {
                    just: by,
                    cited: self.rec.cited_requires.get(&reason.line),
                },
                0,
                &change,
            );
            *self.row_stated.borrow_mut() = None;
            let proof = match proof {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            let change_name = format!("c{k}");
            haves.push(Tactic::Have {
                name: change_name.clone(),
                says: change_says.clone(),
                proof: Box::new(proof),
            });
            let change_h = super::super::tactics::hyp(&change_name);
            let row_name = format!("row{k}");
            // The change put into the row above at the places the checker
            // recorded (`SubstitutedInto::RowAbove`), as a line's equation
            // is put into a line.
            let Some(above_line) = above_cited.clone() else {
                return Route::no("a row put into a row above of several sentences");
            };
            let put = GivenEquation {
                change: super::super::algebra::Cited {
                    node: change.clone(),
                    proof: change_h.clone(),
                    says: Some(change_says.clone()),
                },
                above: Some(above_line),
            };
            let proof = match self.substituted_by_record(
                reason.line,
                None,
                &row_node,
                Some(&put),
                writer,
            ) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            haves.push(Tactic::Have {
                name: row_name.clone(),
                says: row_says.clone(),
                proof: Box::new(proof),
            });
            above_cited = Some(super::super::algebra::Cited {
                node: row_node.clone(),
                proof: super::super::tactics::hyp(&row_name),
                says: Some(row_says),
            });
            above = row_name;
        }
        let last = super::super::doc::Proof::By(Tactic::Exact(
            super::super::tactics::hyp(&above),
        ));
        Route::Built(haves_then(haves, last))
    }

    /// An equation a line says, as a term to rewrite the claim with: the
    /// line itself, or, where the line is computed in a narrower type than
    /// the claim, the line cast up to the claim's type, since Lean rewrites
    /// a term only with an equation of its own type.
    pub(super) fn widened(
        &self,
        line: &Node,
        name: &Printed,
        claim: &Node,
        writer: &Writer,
    ) -> Route<Widened> {
        let same = || {
            Route::Built(Widened {
                have: None,
                name: name.clone(),
            })
        };
        let numbers = |n: &Node| -> Vec<Node> {
            n.children
                .iter()
                .filter(|c| writer.is_number(c))
                .cloned()
                .collect()
        };
        let sides = numbers(line);
        if line.notation() != crate::notations::EQUALITY || sides.len() != 2 {
            return same();
        }
        // The line's type as it was written: the least that holds its sides.
        let mut own = super::super::templates::Num::Int;
        for s in &sides {
            match writer.carrier(s) {
                Route::Built(n) => own = own.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // The claim's type, or the calculation's where the claim is a row.
        let mut wanted = self.worked_in.get().map_or(own, |w| w.max(own));
        for s in numbers(claim) {
            match writer.carrier(&s) {
                Route::Built(n) => wanted = wanted.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        if wanted == own {
            return same();
        }
        self.widened_to(line, name, own, wanted, writer)
    }

    /// The equation `line` of numbers of type `own`, proved by `name`,
    /// stated in the wider `wanted` and proved from it by its casts: a
    /// `have` of `<name>_w`.
    pub(super) fn widened_to(
        &self,
        line: &Node,
        name: &Printed,
        own: super::super::templates::Num,
        wanted: super::super::templates::Num,
        writer: &Writer,
    ) -> Route<Widened> {
        let sides: Vec<Node> = line
            .children
            .iter()
            .filter(|c| writer.is_number(c))
            .cloned()
            .collect();
        let equation = line.notation() == crate::notations::EQUALITY;
        let order = line.notation() == crate::notations::ORDER;
        if !(equation || order) || sides.len() != 2 {
            return Route::no("a line widened that is no relation of two numbers");
        }
        let mut printed = Vec::new();
        for s in &sides {
            match writer.number(s, wanted) {
                Route::Built(p) => printed.push(p),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // Numerals alone are told their type.
        if !sides.iter().any(|s| writer.pinned(s)) {
            printed[0] = Printed::cast(printed[0].clone(), writer.num_type(wanted));
        }
        let [left, right]: [Printed; 2] = match printed.try_into() {
            Ok(both) => both,
            Err(_) => return Route::no("an equation of other than two sides"),
        };
        let wide = format!("{}_w", name.text().replace('.', "_"));
        let op = match equation {
            true => super::super::doc::Op::EQUALS,
            false => match super::super::doc::Op::of(&line.spelling().text()) {
                Some(op) => op,
                None => return Route::no("an order Lean writes no relation for"),
            },
        };
        let said = Printed::infix(op, left, right, super::super::doc::LeanType::Prop);
        // An equation mapped into the wider type, its casts pushed in, and
        // compared with what is wanted up to the ring's laws; an order
        // taken across by its casts.
        // From ℚ to ℝ by ℚ's cast lemmas (`rat_to_real`), as any fact of ℚ
        // crosses; from ℤ, by its casts.
        let rational_to_real = own == super::super::templates::Num::Rat
            && wanted == super::super::templates::Num::Real;
        let have = match (equation, rational_to_real) {
            (true, _) => widening_have(writer, &wide, said, own, wanted, name.clone()),
            (false, true) => {
                let mut narrow = Vec::new();
                for s in &sides {
                    match writer.number(s, own) {
                        Route::Built(p) => narrow.push(p),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                let [nl, nr]: [Printed; 2] = match narrow.try_into() {
                    Ok(both) => both,
                    Err(_) => return Route::no("an order of other than two sides"),
                };
                let narrow =
                    Printed::infix(op, nl, nr, super::super::doc::LeanType::Prop);
                let Some(proof) = rat_to_real(name.clone(), &narrow, said.clone())
                else {
                    return Route::no("an order of ℚ with no lemma to ℝ");
                };
                Tactic::Have {
                    name: wide.clone(),
                    says: said,
                    proof: Box::new(super::super::doc::Proof::Term(proof)),
                }
            }
            (false, false) => Tactic::Have {
                name: wide.clone(),
                says: said,
                proof: Box::new(super::super::doc::Proof::By(
                    super::super::tactics::exact_mod_cast(name.clone()),
                )),
            },
        };
        Route::Built(Widened {
            have: Some(have),
            name: super::super::tactics::hyp(&wide),
        })
    }

    /// The checker's record of how a substitution makes its claim: a row's,
    /// put into the row above, from the rows (`substituted_rows`); a claim
    /// sentence's own, where the record takes the substitution sentence by
    /// sentence (`substituted_sentences`); else the step's (`substituted`).
    pub(super) fn substitution_record(
        &self,
        line: usize,
        sentence: Option<usize>,
        row_above: bool,
    ) -> Option<&crate::checker::record::Substituted> {
        match (row_above, sentence) {
            (true, _) => self.rec.substituted_rows.get(&line),
            (false, Some(k)) => self
                .rec
                .substituted_sentences
                .get(&(line, k))
                .or_else(|| self.rec.substituted.get(&line)),
            (false, None) => self.rec.substituted.get(&line),
        }
    }

    /// Where a step's defines are written out (`written_out`): each line the
    /// step names, by the hypothesis that proves it, and the goal, `goal`,
    /// each with what it says. Not every line in scope, which would rewrite
    /// lines the step does not use, a define's own equation among them, to
    /// `True`.
    pub(super) fn rewritten_at(&self, goal: &Node) -> Vec<RewriteAt> {
        let named = self.named_now.borrow();
        let refs: Vec<&String> = named
            .iter()
            .flatten()
            .filter(|r| !self.thm.defines.iter().any(|d| d.label == **r))
            .collect();
        let mut out = self.hypotheses_of(&refs);
        out.push(RewriteAt {
            at: super::super::doc::Location::Goal,
            said: vec![goal.clone()],
            stated: self.writer.formula(goal).built().into_iter().collect(),
        });
        out
    }

    /// Whether `node` takes a remainder of two integers once each named
    /// number's term, `terms`, is put as its number: each part of the `mod`
    /// is such a term or an integer letter, so that the bridge's `mod` is
    /// the integers' `%` (`mod_int_cast`). A remainder inside a term put as
    /// its number is gone.
    pub(super) fn remainder_of_integers(&self, node: &Node, terms: &[String]) -> bool {
        let print = |n: &Node| self.writer.grammar.print(n);
        if terms.contains(&print(node)) {
            return false;
        }
        let integer = |c: &Node| {
            terms.contains(&print(c))
                || (c.children.is_empty()
                    && self.writer.letters.contains_key(&*c.text)
                    && matches!(
                        self.writer.carrier(c),
                        Route::Built(super::super::templates::Num::Int)
                    ))
        };
        if &*node.notation_name() == "mod" && node.children.iter().all(integer) {
            return true;
        }
        node.children
            .iter()
            .any(|c| self.remainder_of_integers(c, terms))
    }

    /// The tactic lines that put each line `refs` names, but those `giving`
    /// a number, in terms of the named numbers `rules` give, `rw [← spec] at
    /// s3; norm_cast at s3`: only where Lean writes the number's term in the
    /// line as the rewrite has it, and the remainder taken as the integers'
    /// `%` only where the line then has one of integers.
    pub(super) fn put_numbers_in_lines(
        &self,
        refs: &[&String],
        giving: &[String],
        rules: &[NumberRule],
    ) -> Vec<Tactic> {
        use super::super::doc::Location;
        use super::super::tactics as t;
        let terms: Vec<String> = rules.iter().map(|r| r.term.clone()).collect();
        let mut out = Vec::new();
        for place in self.hypotheses_of(refs) {
            let Location::Hypothesis(name) = &place.at else {
                continue;
            };
            if giving.contains(name) {
                continue;
            }
            let here: Vec<super::super::doc::Rule> = rules
                .iter()
                .filter(|r| r.lean.as_ref().is_some_and(|l| place.writes(l)))
                .map(|r| r.rule.clone())
                .collect();
            if here.is_empty() {
                continue;
            }
            let at = || TacticArg::At(vec![place.at.clone()]);
            out.push(t::call("rw", vec![TacticArg::Rules(here), at()]));
            if place
                .said
                .iter()
                .any(|n| self.remainder_of_integers(n, &terms))
            {
                out.push(t::call(
                    "rw",
                    vec![TacticArg::Rules(vec![t::forwards(mod_int_cast())]), at()],
                ));
            }
            out.push(t::call("norm_cast", vec![at()]));
        }
        out
    }

    /// The hypotheses that prove the lines `refs`, each with what its lines
    /// say: `s1` once for the `s1.1` and `s1.2` of a line of two sentences.
    pub(super) fn hypotheses_of(&self, refs: &[&String]) -> Vec<RewriteAt> {
        use super::super::doc::{Location, TermKind};
        // The hypothesis a line's proof is, or projects from, `s1` of `s1.2`.
        fn root(p: &Printed) -> Option<&str> {
            match &p.kind {
                TermKind::Letter(name) => Some(name),
                TermKind::Paren(inner) | TermKind::Field { inner, .. } => root(inner),
                _ => None,
            }
        }
        let mut out: Vec<RewriteAt> = Vec::new();
        for r in refs {
            for s in self.trees.get(*r).into_iter().flatten() {
                if let Some(name) = root(&s.proof) {
                    let at = Location::Hypothesis(name.to_string());
                    let stated = self.line_statement(&s.cited()).built();
                    match out.iter_mut().find(|o| o.at == at) {
                        Some(o) => {
                            o.said.push(s.node.clone());
                            o.stated.extend(stated);
                        }
                        None => out.push(RewriteAt {
                            at,
                            said: vec![s.node.clone()],
                            stated: stated.into_iter().collect(),
                        }),
                    }
                }
            }
        }
        out
    }

    /// Whether a substitution's place in `start` is written in the type of
    /// what it is put into, a term of its arithmetic (`Writer::in_formula_type`
    /// of its parent); the whole of `start` is. Any other, a function's
    /// argument or an exponent, is written in its own type.
    pub(super) fn place_in_formula_type(&self, start: &Node, path: &[usize]) -> bool {
        let Some((&last, up)) = path.split_last() else {
            return true;
        };
        at_path(start, up)
            .is_some_and(|parent| self.writer.in_formula_type(parent, last))
    }

    /// `have e_nat : was = now` in ℕ, from the equation's proof `equation`:
    /// an equation of natural numbers put where Lean's term is of ℕ, a
    /// power's exponent or a count. By `exact_mod_cast`, or by `omega`
    /// where a side is an integer said whole, written as its `toNat`, φ(p) =
    /// (p − 1).toNat. Declined where either side is an integer not said
    /// whole.
    pub(super) fn nat_equation(
        &self,
        was: &Node,
        now: &Node,
        equation: &Printed,
        writer: &Writer,
    ) -> Route<Tactic> {
        use super::super::expr::NaturalForm;
        use super::super::templates::Num;
        let forms = [
            natural_form_named(writer, was),
            natural_form_named(writer, now),
        ];
        if forms.contains(&NaturalForm::Integer) {
            return Route::no("an equation not of natural numbers");
        }
        let to_nat = forms.contains(&NaturalForm::ToNat);
        // Each side in ℕ: a natural number as it stands, a whole integer as
        // its `toNat`.
        let side = |n: &Node, form: NaturalForm| match form {
            NaturalForm::ToNat => writer.number(n, Num::Int).map(|t| {
                Printed::of(
                    super::super::doc::TermKind::ToNat(Box::new(
                        super::super::tactics::bracket(t),
                    )),
                    super::super::doc::LeanType::Num(Num::Nat),
                )
            }),
            _ => writer.number(n, Num::Nat),
        };
        let (Route::Built(l), Route::Built(r)) =
            (side(was, forms[0]), side(now, forms[1]))
        else {
            return Route::no("an equation of natural numbers not written in ℕ");
        };
        Route::Built(Tactic::Have {
            name: "e_nat".to_string(),
            says: Printed::infix(
                super::super::doc::Op::EQUALS,
                l,
                r,
                super::super::doc::LeanType::Prop,
            ),
            proof: Box::new(super::super::doc::Proof::By(match to_nat {
                false => super::super::tactics::exact_mod_cast(equation.clone()),
                true => super::super::tactics::on_h(
                    equation,
                    vec![super::super::tactics::call("omega", vec![])],
                ),
            })),
        })
    }

    /// `have e_w : was = now`, the recorded equation as the substitution puts
    /// it, stated in the wider type `to` (`Writer::closed_formula`) from its
    /// proof `equation` in `from` (`widening_have`).
    pub(super) fn equation_widened(
        &self,
        rec: &crate::checker::record::Substituted,
        was: &Node,
        now: &Node,
        from: super::super::templates::Num,
        to: super::super::templates::Num,
        equation: &Printed,
    ) -> Route<Tactic> {
        let put = rec.equation.with_children(vec![was.clone(), now.clone()]);
        let Route::Built(says) = self.writer.closed_formula(&put, to) else {
            return Route::no("an equation the writer cannot state widened");
        };
        Route::Built(widening_have(
            &self.writer,
            "e_w",
            says,
            from,
            to,
            equation.clone(),
        ))
    }
}
