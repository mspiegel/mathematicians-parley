//! Algebra rows, orders and memberships.

use std::mem;

use super::*;
use crate::checker::record::{FirstAt, OrderFact};
use crate::elab::provenance::requirement;

impl<'a> Elaborator<'a> {
    /// What an inequalities step with rows is proved from: the lines it
    /// cites, and for each `algebra` row, the equation of each side it
    /// rewrites with that side of the row above, which the algebra method
    /// proves (`METHODS.md`, inequalities, Rows). A row keeps its sides where
    /// the row above has them, so side meets side. With the equations, what
    /// the rows make is linear in what the step writes; without them a
    /// rewriting such as a·a^m to a^m·a is two atoms. A step with no rows is
    /// proved from its lines as they are.
    pub(super) fn algebra_rows(
        &mut self,
        step: &Step,
        refs: Vec<String>,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<RowsRewritten> {
        let unchanged = RowsRewritten {
            refs: refs.clone(),
            lines: lines.clone(),
        };
        let Some(cut) = rows(&step.just, &self.thm.path) else {
            return Ok(unchanged);
        };
        let here = lines.copy();
        let mut refs = refs;
        let mut above: Option<Term> = None;
        for row in cut? {
            let node = self.read_one(&row.formula)?;
            let written = self.term(&node)?;
            let said = self.to_term(&written);
            if let (RowReason::Algebra, Some(before)) = (&row.reason, &above) {
                for side in 0..2 {
                    let was = self.rpn(&before.children()[side]);
                    let now = self.rpn(&said.children()[side]);
                    if was == now {
                        continue;
                    }
                    let equation = t!(&was, &now, "wceq");
                    match self.prove_field(None, &equation, scope, facts, &here)? {
                        Built(proof) => {
                            let label = format!("row {} side {side}", row.line);
                            here.set(
                                label.clone(),
                                Line::new(equation, proof, Vec::new()),
                            );
                            refs.push(label);
                        }
                        Declined(d) => {
                            return Err(self.defect(
                                row.line,
                                format!(
                                    "the algebra row of step {} rewrites {} as {}, which algebra does not prove: {}",
                                    step.number,
                                    self.render(&was),
                                    self.render(&now),
                                    self.say(&d)
                                ),
                            ))
                        }
                    }
                }
            }
            above = Some(said);
        }
        Ok(RowsRewritten { refs, lines: here })
    }

    /// A term with each defined name written out as what it names.
    pub(crate) fn defined_names_out(&self, term: &Term) -> Term {
        if term.variable().is_some() {
            return term.clone();
        }
        let kids = term.children();
        if term.label() == Some("cv") && kids.len() == 1 {
            if let Some(body) = self.named_body(term, &Vars::new()) {
                return self.defined_names_out(&body);
            }
        }
        let parts: Vec<Term> = kids.iter().map(|k| self.defined_names_out(k)).collect();
        term.with_children(parts)
    }

    /// A term with each finite sum, one holding no sum of its own, written
    /// over `letter`: a sum a define names and the same sum a line writes
    /// are then one term, whatever letters the two were written over.
    pub(super) fn sums_over(&self, term: &Term, letter: &str) -> Term {
        if term.variable().is_some() {
            return term.clone();
        }
        let kids = term.children();
        if term.label() == Some("csu") && kids.len() == 3 {
            let inner = self.rpn(&kids[1]);
            if !inner.has("csu") {
                let from = self.rpn(&kids[2]);
                let summand =
                    self.restated(&kids[1], &t!(from, "cv"), &t!(letter, "cv"));
                return Term::apply(
                    "csu",
                    vec![kids[0].clone(), summand, self.var_of(letter)],
                );
            }
        }
        let parts: Vec<Term> = kids.iter().map(|k| self.sums_over(k, letter)).collect();
        term.with_children(parts)
    }

    /// The claim, the facts and the lines a step or a requires line cites,
    /// with defined names written out: each cited line written otherwise is
    /// laid down written out, carried across by `same`, which reads a defined
    /// name the same way.
    pub(super) fn names_written_out(
        &mut self,
        step: Option<&Step>,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<WrittenOut>> {
        let claim = self.to_term(term);
        let cited: Vec<ProvedClaim> = refs
            .iter()
            .filter_map(|r| self.line_written(r, lines))
            .collect();
        let labels: Vec<&String> = refs
            .iter()
            .filter(|r| self.line_written(r, lines).is_some())
            .collect();
        // Every sum is written over one letter nothing holds, so that a sum
        // a define names and the same sum a line writes are one term.
        let mut seen: Vec<Term> = vec![claim.clone(), self.to_term(scope)];
        seen.extend(cited.iter().map(|l| self.to_term(&l.claim)));
        let refs: Vec<&Term> = seen.iter().collect();
        let as_written = WrittenOut {
            term: term.clone(),
            facts: facts.clone(),
            lines: lines.clone(),
        };
        let letter = self.unheld(&refs).map(|v| self.rpn(&v).to_string());
        // A distance's two points stand in no order, and the methods read a
        // term's atoms as they are spelt: every such pair is put in order.
        let mut said = vec![term.clone()];
        said.extend(cited.iter().map(|l| l.claim.clone()));
        let mut out_of_order = false;
        for s in &said {
            let ordered = self.pairs_in_order(&self.to_term(s));
            out_of_order = out_of_order || self.rpn(&ordered) != *s;
        }
        let names = match &letter {
            Some(letter) => self.writes_name_and_body(&claim, &cited, letter),
            None => false,
        };
        if !names && !out_of_order {
            return Ok(Built(as_written));
        }
        let letter = letter.filter(|_| names);
        let out = self.written_out(&claim, letter.as_deref());
        let term_out = self.rpn(&out);
        let (facts_out, lines_out) = (facts.copy(), lines.copy());
        for (r, line) in labels.into_iter().zip(&cited) {
            let said = self.to_term(&line.claim);
            let written = self.written_out(&said, letter.as_deref());
            let out_rpn = self.rpn(&written);
            if out_rpn == line.claim {
                continue;
            }
            let held = self.carried(r, facts, lines);
            let Built(alike) = self.same(&said, &written, scope, facts, step)? else {
                return Ok(Route::no(
                    "a cited line is not carried to its names written out",
                ));
            };
            let proof = pf!(self.b; scope, line.claim, out_rpn, held, alike, "mpbid");
            self.know(&facts_out, out_rpn.clone(), proof.clone());
            let kept = lines.get(r).expect("a line cited");
            lines_out.set(r.clone(), kept.restated(out_rpn, proof));
        }
        Ok(Built(WrittenOut {
            term: term_out,
            facts: facts_out,
            lines: lines_out,
        }))
    }

    /// Whether dropping identity elements changes an atom of `term`, a part
    /// `field` reads as a whole, F(0 + 1) for F(1): what is under +, −, ·, /,
    /// a power or a negation is the field's to read, and an identity element
    /// there is one it reads already.
    pub(super) fn drops_inside_atom(&self, term: &Term) -> bool {
        if term.variable().is_some() || term.children().is_empty() {
            return false;
        }
        let arithmetic = field::Op::applied(term).is_some()
            || (term.label() == Some(field::NEG) && term.children().len() == 1);
        if arithmetic {
            let operands = match field::Op::applied(term) {
                Some(_) => &term.children()[..2],
                None => term.children(),
            };
            return operands.iter().any(|c| self.drops_inside_atom(c));
        }
        if matches!(term.label(), Some("wceq") | Some("wne") | Some("wn")) {
            return term.children().iter().any(|c| self.drops_inside_atom(c));
        }
        self.rpn(&self.without_identities(term)) != self.rpn(term)
    }

    /// The claim and the lines a step cites with their identity elements
    /// dropped, as the checker reads them for `algebra` (`SYNTAX.md`, "An
    /// identity element goes without saying"): F(0 + 1) is F(1), one atom.
    /// Only where an atom changes: an identity element the field reads it
    /// reads already (`drops_inside_atom`).
    /// Each cited line written otherwise is laid down bare, carried across
    /// by `tidied`; a line that is not carried, or nothing to drop, is a
    /// decline.
    pub(super) fn identities_written_out(
        &mut self,
        refs: &[String],
        out: &WrittenOut,
        scope: &Rpn,
    ) -> Checked<Route<WrittenOut>> {
        let claim_changes = self.drops_inside_atom(&self.to_term(&out.term));
        let line_changes = refs.iter().any(|r| {
            self.line_written(r, &out.lines)
                .is_some_and(|l| self.drops_inside_atom(&self.to_term(&l.claim)))
        });
        if !claim_changes && !line_changes {
            return Ok(Route::no(
                "no atom changes once identity elements are dropped",
            ));
        }
        let term_out = self.rpn(&self.without_identities(&self.to_term(&out.term)));
        let (facts_out, lines_out) = (out.facts.copy(), out.lines.copy());
        let mut dropped = term_out != out.term;
        for r in refs {
            let Some(line) = self.line_written(r, &out.lines) else {
                continue;
            };
            let bare = self.rpn(&self.without_identities(&self.to_term(&line.claim)));
            if bare == line.claim {
                continue;
            }
            let held = self.carried(r, &out.facts, &out.lines);
            let Some(proof) =
                self.tidied(&held, &line.claim, &bare, scope, &out.facts)?
            else {
                return Ok(Route::no(
                    "a cited line is not carried to its identity elements dropped",
                ));
            };
            self.know(&facts_out, bare.clone(), proof.clone());
            let kept = out.lines.get(r).expect("a line cited");
            lines_out.set(r.clone(), kept.restated(bare, proof));
            dropped = true;
        }
        if !dropped {
            return Ok(Route::no("no identity element to drop"));
        }
        Ok(Built(WrittenOut {
            term: term_out,
            facts: facts_out,
            lines: lines_out,
        }))
    }

    /// A term as `names_written_out` reads it: with its defined names
    /// written out and its sums over `letter`, where a letter is given, and
    /// its pairs in no order put in order.
    pub(super) fn written_out(&mut self, term: &Term, letter: Option<&str>) -> Term {
        let read = match letter {
            Some(letter) => {
                let out = self.read_out(term);
                self.sums_over(&out, letter)
            }
            None => term.clone(),
        };
        self.pairs_in_order(&read)
    }

    /// Whether the claim or a cited line writes both a defined name and
    /// what it names, each sum read over `letter`. Only such a step reads
    /// its names written out; any other reads them as written.
    pub(super) fn writes_name_and_body(
        &mut self,
        claim: &Term,
        cited: &[ProvedClaim],
        letter: &str,
    ) -> bool {
        let mut written: BTreeSet<Rpn> = BTreeSet::new();
        let mut named: BTreeSet<Rpn> = BTreeSet::new();
        let mut rest: Vec<Term> = vec![self.sums_over(claim, letter)];
        rest.extend(
            cited
                .iter()
                .map(|l| self.sums_over(&self.to_term(&l.claim), letter)),
        );
        while let Some(node) = rest.pop() {
            if node.variable().is_some() {
                continue;
            }
            let kids = node.children();
            if node.label() == Some("cv") && kids.len() == 1 {
                if let Some(body) = self.named_body(&node, &Vars::new()) {
                    let out = self.defined_names_out(&body);
                    named.insert(self.rpn(&self.sums_over(&out, letter)));
                }
            }
            // A defined function applied names its rule at the argument:
            // t(k) with t(j) = j + 1 names k + 1.
            if node.label() == Some("cfv") && kids.len() == 2 {
                let out = self.read_out(&node);
                if self.rpn(&out) != self.rpn(&node) {
                    named.insert(self.rpn(&self.sums_over(&out, letter)));
                }
            }
            written.insert(self.rpn(&node));
            rest.extend(kids.iter().cloned());
        }
        named.iter().any(|body| written.contains(body))
    }

    /// The parts of the cited lines a plain step leaves out: each written
    /// part `linear` reads that none of its claim's parts adds, takes both
    /// ways or restates in the combination the checker decided it by
    /// (`CheckedTheorem::orders`), whose facts added as they stand are the
    /// claim. Another combination that contradicts the claim denied may
    /// rest on more lines and ask more of its atoms, as `2/p < m` with
    /// `0 < 2/p` asks p ≠ 0 where `m ∈ ℕ` gives `0 < m` alone. The record
    /// places each fact in the line as the page writes it (`written`); the
    /// step adds the same part of the line as `lines` writes it, with its
    /// names written out.
    pub(super) fn not_combined(
        &mut self,
        step: &Step,
        refs: &[String],
        written: &Lines,
        lines: &Lines,
    ) -> Checked<Vec<Rpn>> {
        let Some(order) = self.checked.orders.get(&step.just.line).cloned() else {
            return Err(self.unreached(
                self.at,
                "the checker recorded no combination for a step adding its facts",
            ));
        };
        // Each fact the combination adds as a line writes it, by the line and
        // its place among the parts the line writes; a requires line above,
        // which a requires line made a step cites (`as_a_step`), whole.
        let mut used: Vec<(String, Option<usize>)> = Vec::new();
        let mut placed: Vec<&FirstAt> = Vec::new();
        for part in order.sentences.iter().flatten() {
            let restated = part.restates.as_ref().map(|r| &r.by);
            for fact in part.uses.iter().chain(&part.split).chain(restated) {
                match fact {
                    OrderFact::Line(at) if at.implied.is_none() => placed.push(at),
                    OrderFact::Requires {
                        line,
                        implied: None,
                    } => {
                        let Some(above) = self.requires_line(step, *line) else {
                            return Err(self.unreached(
                                self.at,
                                "a requires line the checker combined is not among its step's",
                            ));
                        };
                        used.push((requirement(above.line), None));
                    }
                    _ => {}
                }
            }
        }
        for at in placed {
            let recorded = self.recorded_statement(at)?;
            let mut found = None;
            for (k, part) in self.line_writes(&at.line, written).into_iter().enumerate()
            {
                let same = part == recorded
                    || self
                        .renaming(&self.to_term(&recorded), &self.to_term(&part))?
                        .is_some();
                if same {
                    found = Some(k);
                    break;
                }
            }
            let Some(k) = found else {
                return Err(self.unreached(
                    self.at,
                    "a fact the checker combined is no part of the line it placed it in",
                ));
            };
            used.push((at.line.clone(), Some(k)));
        }
        let labels = self.b.flabel.clone();
        let mut out = Vec::new();
        for r in refs {
            for (k, said) in self.line_writes(r, lines).into_iter().enumerate() {
                let one = self.to_term(&said);
                if linear::fact(&one, &labels).is_none() {
                    continue;
                }
                let combined = used
                    .iter()
                    .any(|(line, at)| line == r && at.is_none_or(|at| at == k));
                if !combined {
                    out.push(said);
                }
            }
        }
        Ok(out)
    }

    /// An `inequalities` claim, by whichever route reaches it. `skip` names
    /// sentences of the cited lines to leave out: a case of a split must not
    /// split again on the disequality it split on.
    pub fn prove_order(
        &mut self,
        refs: &[String],
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        skip: &[Rpn],
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let goal = self.to_term(term);
        let mut given = Vec::new();
        let mut where_: Vec<(String, Term)> = Vec::new();
        // What a cited membership implies is offered with the facts as
        // written.
        let mut implied_given = Vec::new();
        let mut implied_where: Vec<(String, Term)> = Vec::new();
        for r in refs {
            for said in self.line_writes(r, lines) {
                if skip.contains(&said) {
                    continue;
                }
                if let Some(one) = linear::fact(&self.to_term(&said), &labels) {
                    given.push(one);
                    where_.push((r.clone(), self.to_term(&said)));
                }
            }
            // The bounds only: k ≠ 0 would split every certificate.
            for said in &self.stated_claims(r, facts, lines) {
                if skip.contains(said) {
                    continue;
                }
                for (extra, _lemmas) in self.implied_terms(said) {
                    if let Some(one) = linear::fact(&self.to_term(&extra), &labels) {
                        if one.how != How::Ne {
                            implied_given.push(one);
                            implied_where.push((r.clone(), self.to_term(&extra)));
                        }
                    }
                }
            }
        }
        if goal.variable().is_none() && goal.label() == Some("wa") {
            return self.both_halves(refs, &goal, scope, facts, lines, skip);
        }
        let Some(claim) = linear::fact(&goal, &labels) else {
            return Ok(Route::no("the claim is not linear"));
        };
        if let Some(closed) = self.by_antisymmetry(&goal, scope, facts)? {
            return Ok(Built(closed));
        }
        let written = given.len();
        given.extend(implied_given);
        where_.extend(implied_where);
        let mut all = given.clone();
        all.push(linear::opposite(&claim));
        // Which cited line each fact came from; the claim denied is none.
        let mut line_of: Vec<Option<usize>> = where_
            .iter()
            .map(|(r, _)| refs.iter().position(|one| one == r))
            .collect();
        line_of.push(None);
        let Some(found) = linear::certificate(&all, &line_of, self.adding_only) else {
            return Ok(Route::no("the cited facts do not reach the claim"));
        };
        let found = match found {
            Certificate::Farkas(w) => w,
            either => {
                return self.either_way(
                    &either, refs, &where_, &given, term, scope, facts, lines, skip,
                )
            }
        };
        if !found.contains_key(&given.len()) {
            // The denied claim went unused, so the cited facts refute each
            // other, and any claim follows (`METHODS.md`, inequalities: the
            // set with the claim denied has no solution). One written fact
            // the refutation uses is denied from the rest, by this route
            // with that fact left out, and the two give the claim
            // (`pm2.21dd`).
            let Some(j) = found
                .iter()
                .filter(|(i, k)| !k.is_zero() && **i < written)
                .map(|(i, _)| *i)
                .next()
            else {
                return Ok(Route::no(
                    "the cited facts refute each other only through what their memberships imply",
                ));
            };
            let (r, said) = where_[j].clone();
            let fact = self.rpn(&said);
            let mut leave = skip.to_vec();
            leave.push(fact.clone());
            let denied = take!(self.prove_order(
                refs,
                &t!(&fact, "wn"),
                scope,
                facts,
                lines,
                &leave
            )?);
            let held = take!(self.cited_fact(&r, &said, scope, facts, lines)?);
            return Ok(Built(
                pf!(self.b; scope, fact, term, held, denied, "pm2.21dd"),
            ));
        }
        let used: Vec<usize> = found
            .iter()
            .filter(|(i, k)| !k.is_zero() && **i < given.len())
            .map(|(i, _)| *i)
            .collect();
        let weight = found[&given.len()].clone();
        if claim.how == How::Ne {
            let made = self.stays_apart(
                &used, &given, &where_, &claim, &goal, scope, facts, lines,
            )?;
            if made.is_declined() {
                let apart =
                    self.apart_by_order(refs, &goal, scope, facts, lines, skip)?;
                if !apart.is_declined() {
                    return Ok(apart);
                }
            }
            return Ok(made);
        }
        if goal.variable().is_none() && goal.label() == Some("wn") {
            return self.negated_order(&goal, refs, term, scope, facts, lines, skip);
        }
        let Some((left, right, how)) = order_sides(&goal) else {
            return Ok(Route::no("the claim states no relation"));
        };
        let (left, right) = (self.rpn(&left), self.rpn(&right));
        // What the scaled facts leave over is a constant, which the method
        // may use as a closed numeral fact the step does not cite.
        let mut spare = claim.side.clone();
        for i in &used {
            spare = spare.minus(&given[*i].side.scaled(&(&found[i] / &weight)));
        }
        if !spare.constant_only() {
            return Ok(Route::no("what is left over is not a constant"));
        }
        // One equation, scaled by a whole number, that is the claim with
        // nothing left over. A fraction is `combination`'s, which clears its
        // denominator.
        let one_equation = match used.as_slice() {
            [only] if given[*only].how == How::Eq && spare.constant.is_zero() => {
                Some((*only, &found[only] / &weight)).filter(|(_, t)| t.is_integer())
            }
            _ => None,
        };
        if let Some((only, times)) = one_equation {
            return self.one_equation_scaled(
                &where_[only],
                &times,
                &left,
                &right,
                how,
                scope,
                facts,
                lines,
            );
        }
        let parts: Vec<Part> = used
            .iter()
            .map(|i| {
                let (cited, said) = where_[*i].clone();
                Part {
                    cited,
                    said,
                    times: &found[i] / &weight,
                }
            })
            .collect();
        self.combination(
            &parts,
            &left,
            &right,
            how,
            &spare.constant,
            scope,
            facts,
            lines,
        )
    }

    /// `membership`: a term in a number system because its parts are, down
    /// to atoms whose membership the step's lines say.
    pub fn by_membership(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let claim = self.to_term(term);
        let supplied = self.supplied(Some(step), scope, facts)?;
        let cited = self.with_cited(Some(step), scope, &supplied, None)?;
        let known = facts.with(&cited);
        // A cited define that says its kind of number keeps its name: its
        // kind gives the value's membership, u(x) ∈ ℝ of `let u(x) = …, a
        // real number`, as the checker reads the step.
        let mut kinded = BTreeSet::new();
        for d in &self.thm.defines {
            if step.just.refs.contains(&d.label)
                && d.kinded(&self.thm.path, &self.g.members)?.is_some()
            {
                kinded.insert(d.label.clone());
            }
        }
        let kept = mem::replace(&mut self.kept_named, kinded);
        let made = self.member_of(&claim, scope, &known, Some(step));
        self.kept_named = kept;
        match made? {
            Built(p) => Ok(Built(p)),
            Declined(d) => Err(self.defect(
                step.line,
                format!(
                    "{} is not built from what step {} cites: {}",
                    self.render(term),
                    step.number,
                    self.say(&d)
                ),
            )),
        }
    }

    /// The proof of one membership by `membership`'s procedure, from the
    /// facts `known`, or a decline naming what it lacks.
    pub fn member_of(
        &mut self,
        claim: &Term,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        // Said of every member: the member is fixed, what its membership says
        // is laid beside it, and the claim is generalised.
        if claim.variable().is_none() && claim.label() == Some("wral") {
            let (body, variable, over) = (
                claim.children()[0].clone(),
                claim.children()[1].clone(),
                claim.children()[2].clone(),
            );
            return self.for_every(
                scope,
                known,
                &body,
                &variable,
                &over,
                &mut |me, said, inner, lifted| me.member_of(said, inner, lifted, step),
                true,
            );
        }
        let term = self.rpn(claim);
        // The claim with its defined names and maps read as what they stand
        // for, and nothing else changed (`read_out`): a part is then the term
        // the page wrote, which the facts saying it are found by, and not a
        // respelling of it, ⌊c·10^n⌋ for ⌊10^n·c⌋, that only the parts' own
        // memberships would carry back.
        let read = self.read_out(claim);
        let (whole, system) = (read.children()[0].clone(), read.children()[1].clone());
        // The claim is read with its defined names written out, and so is
        // each membership the facts hold: a line saying a defined name is
        // real is then a line about what the claim, read, holds.
        let known = &self.read_memberships(scope, known, step)?;
        let made = if whole.variable().is_none() && whole.label() == Some("csu") {
            self.summed(&whole, &self.rpn(&system), scope, known, step)?
        } else {
            self.part(&self.rpn(&whole), &self.rpn(&system), scope, known)?
        };
        if made.is_declined() || self.rpn(&read) == term {
            return Ok(made);
        }
        let made = take!(made);
        let alike = take!(self.same(&read, claim, scope, known, step)?);
        Ok(Built(
            pf!(self.b; scope, self.rpn(&read), term, made, alike, "mpbid"),
        ))
    }

    /// `known`, with each fact `part` builds from — a membership in a number
    /// system, a term's not being 0, and a term above 0 or below it — laid
    /// down beside itself in its standard form, where that differs.
    pub(crate) fn read_memberships(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Facts> {
        let kept = mem::replace(&mut self.reading_facts, true);
        let out = self.memberships_read(scope, known, step);
        self.reading_facts = kept;
        out
    }

    pub(super) fn memberships_read(
        &mut self,
        scope: &Rpn,
        known: &Facts,
        step: Option<&Step>,
    ) -> Checked<Facts> {
        let out = known.copy();
        // The side conditions the step wrote are facts here as well, read
        // as the rest are.
        let mut offered = known.entries();
        for (said, w) in self.written.entries() {
            if let Some(lifted) = self.lifted_to(&said, &w.proof, &w.at, scope) {
                offered.push((said, lifted));
            }
        }
        for (said, held) in offered {
            let fact = self.to_term(&said);
            let member = fact.label() == Some("wcel")
                && lookup(
                    rules::SYSTEMS,
                    self.rpn(&fact.children()[1]).alone().unwrap_or_default(),
                )
                .is_some();
            let nonzero = fact.label() == Some("wn")
                && fact.children()[0].label() == Some("wceq")
                && self.rpn(&fact.children()[0].children()[1]).alone() == Some("cc0");
            // A term above zero or below it, which says it is not zero.
            let signed = fact.label() == Some("wbr")
                && self.rpn(&fact.children()[2]).alone() == Some("clt")
                && (self.rpn(&fact.children()[0]).alone() == Some("cc0")
                    || self.rpn(&fact.children()[1]).alone() == Some("cc0"));
            if fact.variable().is_some() || !(member || nonzero || signed) {
                continue;
            }
            let read = self.standard(&fact);
            let read_rpn = self.rpn(&read);
            if read_rpn == said || self.holds(&out, &read_rpn) {
                continue;
            }
            if let Built(alike) = self.same(&fact, &read, scope, known, step)? {
                let proof = pf!(self.b; scope, said, read_rpn, held, alike, "mpbid");
                self.know(&out, read_rpn.clone(), proof);
            }
        }
        Ok(out)
    }
}
