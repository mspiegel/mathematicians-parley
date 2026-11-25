//! Algebra, fields and what is apart from zero.

use std::mem;

use super::*;
use crate::checker::record::{NonzeroBy, NotZero};
use crate::elab::state::Divided;
use crate::methods::membership::Shown;
use crate::rules::System;

/// How a divisor the build asks of is the page's term a record entry names
/// (`Elaborator::asked_of`).
enum AskedAs {
    /// Spelt as the page spells it, in standard form.
    Page,
    /// The normaliser's spelling of it: ( scope -> named = asked ).
    Normal(Proof),
}

impl<'a> Elaborator<'a> {
    pub(super) fn ask<'s>(&'s mut self, spec: &'s Spec) -> Ask<'s, 'a> {
        Ask { el: self, spec }
    }

    /// The claim as the checker found it made of the lines it cites
    /// (`reason_made`), proved by `normal`. Each part the reason divides by
    /// is shown not zero as the checker recorded it (`reason_divided`).
    pub fn algebra(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let Some(made) = self.reason_made.clone() else {
            return Ok(Route::no(
                "an algebra claim the checker recorded no making of",
            ));
        };
        self.algebra_made(step, &made, term, scope, facts, lines)
    }

    /// `algebra` of a claim made as `made` says.
    fn algebra_made(
        &mut self,
        step: &Step,
        made: &AlgebraMade,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(pairs) = pairs::relation(&self.to_term(term)) {
            let AlgebraMade::Pairs(each) = made else {
                return Ok(Route::no("two pairs the checker recorded as one claim"));
            };
            return self.algebra_pairs(step, &pairs, each, scope, facts, lines);
        }
        // A defined name is read as what it names, as `inequalities` reads
        // it: the claim and each cited line are taken with their defined
        // names written out, decided so, and the proof is carried back to
        // the claim as the page writes it.
        let out = take!(self.names_written_out(
            Some(step),
            &step.just.refs,
            term,
            scope,
            facts,
            lines
        )?);
        // An atom spelt two ways, F(0 + 1) and F(1), is one once identity
        // elements are dropped, as the checker reads the step: where the
        // claim or a line it cites has one, the claim and the lines are
        // decided bare, and the proof carried back.
        let found = match self.identities_written_out(&step.just.refs, &out, scope)? {
            Built(bare) => {
                // The cited lines are read from the elaborator's own table as
                // well as from the ones handed down, a membership of an atom
                // among them, so the bare lines stand there while they are
                // decided.
                let kept = mem::replace(&mut self.lines, bare.lines.clone());
                let decided = self.field_made(step, made, &bare, scope);
                self.lines = kept;
                match decided? {
                    Built(p) => {
                        match self
                            .tidied(&p, &bare.term, &out.term, scope, &out.facts)?
                        {
                            Some(back) => Built(back),
                            None => {
                                Route::no("the claim read bare is not carried back")
                            }
                        }
                    }
                    Declined(d) => Declined(d),
                }
            }
            Declined(_) => self.field_made(step, made, &out, scope)?,
        };
        if let Declined(d) = &found {
            // Found but not written is a gap in the method, and nothing is
            // taken in its place: the build stops here.
            return Err(self.defect(
                step.line,
                format!(
                    "algebra cannot write the proof the checker found of step {}: {}",
                    step.number,
                    self.say(d)
                ),
            ));
        }
        if out.term == *term {
            return Ok(found);
        }
        let proof = take!(found);
        let (said, want) = (self.to_term(&out.term), self.to_term(term));
        let Built(back) = self.same(&said, &want, scope, facts, Some(step))? else {
            return Ok(Route::no("the claim written out is not carried back"));
        };
        Ok(Built(
            pf!(self.b; scope, out.term, term, proof, back, "mpbid"),
        ))
    }

    /// Two pairs compared coordinate by coordinate by `algebra`
    /// (`METHODS.md`, Pairs), each coordinate's claim made as the checker
    /// found (`AlgebraMade::Pairs`): both coordinates' equations, or the
    /// difference at the coordinate the pairs are apart at.
    pub(super) fn algebra_pairs(
        &mut self,
        step: &Step,
        pairs: &PairRelation,
        each: &[(Coordinate, AlgebraMade)],
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let Some((_, made)) = each.iter().find(|(c, _)| *c == at) else {
                    return Ok(Route::no(
                        "a coordinate the checker recorded no making at",
                    ));
                };
                let equation = self.rpn(&pairs.equation(at));
                proved.push(take!(
                    self.algebra_made(step, made, &equation, scope, facts, lines)?
                ));
            }
            return Ok(Built(
                self.pairs_equal(pairs, scope, &proved[0], &proved[1]),
            ));
        }
        let [(at, made)] = each else {
            return Ok(Route::no("pairs apart at other than one coordinate"));
        };
        let denial = self.rpn(&pairs.denial(*at));
        let apart = take!(self.algebra_made(step, made, &denial, scope, facts, lines)?);
        let members = self.number_members(pairs, scope, facts)?;
        Ok(Built(self.pairs_apart(pairs, scope, *at, &apart, &members)))
    }

    /// The claim and lines `out` holds, read as `out` read them, proved as
    /// `made` says the claim is made of the lines: an identity, a sum of
    /// the cited equations, or a cited disequality rescaled.
    fn field_made(
        &mut self,
        step: &Step,
        made: &AlgebraMade,
        out: &WrittenOut,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        // Every finite sum the step reads is written over one letter nothing
        // holds, as `prove_field` writes it.
        let linear = self.sums_linear(&out.term, Some(step), &out.lines);
        let letter = match linear {
            true => {
                let mut seen: Vec<Term> =
                    vec![self.to_term(&out.term), self.to_term(scope)];
                for r in &step.just.refs {
                    if let Some(line) = self.line_written(r, &out.lines) {
                        seen.push(self.to_term(&line.claim));
                    }
                }
                let refs: Vec<&Term> = seen.iter().collect();
                self.unheld(&refs).map(|v| self.rpn(&v).to_string())
            }
            false => None,
        };
        let kept = mem::replace(&mut self.sum_letter, letter);
        let proved = field::reading_sums(linear, || {
            self.field_made_read(step, made, out, scope)
        });
        self.sum_letter = kept;
        proved
    }

    /// `field_made`, with the step's sums read as it reads them.
    fn field_made_read(
        &mut self,
        step: &Step,
        made: &AlgebraMade,
        out: &WrittenOut,
        scope: &Rpn,
    ) -> Checked<Route<Proof>> {
        // A `requires` line is where a step says its denominator is not
        // zero, so what the normalizer is asked is asked of those as well;
        // and what the step cites is laid over the scope's copies, so that
        // a fact one of its lines says is taken from that line.
        let supplied = self.supplied(Some(step), scope, &out.facts)?;
        let facts = self.with_cited(Some(step), scope, &supplied, None)?;
        let mut w = Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: true,
            written: Some(facts.clone()),
            atoms: RefCell::default(),
            implied: Implied::default(),
        });
        let goal = self.to_term(&out.term);
        match made {
            AlgebraMade::Sum(sum) if sum.terms.is_empty() => {
                let Sides { left, right } = self.equation_sides(&out.term);
                self.same_polynomial(&mut w, &left, &right)
            }
            AlgebraMade::Sum(sum) => {
                self.summed_from_cited(sum, out, scope, &facts, &mut w)
            }
            AlgebraMade::Rescaled(r) => {
                self.apart_from_cited(step, r, &goal, out, scope, &facts, &mut w)
            }
            AlgebraMade::Pairs(_) => Ok(Route::no("pairs read as one claim")),
        }
    }

    /// Whether a step reads its sums as linear: one of them, in its claim or
    /// a line it cites, is linear in something (`field::says_something_linear`).
    pub fn sums_linear(&self, term: &Rpn, step: Option<&Step>, lines: &Lines) -> bool {
        let labels = self.b.flabel.clone();
        let mut said = vec![self.to_term(term)];
        if let Some(step) = step {
            for r in &step.just.refs {
                if let Some(line) = self.line_written(r, lines) {
                    said.push(self.to_term(&line.claim));
                }
            }
        }
        said.iter()
            .any(|t| field::says_something_linear(t, &labels))
    }

    /// An identity of the field (`field_proved`), its sums read as the step
    /// reads them.
    pub fn prove_field(
        &mut self,
        step: Option<&Step>,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        // Every finite sum the step reads is written over one letter nothing
        // holds, which neither the claim, the scope nor a cited line spells;
        // where the step reads its sums as atoms there is none.
        let linear = self.sums_linear(term, step, lines);
        let letter = if linear {
            let mut seen: Vec<Term> = vec![self.to_term(term), self.to_term(scope)];
            if let Some(step) = step {
                for r in &step.just.refs {
                    if let Some(line) = self.line_written(r, lines) {
                        seen.push(self.to_term(&line.claim));
                    }
                }
            }
            let refs: Vec<&Term> = seen.iter().collect();
            self.unheld(&refs).map(|v| self.rpn(&v).to_string())
        } else {
            None
        };
        let kept = mem::replace(&mut self.sum_letter, letter);
        let out =
            field::reading_sums(linear, || self.field_proved(step, term, scope, facts));
        self.sum_letter = kept;
        out
    }

    /// An identity of the field, proved by `normal`, the facts the step
    /// cites laid over the scope's where a step asks it.
    pub(super) fn field_proved(
        &mut self,
        step: Option<&Step>,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let goal = self.to_term(term);
        if goal.variable().is_some()
            || goal.label() != Some("wceq")
            || goal.children().len() != 2
        {
            return Ok(Route::no("the claim is not an equation"));
        }
        // A `requires` line is where a step says its denominator is not
        // zero, so what the normalizer is asked is asked of those as well;
        // and what the step cites is laid over the scope's copies, so that
        // a fact one of its lines says is taken from that line.
        let facts = match step {
            Some(step) => {
                let supplied = self.supplied(Some(step), scope, facts)?;
                self.with_cited(Some(step), scope, &supplied, None)?
            }
            None => facts.clone(),
        };
        let mut w = Work::new(Spec {
            scope: scope.clone(),
            facts: facts.clone(),
            apart: true,
            written: Some(facts.clone()),
            atoms: RefCell::default(),
            implied: Implied::default(),
        });
        let left = self.rpn(&goal.children()[0]);
        let right = self.rpn(&goal.children()[1]);
        self.same_polynomial(&mut w, &left, &right)
    }

    /// A disequality that is a cited one rescaled: the cited fact becomes a
    /// difference that is not zero, the two differences are shown to be one
    /// polynomial, and the claim's difference is not zero either, the cited
    /// difference multiplied by any rational other than 0 (`METHODS.md`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn apart_from_cited(
        &mut self,
        step: &Step,
        rescaled: &Rescaled,
        goal: &Term,
        out: &WrittenOut,
        scope: &Rpn,
        facts: &Facts,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let lines = &out.lines;
        let inner = goal.children()[0].clone();
        let (lhs, rhs) = (
            self.rpn(&inner.children()[0]),
            self.rpn(&inner.children()[1]),
        );
        let whole = t!(lhs, rhs, "cmin", "co");
        // The cited disequality and the number its polynomial is multiplied
        // by to be the claim's, as the checker found them.
        let OrderFact::Line(at) = &rescaled.fact else {
            return Ok(Route::no(
                "a rescaled disequality other than a cited line's",
            ));
        };
        let written = self.term(&at.written)?;
        let node = self.read_alike(&self.to_term(&written), &out.read);
        let by = self.term(&rescaled.by)?;
        let Value::Exact(numerators) = take!(field::closed_value(&self.to_term(&by)))
        else {
            return Ok(Route::no("a rescaling by no exact number"));
        };
        let r = &at.line;
        let pair = node.children()[0].clone();
        let (p, qq) = (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
        let mut gap = t!(p, qq, "cmin", "co");
        // A disequality is read by its numerator, so the two
        // differences are one a multiple of the other by the scale
        // of their numerators times the ratio of their denominators,
        // where both are numbers: k(k + 1)/2 − 0 is 1/2 of k(k + 1) − 0.
        let below = |t: &Rpn| {
            field::read(&self.to_term(t), &labels)
                .under
                .constant_value()
        };
        let scale = match (below(&gap), below(&whole)) {
            (Some(theirs), Some(ours)) if !ours.is_zero() => numerators * theirs / ours,
            _ => numerators,
        };
        let given = take!(self.cited_fact(r, &node, scope, facts, lines)?);
        let pp = self.membership(&p, "cc", scope, &w.spec.facts)?;
        let pq = self.membership(&qq, "cc", scope, &w.spec.facts)?;
        let turned = self.b.ap(
            "neqned",
            &binds! {"ph" => scope, "A" => &p, "B" => &qq},
            &[&given],
        );
        let mut apart = self.b.ap(
            "subne0d",
            &binds! {"ph" => scope, "A" => &p, "B" => &qq},
            &[&pp, &pq, &turned],
        );
        if scale == q(-1) {
            let pg = self.membership(&gap, "cc", scope, &w.spec.facts)?;
            apart = self.b.ap(
                "negne0d",
                &binds! {"ph" => scope, "A" => &gap},
                &[&pg, &apart],
            );
            gap = t!(gap, "cneg");
        } else if scale != q(1) {
            // Any other rational multiple (`METHODS.md`): the scale is
            // a closed number other than 0, k(k + 1)/2 ≠ 0 from
            // k(k + 1) ≠ 0 at 1/2.
            let times = field::spell_rational(&scale);
            let what =
                format!("the scale {} of step {}", self.render(&times), step.number);
            let apart_from_zero = t!(times, "cc0", "wne");
            let nonzero =
                self.closed_fact(&apart_from_zero, scope, facts, &what, Some(step))?;
            let ps = self.membership(&times, "cc", scope, &w.spec.facts)?;
            let pg = self.membership(&gap, "cc", scope, &w.spec.facts)?;
            apart = self.b.ap(
                "mulne0d",
                &binds! {"ph" => scope, "A" => &times, "B" => &gap},
                &[&ps, &pg, &nonzero, &apart],
            );
            gap = t!(times, gap, "cmul", "co");
        }
        let alike = take!(self.same_polynomial(w, &gap, &whole)?);
        let pl = self.membership(&lhs, "cc", scope, &w.spec.facts)?;
        let pr = self.membership(&rhs, "cc", scope, &w.spec.facts)?;
        let moved = self.b.ap(
            "eqnetrrd",
            &binds! {"ph" => scope, "A" => &gap, "B" => &whole, "C" => "cc0"},
            &[&alike, &apart],
        );
        let differ = self.b.ap(
            "subne0ad",
            &binds! {"ph" => scope, "A" => &lhs, "B" => &rhs},
            &[&pl, &pr, &moved],
        );
        Ok(Built(self.b.ap(
            "neneqd",
            &binds! {"ph" => scope, "A" => &lhs, "B" => &rhs},
            &[&differ],
        )))
    }

    /// What says a denominator is not zero, asked of the scope: the text
    /// writes these, so the fact is there to be found. `normal` asks this
    /// while writing a proof it has already decided, so a missing fact is a
    /// defect here and not a decline.
    pub fn not_zero(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        said: &Rpn,
    ) -> Checked<Proof> {
        let kept = OnceCell::new();
        self.not_zero_named(scope, facts, &kept, None, said, said)
    }

    /// `not_zero`, where what is asked is a form the normaliser made of a
    /// divisor the page wrote as `named`, which a defect names, proved as
    /// the checker recorded it (`reason_apart`), with the lines the page
    /// writes in scope where the emitter is given them (`written`).
    pub fn not_zero_named(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        written: Option<&Facts>,
        said: &Rpn,
        named: &Rpn,
    ) -> Checked<Proof> {
        match self.reason_apart(said, scope, facts, implied, written)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                self.at,
                format!(
                    "nothing says {}, which this step needs to divide by it",
                    self.render(&t!(named, "cc0", "wne"))
                ),
            )),
        }
    }

    /// ( scope -> divisor =/= 0 ) of a divisor the reason being built divides
    /// by, as the checker recorded it (`reason_divided`, `recorded_apart`),
    /// `written` being the lines the page writes in scope where an emitter
    /// is given them; outside a reason the record names no divisor, and only
    /// numerals whose value is not zero are shown so.
    pub fn reason_apart(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        written: Option<&Facts>,
    ) -> Checked<Route<Proof>> {
        let divided = Divided {
            recorded: self.reason_divided.clone().unwrap_or_default(),
            written: written.map(Facts::copy),
        };
        let kept = self.divided.replace(divided);
        let apart = self.divisor_apart(divisor, scope, facts, implied);
        self.divided = kept;
        apart
    }

    /// ( scope -> divisor =/= 0 ): a reason's divisor as the checker
    /// recorded it (`divided`, `recorded_apart`); and a membership's, by the
    /// order a membership takes evidence of a divisor in (`ELABORATION.md`,
    /// a divisor's ≠ 0), or a decline:
    ///
    /// 1. a term of numerals alone whose value is not zero, worked out as
    ///    `arithmetic` works one out, or a positive integer the page says
    ///    once (`SYNTAX.md`), which rests on no line;
    /// 2. a line the step may rest on saying it (`written_nonzero`);
    /// 3. its parts: a product, a quotient, a negation or a power to a
    ///    numeral is not zero when its parts are, each by this same order.
    ///
    /// A line saying the whole comes before its parts: a step citing t² ≠ 0
    /// rests on that.
    pub fn divisor_apart(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
    ) -> Checked<Route<Proof>> {
        if let Some(divided) = self.divided.clone() {
            return self.recorded_apart(divisor, &divided, scope, facts, implied);
        }
        let apart = t!(divisor, "cc0", "wne");
        // `facts` are what the step may rest on (`in_hand`), and nothing else
        // in scope is read (`GOALS.md` decision 9).
        let numeral = numerals::value(&self.to_term(divisor)).filter(|v| !v.is_zero());
        if let Some(value) = numeral {
            let closed = numerals::ne0(&self.b, value);
            return Ok(Built(pf!(self.b; apart, scope, closed, "a1i")));
        }
        if let Some(found) = self.closed_nonzero(divisor, scope, facts)? {
            return Ok(Built(found));
        }
        if let Some(positive) = self.positive_divisor(divisor, scope, facts)? {
            return Ok(Built(positive));
        }
        if let Some(found) = self.written_nonzero(scope, facts, implied, divisor)? {
            return Ok(Built(found));
        }
        if let Built(found) = self.parts_apart(divisor, scope, facts, implied)? {
            return Ok(Built(found));
        }
        Ok(self.no(
            "nothing says {}, which this step needs to divide by it",
            &[&apart],
        ))
    }

    /// ( scope -> divisor =/= 0 ) as the checker recorded it not zero
    /// (`NotZero`): numerals alone, a positive integer the page says once,
    /// or the one line the record names, the divisor whole where the record
    /// names it; else a product of parts the record says are positive
    /// integers, shown in ℕ whole (`positive_by_record`); else each of its
    /// parts (`parts_apart`). A decline where the record holds none.
    fn recorded_apart(
        &mut self,
        divisor: &Rpn,
        divided: &Divided,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
    ) -> Checked<Route<Proof>> {
        let recorded = &divided.recorded;
        let apart = t!(divisor, "cc0", "wne");
        // Numerals alone rest on no line: their value says it, of a divisor
        // the page writes and of one the normaliser makes of them alike.
        if let Some(value) =
            numerals::value(&self.to_term(divisor)).filter(|v| !v.is_zero())
        {
            let closed = numerals::ne0(&self.b, value);
            return Ok(Built(pf!(self.b; apart, scope, closed, "a1i")));
        }
        if let Some(found) = self.closed_nonzero(divisor, scope, facts)? {
            return Ok(Built(found));
        }
        // The record names the page's term, and the normaliser asks of the
        // same term in its own form (`asked_of`): the term is shown not zero
        // as the page writes it, and carried to the form asked.
        for entry in recorded {
            let named = self.term(&entry.term)?;
            let Some(how) = self.asked_of(divisor, &named, scope, facts)? else {
                continue;
            };
            // What is shown not zero: the divisor asked, spelt as the page
            // spells it, or else the page's term, carried after.
            let shown = match &how {
                AskedAs::Page => divisor.clone(),
                AskedAs::Normal(_) => named.clone(),
            };
            let given = match &entry.by {
                // Proved above, where its value is not zero.
                NonzeroBy::Numerals => None,
                NonzeroBy::Positive { shown: derived } => {
                    self.recorded_positive(&shown, derived, scope, facts)?
                }
                // The line the record names, held among the facts a membership
                // is answered from and the lines the page writes alike.
                NonzeroBy::Stated { from, .. } => {
                    let from = self.term(from)?;
                    let lines = match &divided.written {
                        Some(written) => facts.with(written),
                        None => facts.copy(),
                    };
                    // That line alone says the divisor is not zero, with the
                    // memberships in hand for carrying it to the spelling
                    // asked.
                    match self.recorded_line(&from, &lines, scope)? {
                        Some(said) => {
                            let only = facts.filtered(|c, _| c.ends_with(&["wcel"]));
                            self.know(&only, said.claim, said.proof);
                            self.written_nonzero(
                                scope,
                                &only,
                                &OnceCell::new(),
                                &shown,
                            )?
                        }
                        None => None,
                    }
                }
            };
            let found = match (given, &how) {
                (Some(given), AskedAs::Page) => Some(given),
                (Some(given), AskedAs::Normal(same)) => Some(self.b.ap(
                    "eqnetrrd",
                    &binds! {"ph" => scope, "A" => &named, "B" => divisor, "C" => "cc0"},
                    &[same, &given],
                )),
                (None, _) => None,
            };
            return Ok(match found {
                Some(p) => Built(p),
                None => self.no(
                    "the checker recorded why {} holds, and the build does not reach it",
                    &[&apart],
                ),
            });
        }
        // A product of positive integers, or one to a numeral power, is a
        // positive integer: where the record says each part is one, the
        // whole is shown in ℕ (`positive_divisor`), as a part is.
        if self.positive_by_record(&self.to_term(divisor), recorded, scope, facts)? {
            return Ok(match self.positive_divisor(divisor, scope, facts)? {
                Some(p) => Built(p),
                None => self.no(
                    "the checker recorded each part of {} a positive integer, and the build does not reach it",
                    &[&apart],
                ),
            });
        }
        self.parts_apart(divisor, scope, facts, implied)
    }

    /// ( scope -> divisor =/= 0 ) of a positive integer, the divisor in ℕ
    /// by the derivation the checker recorded (`NonzeroBy::Positive`) and
    /// so not zero (`nnne0d`). None where the derivation is not reached.
    fn recorded_positive(
        &mut self,
        divisor: &Rpn,
        shown: &Shown,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let Some(member) =
            self.derived_membership_as(None, divisor, System::N, shown, scope, facts)?
        else {
            return Ok(None);
        };
        Ok(Some(self.b.ap(
            "nnne0d",
            &binds! {"ph" => scope, "A" => divisor},
            &[&member],
        )))
    }

    /// How a divisor asked is the page's term `named` the record names, or
    /// None where it is not: the same term in standard form, with the
    /// defines the reason is read with written out as the record spells it
    /// (`recorded_out`), |BO| asked of |OB| and A of Σ(k = 1 to n) a(k)² with
    /// A so defined; or the normaliser's spelling of it, 1·x¹ + 3·1 asked of x + 3,
    /// with ( scope -> named = asked ) (`apart_as_written`). A product the
    /// normaliser asks of, 1·|AP|¹, is no entry's term, and is taken apart
    /// (`parts_apart`).
    fn asked_of(
        &mut self,
        divisor: &Rpn,
        named: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<AskedAs>> {
        let (asked, recorded) = (self.to_term(divisor), self.to_term(named));
        if self.alike_as_recorded(&asked, &recorded) {
            return Ok(Some(AskedAs::Page));
        }
        let mut w = Work::plain(scope, facts);
        let labels = self.b.flabel.clone();
        let subject = self.to_term(named);
        Ok(
            match w.e.normalize(&mut self.ask(&w.spec), &subject, &labels)? {
                Built((items, same)) if Emitter::spell_run(&items) == *divisor => {
                    Some(AskedAs::Normal(same))
                }
                _ => None,
            },
        )
    }

    /// The line the record names, `from`, as the build holds it under
    /// `scope`: among `lines`, or among what the step wrote, its requires
    /// lines (`written_held`), each found by standard form as `held` finds
    /// a fact; else the one of either that is `from` with the defines the
    /// reason is read with written out, as the record spells it, A > 0 of
    /// Σ(k = 1 to n) a(k)² > 0 with A so defined (`alike_as_recorded`).
    fn recorded_line(
        &mut self,
        from: &Rpn,
        lines: &Facts,
        scope: &Rpn,
    ) -> Checked<Option<ProvedClaim>> {
        let found = |claim: &Rpn, proof: Proof| ProvedClaim {
            claim: claim.clone(),
            proof,
        };
        if let Some(proof) = self.held(lines, from, scope)? {
            return Ok(Some(found(from, proof)));
        }
        if let Some(w) = self.written_held(from)? {
            if let Some(proof) = self.lifted_to(from, &w.proof, &w.at, scope) {
                return Ok(Some(found(from, proof)));
            }
        }
        let recorded = self.to_term(from);
        for (claim, proof) in lines.entries() {
            if self.alike_as_recorded(&self.to_term(&claim), &recorded) {
                return Ok(Some(found(&claim, proof)));
            }
        }
        let written = self.written.clone();
        for (claim, proof) in written.facts().entries() {
            if !self.alike_as_recorded(&self.to_term(&claim), &recorded) {
                continue;
            }
            let Some(at) = written.at(&claim) else {
                continue;
            };
            if let Some(proof) = self.lifted_to(&claim, &proof, at, scope) {
                return Ok(Some(found(&claim, proof)));
            }
        }
        Ok(None)
    }

    /// Whether `asked`, a term the build holds, is `recorded`, a term the
    /// checker's record of the reason being built names: the two in
    /// standard form once the defines the reason is read with are written
    /// out (`recorded_out`), and each sum is read over one letter neither
    /// holds, as a sum a define names and the same sum the record writes
    /// may run over other letters.
    fn alike_as_recorded(&mut self, asked: &Term, recorded: &Term) -> bool {
        let letter = self
            .unheld(&[asked, recorded])
            .map(|v| self.rpn(&v).to_string());
        let asked = self.read_as_recorded(asked, letter.as_deref());
        asked == self.read_as_recorded(recorded, letter.as_deref())
    }

    /// `term` as `alike_as_recorded` compares it: the reason's recorded
    /// defines written out, each sum over `letter` where one is given, in
    /// standard form.
    fn read_as_recorded(&mut self, term: &Term, letter: Option<&str>) -> Rpn {
        let mut out = self.recorded_out(term);
        if let Some(letter) = letter {
            out = self.sums_over(&out, letter);
        }
        let standard = self.standard(&out);
        self.rpn(&standard)
    }

    /// Whether `term` is a product, or a power to a numeral, whose every
    /// part the record says is a positive integer, said once
    /// (`NonzeroBy::Positive`) or read from a line saying it is in ℕ, or is
    /// of numerals alone whose value is a whole number above 0.
    fn positive_by_record(
        &mut self,
        term: &Term,
        recorded: &[NotZero],
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<bool> {
        let kids = term.children();
        let how = (term.variable().is_none()
            && term.label() == Some("co")
            && kids.len() == 3)
            .then(|| self.rpn(&kids[2]).alone().map(String::from))
            .flatten();
        let parts: Vec<&Term> = match how.as_deref() {
            Some("cmul") => vec![&kids[0], &kids[1]],
            Some("cexp") if numerals::value(&kids[1]).is_some() => vec![&kids[0]],
            _ => return Ok(false),
        };
        for part in parts {
            // Numerals alone whose value is a whole number above 0: 3, 2!.
            if matches!(field::closed_value(part), Built(Value::Exact(v)) if v.is_integer() && v.is_positive())
            {
                continue;
            }
            if self.positive_by_record(part, recorded, scope, facts)? {
                continue;
            }
            let part = self.rpn(part);
            let mut positive = false;
            for entry in recorded {
                let natural = match &entry.by {
                    NonzeroBy::Positive { .. } => true,
                    NonzeroBy::Stated { from, .. } => {
                        let from = self.term(from)?;
                        let from = self.to_term(&from);
                        from.label() == Some("wcel")
                            && self.rpn(&from.children()[1]) == t!("cn")
                    }
                    NonzeroBy::Numerals => false,
                };
                if !natural {
                    continue;
                }
                let named = self.term(&entry.term)?;
                if self.asked_of(&part, &named, scope, facts)?.is_some() {
                    positive = true;
                    break;
                }
            }
            if !positive {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// ( scope -> divisor =/= 0 ) from its parts, each by `divisor_apart`:
    /// a product or a quotient by `mulne0d` or `divne0d`, a negation by
    /// `negne0d`, a power to a numeral by `expne0d`, the numeral 0 among
    /// them. A decline for any other divisor, or a part not so.
    pub(super) fn parts_apart(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
    ) -> Checked<Route<Proof>> {
        let term = self.to_term(divisor);
        if term.variable().is_some() {
            return Ok(Route::no("a letter has no parts"));
        }
        let kids: Vec<Rpn> = term.children().iter().map(|c| self.rpn(c)).collect();
        let how = (term.label() == Some("co") && kids.len() == 3)
            .then(|| kids[2].alone().map(String::from))
            .flatten();
        let power = (how.as_deref() == Some("cexp"))
            .then(|| numerals::value(&term.children()[1]))
            .flatten();
        let (lemma, parts): (&str, Vec<&Rpn>) = match (term.label(), how.as_deref()) {
            (Some("cneg"), _) if kids.len() == 1 => ("negne0d", vec![&kids[0]]),
            (_, Some("cmul")) => ("mulne0d", vec![&kids[0], &kids[1]]),
            (_, Some("cdiv")) => ("divne0d", vec![&kids[0], &kids[1]]),
            (_, Some("cexp")) if power.is_some() => ("expne0d", vec![&kids[0]]),
            _ => return Ok(Route::no(
                "the divisor is no product, quotient, negation or power to a numeral",
            )),
        };
        let mut held = Vec::new();
        let mut apart = Vec::new();
        for part in &parts {
            held.push(take!(self.in_cc(part, scope, facts)?));
            apart.push(take!(self.divisor_apart(part, scope, facts, implied)?));
        }
        let mut binds = binds! {"ph" => scope, "A" => parts[0]};
        if let Some(second) = parts.get(1) {
            binds.insert("B".to_string(), (*second).clone());
        }
        let mut hyps: Vec<Proof> = held.into_iter().chain(apart).collect();
        // ( A ^ N ) with N the whole number written, which `expne0d` asks
        // in ℤ.
        if let Some(power) = power {
            let exponent = &kids[1];
            let whole = if power.is_zero() {
                self.b.step("0z")
            } else {
                let natural = numerals::nn(&self.b, power);
                self.b.ap("nnzi", &binds! {"N" => exponent}, &[&natural])
            };
            hyps.push(self.b.ap(
                "a1i",
                &binds! {"ph" => t!(exponent, "cz", "wcel"), "ps" => scope},
                &[&whole],
            ));
            binds.insert("N".to_string(), exponent.clone());
        }
        let hyps: Vec<&Proof> = hyps.iter().collect();
        Ok(Built(self.b.ap(lemma, &binds, &hyps)))
    }

    /// ( scope -> divisor =/= 0 ) for a closed divisor whose value is not
    /// zero, a fact about numerals worked out as `arithmetic` works one out,
    /// which the page says once (`SYNTAX.md`); None for any other.
    pub(super) fn closed_nonzero(
        &mut self,
        divisor: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        if !matches!(field::closed_value(&self.to_term(divisor)), Built(Value::Exact(v)) if !v.is_zero())
        {
            return Ok(None);
        }
        let denial = t!(t!(divisor, "cc0", "wceq"), "wn");
        let worked = match self.prove_numeral(&denial, scope, facts)? {
            Built(p) => Built(p),
            Declined(_) => self.by_values(&denial, scope, facts)?,
        };
        Ok(match worked {
            Built(p) => Some(self.b.ap(
                "neqned",
                &binds! {"ph" => scope, "A" => divisor, "B" => "cc0"},
                &[&p],
            )),
            Declined(_) => None,
        })
    }

    /// What a line among `facts`, or what the step wrote, says makes a term
    /// not zero, or None: the one reading of a line for a divisor's ≠ 0
    /// (`divisor_apart`, stages 2 and 5).
    pub fn written_nonzero(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
        implied: &OnceCell<Vec<Facts>>,
        said: &Rpn,
    ) -> Checked<Option<Proof>> {
        // Written either way round, and as ¬ said = 0 as well (`held`), in
        // a line or in what the step wrote.
        let want = t!(said, "cc0", "wne");
        if let Some(p) = self.held(facts, &want, scope)? {
            return Ok(Some(p));
        }
        if let Some(w) = self.written_held(&want)? {
            if let Some(p) = self.lifted_to(&want, &w.proof, &w.at, scope) {
                return Ok(Some(p));
            }
        }
        // A line saying the term is above zero, or below it, says it is not
        // zero (`gt0ne0d`, `lt0ne0d`), as a reader takes A > 0.
        for (sign, lemma) in [
            (t!("cc0", said, "clt", "wbr"), "gt0ne0d"),
            (t!(said, "cc0", "clt", "wbr"), "lt0ne0d"),
        ] {
            let mut found = self.held(facts, &sign, scope)?;
            if found.is_none() {
                if let Some(w) = self.written_held(&sign)? {
                    found = self.lifted_to(&sign, &w.proof, &w.at, scope);
                }
            }
            if let Some(found) = found {
                return Ok(Some(self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "A" => said},
                    &[&found],
                )));
            }
        }
        // Or a membership written that says it: N ∈ ℕ says N ≠ 0. What each
        // of `facts` also says is worked out once for all the denominators
        // that ask (`take_implied`).
        for more in take_implied(implied, self, scope, facts)? {
            if let Some(p) = self.held(more, &want, scope)? {
                return Ok(Some(p));
            }
        }
        if let Some(p) = self.apart_as_written(said, scope, facts)? {
            return Ok(Some(p));
        }
        // A term is not zero where its negation is not (`negne0bd`): the
        // normaliser writes (−q)/(−p) over p, and the page says −p ∈ ℕ.
        let term = self.to_term(said);
        if term.label() == Some("cneg") {
            return Ok(None);
        }
        let negated = t!(said, "cneg");
        let Some(found) = self.written_nonzero(scope, facts, implied, &negated)? else {
            return Ok(None);
        };
        let Built(number) = self.part(said, &t!("cc"), scope, facts)? else {
            return Ok(None);
        };
        let turned =
            self.b
                .ap("negne0bd", &binds! {"ph" => scope, "A" => said}, &[&number]);
        Ok(Some(self.b.ap(
            "mpbird",
            &binds! {"ph" => scope, "ps" => &want, "ch" => t!(&negated, "cc0", "wne")},
            &[&found, &turned],
        )))
    }

    /// The same fact about the same denominator, spelt as the text spells
    /// it: what decides is the polynomial, and the equation carrying one
    /// spelling to the other is the normalizer's own.
    pub(super) fn apart_as_written(
        &mut self,
        said: &Rpn,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let mut w = Work::plain(scope, facts);
        let labels = self.b.flabel.clone();
        for (fact, proof) in facts.entries() {
            if !fact.ends_with(&["wne"]) && !fact.ends_with(&["wn"]) {
                continue;
            }
            let node = self.to_term(&fact);
            if node.variable().is_some() {
                continue;
            }
            let sides = if node.label() == Some("wn") {
                let inner = node.children()[0].clone();
                if inner.variable().is_some() || inner.label() != Some("wceq") {
                    continue;
                }
                inner.children().to_vec()
            } else {
                node.children().to_vec()
            };
            if sides.len() != 2 {
                continue;
            }
            // The side that is not zero, whichever side the page wrote it on,
            // and the fact read as that side =/= 0 (`held`).
            let (left, right) = (self.rpn(&sides[0]), self.rpn(&sides[1]));
            let subject =
                match (left.alone() == Some("cc0"), right.alone() == Some("cc0")) {
                    (false, true) => sides[0].clone(),
                    (true, false) => sides[1].clone(),
                    _ => continue,
                };
            let was = self.rpn(&subject);
            if was == *said {
                continue;
            }
            let wanted = t!(was, "cc0", "wne");
            let one = Facts::new();
            self.know(&one, fact.clone(), proof.clone());
            let Some(given) = self.held(&one, &wanted, scope)? else {
                continue;
            };
            let Built((items, same)) =
                w.e.normalize(&mut self.ask(&w.spec), &subject, &labels)?
            else {
                continue;
            };
            if Emitter::spell_run(&items) != *said {
                continue;
            }
            return Ok(Some(self.b.ap(
                "eqnetrrd",
                &binds! {"ph" => scope, "A" => &was, "B" => said, "C" => "cc0"},
                &[&same, &given],
            )));
        }
        Ok(None)
    }
}
