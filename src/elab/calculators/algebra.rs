//! Algebra, fields and what is apart from zero.

use std::mem;

use super::*;
use crate::checker::record::{NonzeroBy, NotZero};
use crate::elab::state::Divided;
use crate::methods::algebra::apart_at;

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

    /// Decided by `field`, then proved by `normal`. A step that is not an
    /// identity of the field is refused rather than assumed; what `normal`
    /// does not yet write is taken as stated. Each part the reason divides
    /// by is shown not zero as the checker recorded it (`reason_divided`).
    pub fn algebra(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if let Some(pairs) = pairs::relation(&self.to_term(term)) {
            return self.algebra_pairs(step, &pairs, scope, facts, lines);
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
        let mut found: Route<Proof> = Route::no("nothing to decide bare");
        if let Built(bare) =
            self.identities_written_out(&step.just.refs, &out, scope)?
        {
            // The cited lines are read from the elaborator's own table as
            // well as from the ones handed down, a membership of an atom
            // among them, so the bare lines stand there while they are
            // decided.
            let kept = mem::replace(&mut self.lines, bare.lines.clone());
            let decided = self.field_either_way(
                step,
                &bare.term,
                scope,
                &bare.facts,
                &bare.lines,
            );
            self.lines = kept;
            if let Built(p) = decided? {
                if let Some(back) =
                    self.tidied(&p, &bare.term, &out.term, scope, &out.facts)?
                {
                    found = Built(back);
                }
            }
        }
        let found = match found {
            Built(p) => Built(p),
            Declined(_) => self
                .algebra_written_out(step, &out.term, scope, &out.facts, &out.lines)?,
        };
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
    /// (`METHODS.md`, Pairs): both coordinates' equations, or the
    /// difference at the first coordinate whose difference rescales one
    /// the step cites (`methods::algebra::apart_at`).
    pub(super) fn algebra_pairs(
        &mut self,
        step: &Step,
        pairs: &PairRelation,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        if !pairs.apart {
            let mut proved = Vec::new();
            for at in Coordinate::BOTH {
                let equation = self.rpn(&pairs.equation(at));
                proved.push(take!(self.algebra(step, &equation, scope, facts, lines)?));
            }
            return Ok(Built(
                self.pairs_equal(pairs, scope, &proved[0], &proved[1]),
            ));
        }
        let cited: Vec<Term> = step
            .just
            .refs
            .iter()
            .filter_map(|r| self.line_written(r, lines).map(|l| self.to_term(&l.claim)))
            .collect();
        let labels = self.b.flabel.clone();
        let Some(at) = apart_at(pairs, &cited, &labels) else {
            return Ok(Route::no(
                "no coordinate's difference is a disequality the step cites, rescaled",
            ));
        };
        let denial = self.rpn(&pairs.denial(at));
        let apart = take!(self.algebra(step, &denial, scope, facts, lines)?);
        let members = self.number_members(pairs, scope, facts)?;
        Ok(Built(self.pairs_apart(pairs, scope, at, &apart, &members)))
    }

    /// `prove_field` of the claim, or of the claim turned round: an equation
    /// is one claim either way round, and a route that reaches `b = a`
    /// reaches the claim `a = b` turned (`turned_claim`).
    pub(super) fn field_either_way(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let found = self.prove_field(Some(step), term, scope, facts, lines)?;
        if !found.is_declined() {
            return Ok(found);
        }
        if let Some((turned, flip)) = self.turned_claim(term) {
            if let Built(p) =
                self.prove_field(Some(step), &turned, scope, facts, lines)?
            {
                let Sides { left, right } = self.equation_sides(&turned);
                return Ok(Built(pf!(self.b; scope, left, right, p, flip)));
            }
        }
        Ok(found)
    }

    /// `algebra` over a claim and lines whose defined names are written out.
    pub(super) fn algebra_written_out(
        &mut self,
        step: &Step,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let found = self.field_either_way(step, term, scope, facts, lines)?;
        if let Declined(d) = &found {
            // Decided but not written is a gap in the method, and nothing is
            // taken in its place: the build stops here.
            return Err(self.defect(
                step.line,
                format!(
                    "step {} is an identity, and algebra cannot write its proof: {}",
                    step.number,
                    self.say(d)
                ),
            ));
        }
        Ok(found)
    }

    /// An `algebra` claim, by whichever of the routes reaches it, in the
    /// order they cost; refused in the words of every route that declined.
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
        let out = field::reading_sums(linear, || {
            self.field_proved(step, term, scope, facts, lines)
        });
        self.sum_letter = kept;
        out
    }

    pub(super) fn field_proved(
        &mut self,
        step: Option<&Step>,
        term: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Route<Proof>> {
        let goal = self.to_term(term);
        let apart = goal.variable().is_none()
            && goal.label() == Some("wn")
            && goal.children().len() == 1;
        if !apart
            && (goal.variable().is_some()
                || goal.label() != Some("wceq")
                || goal.children().len() != 2)
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
        if apart {
            return self.apart_from_cited(step, &goal, scope, &facts, lines, &mut w);
        }
        let left = self.rpn(&goal.children()[0]);
        let right = self.rpn(&goal.children()[1]);
        // Each route's decline, written out only if every route declines.
        let mut declines = Vec::new();
        let found = self.same_polynomial(&mut w, &left, &right)?;
        match found {
            Built(p) => return Ok(Built(p)),
            Declined(d) => declines.push(d),
        }
        if let Some(step) = step {
            for route in 0..3 {
                let found = match route {
                    0 => self.scaled_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                    1 => self.crossed_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                    _ => self.summed_from_cited(
                        step, &left, &right, scope, &facts, lines, &mut w,
                    )?,
                };
                match found {
                    Built(p) => return Ok(Built(p)),
                    Declined(d) => declines.push(d),
                }
            }
        }
        let said: Vec<String> = declines.iter().map(|d| self.say(d)).collect();
        Ok(Route::no(said.join("; ")))
    }

    /// A disequality that is a cited one rescaled: the cited fact becomes a
    /// difference that is not zero, the two differences are shown to be one
    /// polynomial, and the claim's difference is not zero either, the cited
    /// difference multiplied by any rational other than 0 (`METHODS.md`).
    pub(super) fn apart_from_cited(
        &mut self,
        step: Option<&Step>,
        goal: &Term,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let Some(step) = step else {
            return Ok(Route::no("a disequality needs the step it cites"));
        };
        let labels = self.b.flabel.clone();
        let claim = field::denied(goal, &labels);
        let inner = goal.children()[0].clone();
        let (lhs, rhs) = (
            self.rpn(&inner.children()[0]),
            self.rpn(&inner.children()[1]),
        );
        let whole = t!(lhs, rhs, "cmin", "co");
        for r in &step.just.refs {
            for said in self.line_writes(r, lines) {
                let node = self.to_term(&said);
                let cited = field::denied(&node, &labels);
                let Some(numerators) = rescales(cited.as_ref(), claim.as_ref()) else {
                    continue;
                };
                let pair = node.children()[0].clone();
                let (p, qq) =
                    (self.rpn(&pair.children()[0]), self.rpn(&pair.children()[1]));
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
                    (Some(theirs), Some(ours)) if !ours.is_zero() => {
                        numerators * theirs / ours
                    }
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
                    let what = format!(
                        "the scale {} of step {}",
                        self.render(&times),
                        step.number
                    );
                    let apart_from_zero = t!(times, "cc0", "wne");
                    let nonzero = self.closed_fact(
                        &apart_from_zero,
                        scope,
                        facts,
                        &what,
                        Some(step),
                    )?;
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
                return Ok(Built(self.b.ap(
                    "neneqd",
                    &binds! {"ph" => scope, "A" => &lhs, "B" => &rhs},
                    &[&differ],
                )));
            }
        }
        Ok(Route::no("no cited disequality is the claim rescaled"))
    }

    /// A claim the cited equation already is, once its division goes:
    /// `divmuleq` is the step between them.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn crossed_from_cited(
        &mut self,
        step: &Step,
        left: &Rpn,
        right: &Rpn,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
        w: &mut Work,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let want = field::equation(&self.to_term(&t!(left, right, "wceq")), &labels);
        for r in &step.just.refs {
            // A line saying several things is read a sentence at a time, as
            // any line a step cites is.
            for part in self.line_writes(r, lines) {
                let cited = self.to_term(&part);
                if cited.variable().is_some()
                    || cited.label() != Some("wceq")
                    || cited.children().len() != 2
                {
                    continue;
                }
                let mine = field::equation(&cited, &labels);
                match (&want, &mine) {
                    (Some(want), Some(mine)) if mine == want => {}
                    _ => continue,
                }
                let Built(given) = self.cited_fact(r, &cited, scope, facts, lines)?
                else {
                    continue;
                };
                let found = self.cleared(w, &cited, left, right, given)?;
                if !found.is_declined() {
                    return Ok(found);
                }
            }
        }
        Ok(Route::no("no cited equation is the claim divided"))
    }

    /// The cited equation with its denominators multiplied out.
    pub(super) fn cleared(
        &mut self,
        w: &mut Work,
        cited: &Term,
        left: &Rpn,
        right: &Rpn,
        given: Proof,
    ) -> Checked<Route<Proof>> {
        let labels = self.b.flabel.clone();
        let was: Vec<Rpn> = cited.children().iter().map(|c| self.rpn(c)).collect();
        let mut quotients = Vec::new();
        for (side, said) in cited.children().iter().zip(&was) {
            let Quotiented { over, under, proof } =
                take!(w
                    .e
                    .normalize_quotient(&mut self.ask(&w.spec), side, &labels)?);
            quotients.push(w.e.as_quotient(
                &mut self.ask(&w.spec),
                over,
                under,
                proof,
                said,
            )?);
        }
        let (below, beneath, second) = quotients.pop().unwrap();
        let (over, under, first) = quotients.pop().unwrap();
        let (a, b) = (Emitter::spell_run(&over), Emitter::spell_run(&under));
        let (c, d) = (Emitter::spell_run(&below), Emitter::spell_run(&beneath));
        let p1 = w.e.pair_of(&mut self.ask(&w.spec), &under)?;
        let p2 = w.e.pair_of(&mut self.ask(&w.spec), &beneath)?;
        let (p1, p2) = (take!(p1), take!(p2));
        let u = w.spec.scope.clone();
        let rc1 = w.e.run_cc(&mut self.ask(&w.spec), &over)?;
        let rc2 = w.e.run_cc(&mut self.ask(&w.spec), &below)?;
        let quotient = t!(t!(a, b, "cdiv", "co"), t!(c, d, "cdiv", "co"), "wceq");
        let crossed_eq = t!(t!(a, d, "cmul", "co"), t!(c, b, "cmul", "co"), "wceq");
        let matched = self.b.ap(
            "3eqtr3d",
            &binds! {"ph" => &u, "A" => &was[0], "B" => &was[1], "C" => t!(a, b, "cdiv", "co"), "D" => t!(c, d, "cdiv", "co")},
            &[&given, &first, &second],
        );
        let tops = self.b.ap("jca", &binds! {"ph" => &u, "ps" => t!(a, "cc", "wcel"), "ch" => t!(c, "cc", "wcel")}, &[&rc1, &rc2]);
        let pair = |x: &Rpn| t!(t!(x, "cc", "wcel"), t!(x, "cc0", "wne"), "wa");
        let bottoms = self.b.ap(
            "jca",
            &binds! {"ph" => &u, "ps" => pair(&b), "ch" => pair(&d)},
            &[&p1, &p2],
        );
        let law = self.b.ap(
            "divmuleq",
            &binds! {"A" => &a, "B" => &c, "C" => &b, "D" => &d},
            &[],
        );
        let turn = self.b.ap(
            "syl2anc",
            &binds! {"ph" => &u, "ps" => t!(t!(a, "cc", "wcel"), t!(c, "cc", "wcel"), "wa"),
            "ch" => t!(pair(&b), pair(&d), "wa"), "th" => t!(quotient, crossed_eq, "wb")},
            &[&tops, &bottoms, &law],
        );
        let crossed = self.b.ap(
            "mpbid",
            &binds! {"ph" => &u, "ps" => &quotient, "ch" => &crossed_eq},
            &[&matched, &turn],
        );
        // The claim and the crossed equation are one polynomial, which says
        // their differences agree and not their sides: (H(b) − H(a))·1 =
        // 0·(b − a) carries H(b) = H(a) with each side split otherwise.
        let facts = w.spec.facts.clone();
        let (p, q) = (t!(a, d, "cmul", "co"), t!(c, b, "cmul", "co"));
        let p_cc = self.in_cc(&p, &u, &facts)?;
        let gap = t!(p, q, "cmin", "co");
        let whole = t!(left, right, "cmin", "co");
        let alike = self.same_polynomial(w, &gap, &whole)?;
        let left_cc = self.in_cc(left, &u, &facts)?;
        let right_cc = self.in_cc(right, &u, &facts)?;
        let (p_cc, alike, left_cc, right_cc) =
            (take!(p_cc), take!(alike), take!(left_cc), take!(right_cc));
        let vanishes = self.b.ap(
            "subeq0bd",
            &binds! {"ph" => &u, "A" => &p, "B" => &q},
            &[&p_cc, &crossed],
        );
        let reached = self.b.ap(
            "eqtr3d",
            &binds! {"ph" => &u, "A" => &gap, "B" => &whole, "C" => "cc0"},
            &[&alike, &vanishes],
        );
        let turn = self.b.ap(
            "subeq0ad",
            &binds! {"ph" => &u, "A" => left, "B" => right},
            &[&left_cc, &right_cc],
        );
        Ok(Built(self.b.ap(
            "mpbid",
            &binds! {"ph" => &u, "ps" => t!(whole, "cc0", "wceq"), "ch" => t!(left, right, "wceq")},
            &[&reached, &turn],
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
                NonzeroBy::Positive => self.positive_divisor(&shown, scope, facts)?,
                // The line the record names, held among the facts a membership
                // is answered from and the lines the page writes alike.
                NonzeroBy::Stated { from, .. } => {
                    let from = self.term(from)?;
                    let lines = match &divided.written {
                        Some(written) => facts.with(written),
                        None => facts.copy(),
                    };
                    // The line is held among those, or among what the step
                    // wrote, its requires lines (`written_held`).
                    let mut said = self.held(&lines, &from, scope)?;
                    if said.is_none() {
                        if let Some(w) = self.written_held(&from)? {
                            said = self.lifted_to(&from, &w.proof, &w.at, scope);
                        }
                    }
                    // That line alone says the divisor is not zero, with the
                    // memberships in hand for carrying it to the spelling
                    // asked.
                    match said {
                        Some(said) => {
                            let only = facts.filtered(|c, _| c.ends_with(&["wcel"]));
                            self.know(&only, from, said);
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

    /// How a divisor asked is the page's term `named` the record names, or
    /// None where it is not: the same term in standard form, |BO| asked of
    /// |OB|; or the normaliser's spelling of it, 1·x¹ + 3·1 asked of x + 3,
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
        let standard = |me: &mut Self, d: &Rpn| {
            let s = me.standard(&me.to_term(d));
            me.rpn(&s)
        };
        if standard(self, divisor) == standard(self, named) {
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
                    NonzeroBy::Positive => true,
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
