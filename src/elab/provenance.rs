//! The proof rules: what a step's proof may rest on.
//!
//! This is the sixth of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given a finished step's proof and what the step
//! names, it refuses a proof the build made that rests on anything the step
//! does not name (R1), and a `requires` line whose proof does not come from
//! its reason (R2). Whether the step uses everything it names is the
//! checker's to say.
//!
//! A proof carries its `origin`, the page items it rests on. `seal` makes a
//! proof stand for one item from then on.

use std::collections::BTreeSet;

use super::state::{number_of, Elaborator};
use super::Facts;
use crate::corpus::proof::Requires;
use crate::corpus::{Head, Item, Method, Step};
use crate::formula::Node;
use crate::mm::spell::Proof;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup};
use crate::targets;
use crate::{pf, t, take};

pub const REQUIRES: &str = "requires@";

/// What a letter's membership in a number system is called as the origin of
/// a proof (`Elaborator::introduced_membership`): the page says it once, on
/// the line introducing the letter, and a step rests on it without naming
/// that line.
pub const MEMBERSHIP: &str = "membership@";

/// Whether a proof resting on `origin` may be offered where a proof may rest
/// on `resting`: what it names, and a membership the page says once.
pub fn may_rest_on(resting: &BTreeSet<String>, origin: &str) -> bool {
    resting.contains(origin) || origin.starts_with(MEMBERSHIP)
}

/// What a `requires` line is called as the origin of a proof: it has no
/// number of its own, so it is named by where it stands.
pub fn requirement(line: usize) -> String {
    format!("{REQUIRES}{line}")
}

/// Whether a `requires` line made this proof.
pub fn from_requires(proof: &Proof) -> bool {
    proof.origin.iter().any(|o| o.starts_with(REQUIRES))
}

/// Whether a proof rests on exactly one item, and that one.
/// What a requires line may not rest on: what it and the lines below it
/// made, which a pass made before this one may hold. A line rests only on
/// those above it (R2), and its own earlier proof would hide the line it
/// names.
fn not_above(step: &Step, req: &Requires) -> BTreeSet<String> {
    step.requires
        .iter()
        .skip_while(|o| o.line != req.line)
        .map(|o| requirement(o.line))
        .collect()
}

pub fn rests_on_only(proof: &Proof, item: &str) -> bool {
    proof.origin.len() == 1
        && proof.origin.iter().next().map(String::as_str) == Some(item)
}

impl<'a> Elaborator<'a> {
    /// What a step names, which is everything its proof may rest on: the
    /// lines it cites, its own requires lines, and the sorts in scope. A block
    /// also rests on its own steps and on what it assumes, and on the lines a
    /// `join` inside it names.
    pub fn named(&self, step: &Step, number: &str, block: bool) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = step.just.refs.iter().cloned().collect();
        // The line a step contradicts is one it rests on, where it ends a
        // case that cannot occur.
        out.extend(step.just.contradicting.iter().cloned());
        out.extend(self.sorts.iter().cloned());
        out.extend(step.requires.iter().map(|r| requirement(r.line)));
        // A theorem of this file stated over the file's defines is read with
        // them, and the step rests on them through it (`sorts::stated_over`).
        if let Some(cited) = step.just.cited_item() {
            let full = self.thm.names.full(&cited);
            out.extend(crate::sorts::stated_over(self.thm, self.scopes, &full));
        }
        if block {
            let prefix = format!("{number}.");
            out.extend(
                self.lines
                    .keys()
                    .into_iter()
                    .filter(|k| k.starts_with(&prefix)),
            );
            // A step's requires lines are the block's as the step is: the
            // last step of a part says there what the part's end asks, an
            // identity element's operand a number (`SYNTAX.md`).
            out.extend(
                self.thm
                    .steps
                    .iter()
                    .filter(|s| number_of(s).starts_with(&prefix))
                    .flat_map(|s| s.requires.iter().map(|r| requirement(r.line))),
            );
            out.extend(
                step.openers
                    .iter()
                    .filter(|o| !o.label.is_empty())
                    .map(|o| o.label.clone()),
            );
            out.insert(format!("{number} assumes"));
            // A define inside the block is the block's own, as its openers
            // are: it comes after the block's first line and before its last
            // step.
            let last = self
                .thm
                .steps
                .iter()
                .filter(|s| number_of(s).starts_with(&prefix))
                .map(|s| s.line)
                .max();
            if let Some(last) = last {
                out.extend(
                    self.thm
                        .defines
                        .iter()
                        .filter(|d| step.line < d.line && d.line < last)
                        .map(|d| d.label.clone()),
                );
            }
            let depth = number.matches('.').count() + 1;
            for inner in &self.thm.steps {
                let name = number_of(inner);
                if !name.starts_with(&prefix) || name.matches('.').count() != depth {
                    continue;
                }
                if inner.just.head.is(Method::Join) {
                    out.extend(inner.just.refs.iter().cloned());
                }
                // A block closed on a contradiction rests on the line its
                // last step contradicts.
                out.extend(inner.just.contradicting.iter().cloned());
            }
        }
        out
    }

    /// What the lines `refs` name say, held as those lines proved it where
    /// the proof held rests on something outside `resting`: a step or a
    /// requires line rests only on what it names (`rests_on_named`), so a
    /// claim another line said too is found as the line named gave it. A
    /// proof it may rest on, a sort's among them, stays.
    pub fn named_first(
        &mut self,
        refs: &[String],
        resting: &BTreeSet<String>,
        facts: &Facts,
    ) {
        for r in refs {
            for (claim, proof) in facts.of_line(r) {
                let usable = facts.proof(&claim).is_some_and(|held| {
                    held.origin.iter().all(|o| may_rest_on(resting, o))
                });
                if !usable {
                    self.know(facts, claim, proof);
                }
            }
        }
    }

    /// A requires line's proof, checked against its reason and sealed: it
    /// rests only on the lines its reason cites, the step's requires lines
    /// above it, and the sorts in scope.
    pub fn discharged_by(
        &mut self,
        made: Proof,
        step: &Step,
        req: &Requires,
    ) -> Checked<Proof> {
        let allowed = self.reason_allows(step, req);
        self.rests_on_named(&made, &allowed, req.line, "the requires line")?;
        Ok(self.seal(made, &requirement(req.line)))
    }

    /// What the requires line `req` may rest on (R2): what its reason
    /// cites, the sorts, and the requires lines above it; and itself, as a
    /// line already proved and found again is sealed with its own name.
    pub fn reason_allows(&self, step: &Step, req: &Requires) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = req.refs().iter().cloned().collect();
        out.extend(self.sorts.iter().cloned());
        out.extend(step.requires_above(req.line).map(|r| requirement(r.line)));
        out.insert(requirement(req.line));
        out
    }

    /// A proof resting on nothing its line does not name, or a defect.
    ///
    /// `GOALS.md` decision 9: the kernel proof is derived from the text, so
    /// what it rests on is what the text says it rests on. A proof that
    /// verifies while resting on something else says nothing is wrong, and
    /// this is where that is said.
    pub fn rests_on_named(
        &self,
        proof: &Proof,
        allowed: &BTreeSet<String>,
        line: usize,
        what: &str,
    ) -> Checked<()> {
        // A letter's membership is said where the letter is introduced, and
        // every line rests on it unnamed (`introduced_membership`).
        let extra: Vec<&String> = proof
            .origin
            .iter()
            .filter(|o| !allowed.contains(*o) && !o.starts_with(MEMBERSHIP))
            .collect();
        if extra.is_empty() {
            return Ok(());
        }
        let shown: Vec<String> = extra
            .iter()
            .map(|e| match e.strip_prefix(REQUIRES) {
                Some(at) => format!("the requires line at {at}"),
                None => e.to_string(),
            })
            .collect();
        Err(self.defect(
            line,
            format!(
                "{what} rests on {}, which it does not name",
                shown.join(", ")
            ),
        ))
    }

    /// The proof, standing from here on for one thing on the page.
    pub fn seal(&mut self, proof: Proof, item: &str) -> Proof {
        Proof {
            items: proof.items,
            origin: std::iter::once(item.to_string()).collect(),
        }
    }

    /// The letter a step's claim says "for all" of, as the page writes it,
    /// and the kernel name it is bound to; None for any other claim. A step
    /// said of every member is proved at one, and its requires lines speak
    /// of that member by this letter.
    pub fn member_letter(&mut self, step: &Step) -> Checked<Option<(String, String)>> {
        let said = step.claim.sentences();
        let [sentence] = said.as_slice() else {
            return Ok(None);
        };
        let node = self.read(sentence)?;
        let universals = &self.item_library().ctx.universals;
        if !universals.contains(&node.notation()) || !node.children[0].is_name() {
            return Ok(None);
        }
        let said = self.term(&node)?;
        let term = self.to_term(&said);
        if term.variable().is_some() || term.label() != Some("wral") {
            return Ok(None);
        }
        let kernel = format!("{} cv", self.rpn(&term.children()[1]));
        Ok(Some((node.children[0].text.to_string(), kernel)))
    }

    /// A step's finished proof, sealed: it rests on nothing the step does
    /// not name (R1), and from here on the proof stands for the step's
    /// number.
    pub fn check_step(
        &mut self,
        proof: Proof,
        step: &Step,
        number: &str,
        block: bool,
    ) -> Checked<Proof> {
        let allowed = self.named(step, number, block);
        self.rests_on_named(&proof, &allowed, step.line, &format!("step {number}"))?;
        Ok(self.seal(proof, number))
    }

    /// Run `f` with the search offered only facts resting on `allowed`.
    ///
    /// The scope holds more, and a side condition answered from a line the
    /// step does not name is one R1 refuses afterwards.
    pub fn resting_on<T>(
        &mut self,
        allowed: Option<BTreeSet<String>>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        if self.whole_scope {
            return f(self);
        }
        let kept = std::mem::replace(&mut self.resting, allowed);
        let out = f(self);
        self.resting = kept;
        out
    }

    /// The page items a scope is the conjunction of.
    pub fn scope_origin(
        &mut self,
        scope: &str,
        facts: &Facts,
    ) -> Checked<BTreeSet<String>> {
        let mut out = BTreeSet::new();
        let mut todo = vec![scope.to_string()];
        while let Some(one) = todo.pop() {
            if let Some(held) = self.held(facts, &one, scope)? {
                if !held.origin.is_empty() {
                    out.extend(held.origin.iter().cloned());
                    continue;
                }
            }
            let node = self.to_term(&one);
            if node.variable().is_none()
                && node.label() == Some("wa")
                && node.children().len() == 2
            {
                todo.extend(node.children().iter().map(|c| self.rpn(c)));
            }
        }
        Ok(out)
    }

    /// The facts a step's own `requires` lines put within reach, proved once
    /// in the order the step writes them and offered alongside what the scope
    /// holds.
    ///
    /// A requires line rests on the lines written above it (`SYNTAX.md`), and
    /// each is proved with those in hand. A line naming an item is that item
    /// cited, and citing it asks the step for its requires lines; asked while
    /// one is being proved, the answer is what that line was given, so no
    /// line below it is proved first.
    pub fn supplied(
        &mut self,
        step: Option<&Step>,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Facts> {
        let known = facts.copy();
        let Some(step) = step else {
            return Ok(known);
        };
        if !self.supplying.is_empty() {
            return Ok(known);
        }
        for r in &step.requires {
            let want = self.read_one(&r.fact)?;
            let term = self.term(&want)?;
            // A claim the scope already holds is taken as it stands only
            // where this line's own reason made that proof.
            let mut given = known.clone();
            if let Some(held) = self.held(&known, &term, scope)? {
                if held.origin.contains(&requirement(r.line)) {
                    continue;
                }
                if !self.rests_on_lines(r) {
                    // The claim however it is spelt: each fact with its
                    // standard form is the claim. A line the reason cites
                    // that says it is still that line, as the scope carries
                    // it (`filtered_claims`).
                    let key = self.fact_key(&term);
                    let same = known.under(&key);
                    given = known.filtered_claims(|k, _| !same.iter().any(|s| s == k));
                }
            }
            let not_above = not_above(step, r);
            let unbelow = |v: &Proof| !v.origin.iter().any(|o| not_above.contains(o));
            let given = given.filtered(|_, v| unbelow(v));
            let resting = self.reason_allows(step, r);
            self.named_first(r.refs(), &resting, &given);
            let written = self.written.clone();
            self.written = self.written.filtered(unbelow);
            self.supplying.insert(term.clone());
            let made = self.side(&want, r, scope, &given, Some(step));
            self.supplying.shift_remove(&term);
            self.written = written;
            let made = match made? {
                Built(p) => self.discharged_by(p, step, r)?,
                Declined(d) => panic!(
                    "the requires line at {} declined where it is proved: {}",
                    r.line,
                    self.say(&d)
                ),
            };
            // Turned as well: a line of the scope saying it held it both
            // ways round, and the step takes this line's proof either way.
            self.know_turned(&known, &term, &made, scope);
            // What the line's membership implies is the line's too, proved
            // last, so that the step takes it over a line of the scope that
            // says the same: |A| ∈ ℂ from `requires |A| ∈ ℝ`, not from a
            // line saying |A| ∈ ℕ that the step does not name.
            let implied = self.implied(&term, &made, scope, &known)?;
            for (said, proof) in implied.entries() {
                self.know(&known, said, proof);
            }
            // A line saying several sentences says each of them, as a line
            // the step cites does.
            self.know_conjuncts(&known, &term, &made, scope);
            self.know(&known, term, made);
        }
        Ok(known)
    }

    /// The facts the proof being built may rest on (`resting_on`): those
    /// whose every origin is a line it names, a requires line, or a
    /// membership said once. All of them where nothing restricts it.
    pub fn restable(&self, facts: &Facts) -> Facts {
        match &self.resting {
            Some(resting) => {
                facts.filtered(|_, v| v.origin.iter().all(|o| may_rest_on(resting, o)))
            }
            None => facts.clone(),
        }
    }

    /// Whether a `requires` line's reason is the lines it cites: `from H1`
    /// is, and so is a definition the database gives no target for, which the
    /// notation folds into the line it is unfolded at.
    pub fn rests_on_lines(&self, req: &Requires) -> bool {
        if req.is_lines() {
            return true;
        }
        let Ok(Head::Item { cited, .. }) = req.by().map(|by| &by.head) else {
            return false;
        };
        let full = self.thm.names.full(cited);
        // A definition with no lemma, or whose lemma is `biid`, says one
        // formula two ways: its notations' targets make the sides the same,
        // so it is unfolded where a line says it.
        match self.items.get(&full) {
            Some(Item::Record(r)) => {
                let clauses = targets::clauses(r);
                r.kind.unfolds() && (clauses.is_empty() || clauses == ["biid"])
            }
            _ => false,
        }
    }

    /// A sentence as the page writes it: a membership of a power set is the
    /// part `let X ⊆ A` writes, and every other sentence is written as it is
    /// read.
    fn as_written(&self, said: &str) -> String {
        let node = self.to_term(said);
        if node.label() == Some("wcel") && node.children().len() == 2 {
            let power = &node.children()[1];
            if power.label() == Some("cpw") && power.children().len() == 1 {
                return t!(
                    self.rpn(&node.children()[0]),
                    self.rpn(&power.children()[0]),
                    "wss"
                );
            }
        }
        said.to_string()
    }

    /// What a line said of every member of a set says at a member the facts
    /// place in that set, taken apart as the line itself is: `requires s(x) ∈
    /// ℕ₀: from 5`, where line 5 says for all x ∈ ℚ, s(x) ∈ ℕ₀ and more, at x
    /// ∈ ℚ. None where no member gives `term`.
    fn part_at_a_member(
        &mut self,
        said: &str,
        whole: &Proof,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Option<Proof>> {
        let line = self.to_term(said);
        let (body, letter, domain) = (
            line.children()[0].clone(),
            self.rpn(&line.children()[1]),
            self.rpn(&line.children()[2]),
        );
        let mark = format!("{letter} cv");
        for (member, inside) in facts.entries() {
            let m = self.to_term(&member);
            if m.variable().is_some()
                || m.label() != Some("wcel")
                || self.rpn(&m.children()[1]) != domain
            {
                continue;
            }
            let at = self.rpn(&m.children()[0]);
            // A membership the page says once is taken from where it says
            // it, so the line rests on no let it does not name.
            let inside = match self.said_once_proof(&m, scope, facts)? {
                Built(p) => p,
                Declined(_) => inside,
            };
            let instance = self.rpn(&self.restated(&body, &mark, &at));
            let held = Facts::new();
            self.know(&held, said, whole.clone());
            self.know(&held, member.clone(), inside);
            let Some(p) = self.instance_of_universal(&instance, scope, &held)? else {
                continue;
            };
            let parts = Facts::new();
            self.know(&parts, instance.clone(), p.clone());
            self.unpack_all(&instance, &p, scope, &parts);
            if let Some(found) = self.held(&parts, term, scope)? {
                return Ok(Some(found));
            }
        }
        Ok(None)
    }

    /// A "for all" over a set inside the one a line's "for all" is over: a
    /// line said of every member of a set says it of every member of a set
    /// inside that one (`SYNTAX.md`). Each member of the claim's set is
    /// fixed, shown a member of the line's (`within`, by the table the
    /// checker reads), and the line taken at it (`part_at_a_member`).
    fn narrowed(
        &mut self,
        said: &str,
        whole: &Proof,
        term: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let want = self.to_term(term);
        if want.label() != Some("wral") {
            return Ok(Route::no("the claim is not \"for all\""));
        }
        let domain = self.rpn(&self.to_term(said).children()[2]);
        let over = want.children()[2].clone();
        if self.rpn(&over) == domain {
            return Ok(Route::no("the claim is over the line's own set"));
        }
        let held = facts.copy();
        self.know(&held, said.to_string(), whole.clone());
        let (body, variable) = (want.children()[0].clone(), want.children()[1].clone());
        let over_rpn = self.rpn(&over);
        self.for_every(
            scope,
            &held,
            &body,
            &variable,
            &over,
            &mut |me, claim, inner, lifted| {
                // The member `for_every` fixed, under whatever letter it chose.
                let fixed = lifted.entries().into_iter().find_map(|(k, _)| {
                    let m = me.to_term(&k);
                    (m.label() == Some("wcel")
                        && m.children()[0].label() == Some("cv")
                        && me.rpn(&m.children()[1]) == over_rpn)
                        .then(|| me.rpn(&m.children()[0]))
                });
                let Some(at) = fixed else {
                    return Ok(Route::no("no member of the claim's set is fixed"));
                };
                let inside = take!(me.within(&at, &domain, inner, lifted, 3)?);
                let Some(line) = me.held(lifted, said, inner)? else {
                    return Ok(Route::no(
                        "the line does not hold where the member is fixed",
                    ));
                };
                let there = lifted.copy();
                me.know(&there, t!(at, domain, "wcel"), inside);
                let claim = me.rpn(claim);
                match me.part_at_a_member(said, &line, &claim, inner, &there)? {
                    Some(p) => Ok(Built(p)),
                    None => {
                        Ok(Route::no("the line taken at the member is not the claim"))
                    }
                }
            },
            false,
        )
    }

    /// What a line a `requires` line names says, taken apart: a definition
    /// the database gives no target for is one the notation folds away, so
    /// the unfolding is the line itself, and a `from H1` reason asks the same
    /// of the line it names. With `above`, a requires line written above
    /// this one is such a line too.
    pub fn unfolded_at(
        &mut self,
        term: &str,
        scope: &str,
        facts: &Facts,
        refs: &[String],
        above: bool,
    ) -> Checked<Route<Proof>> {
        if above {
            for (said, proof) in facts.entries() {
                if proof.origin.is_empty()
                    || !proof.origin.iter().all(|o| o.starts_with(REQUIRES))
                {
                    continue;
                }
                let held = Facts::new();
                self.know(&held, said.clone(), proof.clone());
                self.unpack_all(&said, &proof, scope, &held);
                if let Some(p) = self.held(&held, term, scope)? {
                    return Ok(Built(p));
                }
            }
        }
        for r in refs {
            let Some(line) = self.lines.get(r) else {
                continue;
            };
            // The line states the fact where one of its sentences, as the
            // page writes it, is the fact; how the kernel spells the two is
            // then the elaborator's to bridge. A line keeps each sentence as
            // the page writes it, but for a let, which keeps the formula it
            // is read as, and `let X ⊆ A` is read as X ∈ 𝒫A.
            let mut says_it = false;
            for s in &line.sentences {
                let said = self.term(s)?;
                if self.as_written(&said) == term {
                    says_it = true;
                }
            }
            let held = Facts::new();
            let lines = self.lines.clone();
            let whole = self.carried(r, facts, &lines);
            self.know(&held, line.term.clone(), whole.clone());
            self.unpack_all(&line.term, &whole, scope, &held);
            if let Some(p) = self.held(&held, term, scope)? {
                return Ok(Built(p));
            }
            // Or what a membership it states says as well: `let k ∈ ℕ` says
            // k ∈ ℝ and k ≠ 0, each one lemma from it.
            let stated = held.copy();
            for (said, proof) in facts.entries() {
                if rests_on_only(&proof, r) {
                    self.know_default(&stated, said, proof);
                }
            }
            for (said, proof) in stated.entries() {
                let more = self.implied(&said, &proof, scope, facts)?;
                if let Some(p) = self.held(&more, term, scope)? {
                    return Ok(Built(p));
                }
                if !says_it {
                    continue;
                }
                let (was, now) = (self.to_term(&said), self.to_term(term));
                if let Built(across) = self.same(&was, &now, scope, facts, None)? {
                    return Ok(Built(
                        pf!(self.b; scope, said, term, proof, across, "mpbid"),
                    ));
                }
            }
            // The line with its own letters bound: one claim, spelt apart.
            let label = self.to_term(&line.term).label().unwrap_or("").to_string();
            if lookup(rules::BOUND, &label).is_some() {
                if let Some(spelt) = self.respelt(&whole, &line.term, term, scope)? {
                    return Ok(Built(spelt));
                }
            }
            if label == "wral" {
                if let Some(p) =
                    self.part_at_a_member(&line.term, &whole, term, scope, facts)?
                {
                    return Ok(Built(p));
                }
                if let Built(p) =
                    self.narrowed(&line.term, &whole, term, scope, facts)?
                {
                    return Ok(Built(p));
                }
            }
            // What the line says beyond its recorded term: an obtain records
            // the body it obtained, and the name's domain went into the scope
            // with the line as its origin.
            if let Some(found) = self.held(facts, term, scope)? {
                if rests_on_only(&found, r) {
                    return Ok(Built(found));
                }
            }
        }
        // What two of the lines say together: a function's type and a
        // membership of its domain put its value there in its codomain.
        let wanted = self.to_term(term);
        if wanted.label() == Some("wcel") && wanted.children().len() == 2 {
            let (value, system) = (
                self.rpn(&wanted.children()[0]),
                self.rpn(&wanted.children()[1]),
            );
            if lookup(rules::SYSTEMS, &system).is_some() {
                if let Some(p) = self.function_value(&value, &system, scope, facts)? {
                    return Ok(Built(p));
                }
            }
        }
        Ok(Route::no("no line this names says it"))
    }

    /// A proof of what one `requires` line asks for.
    ///
    /// While the line is proved, what it cites is what may be carried without
    /// a search, and what the search is offered is what the line may rest on.
    pub fn side(
        &mut self,
        want: &Node,
        req: &Requires,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let citing =
            std::mem::replace(&mut self.citing, req.refs().iter().cloned().collect());
        let allowed = step.map(|s| self.reason_allows(s, req));
        let out = self.resting_on(allowed, |me| {
            me.by_its_reason(want, Some(req), scope, facts, step)
        });
        self.citing = citing;
        out
    }

    /// `side`, with what the line cites in hand.
    fn by_its_reason(
        &mut self,
        want: &Node,
        req: Option<&Requires>,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let how = req.map_or("", |r| r.how.as_str());
        let term = self.term(want)?;
        let refs: Vec<String> = req.map_or(Vec::new(), |r| r.refs().to_vec());
        // A define gives its function on the domain it names, which is proved
        // as it is for a step citing the define.
        let whole = self.to_term(&term);
        // The theorem's own defines, and those above it in its file or
        // imported, by the label each is held under (`outside_label`).
        let outside: Vec<String> = self
            .visible_outside()
            .into_iter()
            .map(|(name, d, src)| self.outside_label(&name, &d, src))
            .collect();
        let defines = || {
            refs.iter().all(|r| {
                self.thm.defines.iter().any(|d| &d.label == r) || outside.contains(r)
            })
        };
        if whole.label() == Some("wfn") && refs.len() == 1 && defines() {
            return match self.define_on(&whole, scope, facts)? {
                Built(p) => Ok(Built(p)),
                Declined(d) => Err(self.defect(
                    self.at,
                    format!(
                        "{} does not give {}: {}",
                        str::trim(how),
                        self.render(&term),
                        self.say(&d)
                    ),
                )),
            };
        }
        // Read from the lines it cites before the scope is asked, since the
        // scope may hold the same claim for another reason.
        if req.is_some_and(|r| self.rests_on_lines(r)) {
            // A definition folded into the line it is unfolded at may be
            // unfolded at a requires line above this one, which the line
            // rests on as it rests on a cited one (R2). A reason that is only
            // `from` names its lines, and is read from those.
            let above = !req.is_some_and(Requires::is_lines);
            if let Built(p) = self.unfolded_at(&term, scope, facts, &refs, above)? {
                return Ok(Built(p));
            }
            // A membership the lines give together is built from them as
            // `membership` builds one, which the checker reads a bare `from`
            // as giving: (k + 1)! ∈ ℝ from k! ∈ ℕ and (k + 1)! = k!·(k + 1),
            // c·gcd(a, b) ∈ ℤ from gcd(a, b) ∈ ℕ. What it may rest on is
            // the line's reason, as `side` offers it.
            let in_system = whole.variable().is_none()
                && whole.label() == Some("wcel")
                && lookup(rules::SYSTEMS, &self.rpn(&whole.children()[1])).is_some();
            let built = match in_system {
                true => self.member_of(&whole, scope, facts, step)?,
                false => self.no("not a membership in a number system", &[]),
            };
            return match built {
                Built(p) => Ok(Built(p)),
                Declined(_) => Err(self.defect(
                    self.at,
                    format!(
                        "{} does not reach {}, which this line claims it supplies",
                        str::trim(how),
                        self.render(&term)
                    ),
                )),
            };
        }
        if let Some(p) = self.held(facts, &term, scope)? {
            return Ok(Built(p));
        }
        // A reason that is a method or an item is proved as the step it would
        // be, by the route a numbered step takes (`as_a_step`): a requires
        // line and a step have one way of being proved.
        if let (Some(step), Some(req)) = (step, req) {
            let what = format!(
                "the requires line {} of step {}",
                str::trim(req.fact.text()),
                step.number
            );
            if let Built(p) = self.as_a_step(step, req, &what, scope, facts)? {
                return Ok(Built(p));
            }
        }
        // What no route reaches is a defect naming the line; nothing is taken
        // in its place.
        Err(self.defect(
            self.at,
            format!(
                "{} does not reach {}, which this line claims it supplies",
                str::trim(how),
                self.render(&term)
            ),
        ))
    }

    /// The `requires` line that supplies one side condition.
    ///
    /// A lemma can ask for more than the text writes: only the side a reader
    /// could doubt is written down, and what no line supplies is settled from
    /// the term.
    pub fn required(
        &mut self,
        step: &Step,
        goal: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Proof> {
        let mut written: BTreeSet<String> = BTreeSet::new();
        for r in &step.requires {
            let node = self.read_one(&r.fact)?;
            written.insert(self.term(&node)?);
        }
        // The scope's copy of a claim is taken only where no line of the step
        // writes it, and a membership the page says once is taken from where
        // it says it.
        if !written.contains(goal) {
            if let Built(p) = self.said_once_proof(&self.to_term(goal), scope, facts)? {
                return Ok(p);
            }
            if let Some(p) = self.held(facts, goal, scope)? {
                return Ok(p);
            }
        }
        // A lemma may ask its side conditions as one conjunction where the
        // text writes a line each, and a conjunction the lines do name
        // between them is answered a part at a time.
        let whole = self.to_term(goal);
        if whole
            .children()
            .iter()
            .any(|one| written.contains(&self.rpn(one)))
        {
            let joined = self.conjoined(&whole, scope, &mut |me, one| {
                let part = me.rpn(one);
                me.required(step, &part, scope, facts).map(Built)
            })?;
            match joined {
                Some(Declined(d)) => return Err(self.defect(self.at, self.say(&d))),
                Some(Built(p)) => return Ok(p),
                None => {}
            }
        }
        for r in &step.requires {
            let node = self.read_one(&r.fact)?;
            if self.term(&node)? == goal {
                // The line proved once already, by its own reason, where the
                // step's requires lines were supplied: that proof is the line.
                if let Some(p) = self.held(facts, goal, scope)? {
                    if p.origin.contains(&requirement(r.line)) {
                        return Ok(p);
                    }
                }
                // `side` is where a line is discharged by what it names, so
                // it is given `how` as well as the claim.
                let named = facts.copy();
                let resting = self.reason_allows(step, r);
                self.named_first(r.refs(), &resting, &named);
                return match self.side(&node, r, scope, &named, Some(step))? {
                    Built(made) => self.discharged_by(made, step, r),
                    Declined(d) => Err(self.defect(
                        self.at,
                        format!(
                            "the requires line for {} is justified by {}, which does not reach it: {}",
                            self.render(goal),
                            r.how,
                            self.say(&d)
                        ),
                    )),
                };
            }
        }
        // A `requires` line that is not there is the text's to fix, so this
        // one is a defect.
        match self.settle(&self.to_term(goal), scope, facts, 3, None, None)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                self.at,
                format!("no requires line for {}", self.render(goal)),
            )),
        }
    }
}
