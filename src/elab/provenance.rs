//! The proof rules: what a step's proof may rest on, and what it must use.
//!
//! This is the sixth of the elaborator's six parts (`ELABORATION.md`, "How
//! the elaborator is built"). Given a finished step's proof and what the step
//! names, it refuses a proof that rests on anything the step does not name
//! (R1), a `requires` line or a named line that does no work, and a
//! `requires` line whose proof does not come from its reason (R2).
//!
//! A proof carries its `origin`, the page items it rests on. `seal` makes a
//! proof stand for one item from then on, and keeps what it was built from
//! in `rests_on`, so a line is asked the same of its own reason and a use is
//! traced through the lines that use it.

use std::collections::BTreeSet;

use super::linear;
use super::state::{number_of, Elaborator};
use super::Facts;
use crate::corpus::proof::{cited_item, references};
use crate::corpus::{fmt, item_prefix, Item, Step};
use crate::formula::Node;
use crate::mm::spell::Proof;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup};
use crate::targets;
use crate::{pf, t};

pub const REQUIRES: &str = "requires@";

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
pub fn rests_on_only(proof: &Proof, item: &str) -> bool {
    proof.origin.len() == 1
        && proof.origin.iter().next().map(String::as_str) == Some(item)
}

/// The references a justification names, for a reader outside its file.
pub fn citations(text: &str) -> Vec<String> {
    references(text).0
}

/// The lemmas an item's `target` names, one per `then` group; none for a
/// theorem of the corpus.
pub fn item_clauses(item: Item) -> Vec<String> {
    match item {
        Item::Record(r) => targets::clauses(r),
        Item::Theorem(_) => Vec::new(),
    }
}

impl<'a> Elaborator<'a> {
    /// The atoms of a claim a method combined, and every term in it.
    ///
    /// An atom is what the method treats as a number it knows nothing
    /// about: a name, an absolute value, a function's value, a power whose
    /// exponent is not a numeral. A numeral of more than one digit is an atom
    /// to the method, which reads only digits, but not to the page: `deccl`
    /// says 10 is a number, so the step is not asked to.
    pub fn atoms_of(
        &self,
        rpn: &str,
        linear: bool,
        atoms: &mut BTreeSet<String>,
        terms: &mut BTreeSet<String>,
    ) {
        fn walk(
            me: &Elaborator,
            node: &crate::mm::Term,
            linear: bool,
            atoms: &mut BTreeSet<String>,
            terms: &mut BTreeSet<String>,
        ) {
            let label = node.label().unwrap_or("");
            if node.variable().is_none() && rules::RELATIONS.contains(&label) {
                let kids = if label == "wbr" {
                    &node.children()[..2]
                } else {
                    node.children()
                };
                for kid in kids {
                    walk(me, kid, linear, atoms, terms);
                }
                return;
            }
            terms.insert(me.rpn(node));
            if linear::numeral(node, me.flabel()).is_some() || label == "cdc" {
                return;
            }
            if node.variable().is_none() && label == "co" && node.children().len() == 3
            {
                let op = me.rpn(&node.children()[2]);
                if rules::ARITHMETIC.contains(&op.as_str()) {
                    walk(me, &node.children()[0], linear, atoms, terms);
                    walk(me, &node.children()[1], linear, atoms, terms);
                    return;
                }
                if op == "cexp"
                    && linear::numeral(&node.children()[1], me.flabel()).is_some()
                {
                    walk(me, &node.children()[0], linear, atoms, terms);
                    return;
                }
            }
            if node.variable().is_none() && label == "cneg" {
                walk(me, &node.children()[0], linear, atoms, terms);
                return;
            }
            // A finite sum read as linear is looked inside: what it combines
            // is each part's factor free of its letter, and what holds the
            // letter is a number as a summand is, by what its terms are.
            if let Some((_, _, parts)) = linear
                .then(|| super::field::linear_sum(node, me.flabel()))
                .flatten()
            {
                for part in parts {
                    for (atom, _) in &part.free {
                        walk(me, &me.to_term(atom), linear, atoms, terms);
                    }
                }
                return;
            }
            atoms.insert(me.rpn(node));
        }
        walk(self, &self.to_term(rpn), linear, atoms, terms);
    }

    /// Whether a term a line says is a number is an atom a method combined:
    /// the same term, over other bound letters or with its defined names
    /// written out, as `inequalities` reads it.
    fn one_atom(&self, held: &str, atom: &str) -> bool {
        if held == atom || self.rebound(held, atom) {
            return true;
        }
        let out = self.rpn(&self.defined_names_out(&self.to_term(held)));
        out == atom || self.rebound(&out, atom)
    }

    /// Everything a step names does work, or a defect names what does not.
    ///
    /// A cited line or requires line is at work where the proof rests on it,
    /// directly or through another of the step's requires lines. On a method
    /// step a requires line is also at work where the method demands it
    /// without the kernel needing it, and each atom's membership must be on
    /// the page. A step citing an item, as its head or as what it obtains
    /// from, is the checker's to judge.
    pub fn does_work(
        &mut self,
        step: &Step,
        number: &str,
        proof: &Proof,
    ) -> Checked<()> {
        if cited_item(&step.just).is_some() {
            return Ok(());
        }
        let mut used: BTreeSet<String> = proof.origin.clone();
        let mut todo: Vec<String> = used
            .iter()
            .filter(|u| u.starts_with(REQUIRES))
            .cloned()
            .collect();
        while let Some(one) = todo.pop() {
            let more: Vec<String> = self
                .rests_on
                .get(&one)
                .map(|s| s.iter().cloned().collect())
                .unwrap_or_default();
            for m in more {
                if !used.contains(&m) {
                    used.insert(m.clone());
                    if m.starts_with(REQUIRES) {
                        todo.push(m);
                    }
                }
            }
        }
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        for r in &step.just.refs {
            if !seen.insert(r) {
                continue;
            }
            if !used.contains(r) && !self.sorts.contains(r) {
                return Err(self.defect(
                    step.line,
                    format!("step {number} cites {r} and uses nothing it says"),
                ));
            }
        }
        let mut atoms = BTreeSet::new();
        let mut terms = BTreeSet::new();
        let combined: Vec<String> = self
            .combined
            .get(&step.line)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default();
        // An `algebra` step reads its sums as linear where one of them is
        // linear in something, and then what it combines is inside them.
        let lines = self.lines.clone();
        let linear = step.just.head.to_string() == "algebra"
            && combined
                .iter()
                .any(|c| self.sums_linear(c, Some(step), &lines));
        for claim in &combined {
            self.atoms_of(claim, linear, &mut atoms, &mut terms);
        }
        let mut written = Vec::new();
        let letter = if step.requires.is_empty() {
            None
        } else {
            self.member_letter(step)?
        };
        for r in &step.requires {
            let term = self.names_kept(|me| -> Checked<String> {
                if let Some((page, kernel)) = &letter {
                    if !me.names.contains_key(page) {
                        me.names.insert(page.clone(), kernel.clone());
                    }
                }
                let node = me.read(&r.fact)?;
                me.term(&node)
            })?;
            let claim = self.to_term(&term);
            written.push(claim.clone());
            if used.contains(&requirement(r.line)) {
                continue;
            }
            let demanded = match claim.label() {
                // An atom is the same atom over other bound letters, and a
                // defined name the atom it names.
                Some("wcel") => {
                    let held = self.rpn(&claim.children()[0]);
                    atoms.iter().any(|a| self.one_atom(&held, a))
                }
                Some("wne") => terms.contains(&self.rpn(&claim.children()[0])),
                Some("wn") if claim.children()[0].label() == Some("wceq") => {
                    terms.contains(&self.rpn(&claim.children()[0].children()[0]))
                }
                _ => false,
            };
            if !demanded {
                return Err(self.defect(
                    r.line,
                    format!(
                        "the requires line of step {number} says {}, and the step neither uses nor asks for it",
                        str::trim(&r.fact)
                    ),
                ));
            }
        }
        let mut cited: BTreeSet<String> = BTreeSet::new();
        for r in &step.just.refs {
            if let Some(line) = self.lines.get(r) {
                cited.extend(self.parts(&line.term));
            }
        }
        for atom in &atoms {
            let mut said = written.iter().any(|c| {
                let held = self.rpn(&c.children()[0]);
                c.label() == Some("wcel") && self.one_atom(&held, atom)
            });
            said = said
                || cited.iter().any(|p| {
                    let node = self.to_term(p);
                    node.label() == Some("wcel") && {
                        let held = self.rpn(&node.children()[0]);
                        self.one_atom(&held, atom)
                    }
                });
            if !said {
                // By the name the page writes, where the atom is one.
                let shown = self
                    .names
                    .iter()
                    .find(|(_, kernel)| *kernel == atom)
                    .map(|(name, _)| name.clone())
                    .unwrap_or_else(|| self.render(atom));
                return Err(self.defect(
                    step.line,
                    format!(
                        "step {number} combines {shown}, and nothing it writes or cites says it is a number"
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Record what a method step's claim is built from: the claim and the
    /// sentences of cited lines the method combined.
    pub fn combining(&mut self, terms: &[String]) {
        let at = self.at;
        let held = self.combined.entry(at).or_default();
        for t in terms {
            held.insert(t.clone());
        }
    }

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
        if block {
            let prefix = format!("{number}.");
            out.extend(
                self.lines
                    .keys()
                    .into_iter()
                    .filter(|k| k.starts_with(&prefix)),
            );
            out.extend(
                step.openers
                    .iter()
                    .filter(|o| !o.label.is_empty())
                    .map(|o| o.label.clone()),
            );
            out.insert(format!("{number} assumes"));
            let depth = number.matches('.').count() + 1;
            for inner in &self.thm.steps {
                let name = number_of(inner);
                if !name.starts_with(&prefix) || name.matches('.').count() != depth {
                    continue;
                }
                if inner.just.head.to_string() == "join" {
                    out.extend(inner.just.refs.iter().cloned());
                }
                // A block closed on a contradiction rests on the line its
                // last step contradicts.
                out.extend(inner.just.contradicting.iter().cloned());
            }
        }
        out
    }

    /// A requires line's proof, checked against its reason and sealed: it
    /// rests only on the lines its reason cites, the step's other requires
    /// lines, and the sorts in scope.
    pub fn discharged_by(
        &mut self,
        made: Proof,
        step: &Step,
        how: &str,
        line: usize,
    ) -> Checked<Proof> {
        let allowed = self.reason_allows(step, how);
        self.rests_on_named(&made, &allowed, line, "the requires line")?;
        Ok(self.seal(made, &requirement(line)))
    }

    /// What a requires line with this reason may rest on (R2).
    pub fn reason_allows(&self, step: &Step, how: &str) -> BTreeSet<String> {
        let mut out: BTreeSet<String> = citations(how).into_iter().collect();
        out.extend(self.sorts.iter().cloned());
        out.extend(step.requires.iter().map(|r| requirement(r.line)));
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
        let extra: Vec<&String> = proof
            .origin
            .iter()
            .filter(|o| !allowed.contains(*o))
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

    /// The proof, standing from here on for one thing on the page. What the
    /// proof was built from is kept in `rests_on`.
    pub fn seal(&mut self, proof: Proof, item: &str) -> Proof {
        self.rests_on
            .entry(item.to_string())
            .or_default()
            .extend(proof.origin.iter().cloned());
        Proof {
            items: proof.items,
            origin: std::iter::once(item.to_string()).collect(),
        }
    }

    /// A step's finished proof, checked by the rules and sealed: it rests on
    /// nothing the step does not name (R1), everything the step names does
    /// work, and from here on the proof stands for the step's number.
    /// The letter a step's claim says "for all" of, as the page writes it,
    /// and the kernel name it is bound to; None for any other claim. A step
    /// said of every member is proved at one, and its requires lines speak
    /// of that member by this letter.
    pub fn member_letter(&mut self, step: &Step) -> Checked<Option<(String, String)>> {
        let said = self.sentences(&step.claim_text());
        let [sentence] = said.as_slice() else {
            return Ok(None);
        };
        let node = self.read(sentence)?;
        if !node.notation.starts_with("for-all") || !node.children[0].is_name() {
            return Ok(None);
        }
        let said = self.term(&node)?;
        let term = self.to_term(&said);
        if term.variable().is_some() || term.label() != Some("wral") {
            return Ok(None);
        }
        let kernel = format!("{} cv", self.rpn(&term.children()[1]));
        Ok(Some((node.children[0].text.clone(), kernel)))
    }

    pub fn check_step(
        &mut self,
        proof: Proof,
        step: &Step,
        number: &str,
        block: bool,
    ) -> Checked<Proof> {
        let allowed = self.named(step, number, block);
        self.rests_on_named(&proof, &allowed, step.line, &format!("step {number}"))?;
        self.does_work(step, number, &proof)?;
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
    pub fn scope_origin(&self, scope: &str, facts: &Facts) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let mut todo = vec![scope.to_string()];
        while let Some(one) = todo.pop() {
            if let Some(held) = facts.get(&one) {
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
        out
    }

    /// The facts a step's own `requires` lines put within reach, proved once
    /// and offered alongside what the scope holds.
    ///
    /// A line naming an item is that item cited, and citing it asks the step
    /// for its own `requires` lines again. The one being proved is not among
    /// what can prove it, so it is held out while it is.
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
        for r in &step.requires {
            let want = self.read(&r.fact)?;
            let term = self.term(&want)?;
            if self.supplying.contains(&term) {
                continue;
            }
            // A claim the scope already holds is taken as it stands only
            // where this line's own reason made that proof.
            let mut given = known.clone();
            if let Some(held) = known.get(&term) {
                if held.origin.contains(&requirement(r.line)) {
                    continue;
                }
                if !self.rests_on_lines(&r.how) {
                    given = known.filtered(|k, _| k != term);
                }
            }
            self.supplying.insert(term.clone());
            let made = self.side(&want, &r.how, scope, &given, Some(step));
            self.supplying.shift_remove(&term);
            let made = match made? {
                Built(p) => self.discharged_by(p, step, &r.how, r.line)?,
                Declined(d) => panic!(
                    "the requires line at {} declined where it is proved: {}",
                    r.line,
                    self.say(&d)
                ),
            };
            known.set(term, made);
        }
        Ok(known)
    }

    /// Whether a `requires` line's reason is the lines it cites: `from H1`
    /// is, and so is a definition the database gives no target for, which the
    /// notation folds into the line it is unfolded at.
    pub fn rests_on_lines(&self, how: &str) -> bool {
        let reason = str::trim(how.split(',').next().unwrap_or("")).to_string();
        if reason.starts_with("from ") {
            return true;
        }
        let name = match reason.split_once(':') {
            Some((_, n)) => n,
            None => "",
        };
        if item_prefix(&reason).is_none() || str::trim(name).is_empty() {
            return false;
        }
        let first = name.split_whitespace().next().unwrap_or("");
        let full = self.thm.names.full(first);
        match self.items.get(&full) {
            Some(Item::Record(r)) => r.kind.unfolds() && targets::clauses(r).is_empty(),
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

    /// What a line a `requires` line names says, taken apart: a definition
    /// the database gives no target for is one the notation folds away, so
    /// the unfolding is the line itself, and a `from H1` reason asks the same
    /// of the line it names.
    pub fn unfolded_at(
        &mut self,
        term: &str,
        scope: &str,
        facts: &Facts,
        refs: &[String],
    ) -> Checked<Route<Proof>> {
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
            held.set(line.term.clone(), self.carried(r, facts, &self.lines));
            let whole = held.get(&line.term).unwrap();
            self.unpack(&line.term, &whole, scope, &held, 4);
            if let Some(p) = held.get(term) {
                return Ok(Built(p));
            }
            // Or what a membership it states says as well: `let k ∈ ℕ` says
            // k ∈ ℝ and k ≠ 0, each one lemma from it.
            let stated = held.copy();
            for (said, proof) in facts.entries() {
                if rests_on_only(&proof, r) {
                    stated.set_default(said, proof);
                }
            }
            for (said, proof) in stated.entries() {
                let more = self.implied(&said, &proof, scope);
                if let Some(p) = more.get(term) {
                    return Ok(Built(p.clone()));
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
            // What the line says beyond its recorded term: an obtain records
            // the body it obtained, and the name's domain went into the scope
            // with the line as its origin.
            if let Some(found) = facts.get(term) {
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
        how: &str,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let citing =
            std::mem::replace(&mut self.citing, citations(how).into_iter().collect());
        let allowed = step.map(|s| self.reason_allows(s, how));
        let out = self.resting_on(allowed, |me| {
            me.by_its_reason(want, how, scope, facts, step)
        });
        self.citing = citing;
        out
    }

    /// `side`, with what the line cites in hand.
    fn by_its_reason(
        &mut self,
        want: &Node,
        how: &str,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
    ) -> Checked<Route<Proof>> {
        let term = self.term(want)?;
        let refs = citations(how);
        // A define gives its function on the domain it names, which is proved
        // as it is for a step citing the define.
        let whole = self.to_term(&term);
        let defines = || {
            refs.iter()
                .all(|r| self.thm.defines.iter().any(|d| &d.label == r))
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
        if self.rests_on_lines(how) {
            return match self.unfolded_at(&term, scope, facts, &refs)? {
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
        if let Some(p) = facts.get(&term) {
            return Ok(Built(p));
        }
        let closure = str::trim(how.split(',').next().unwrap_or("")).to_string();
        // `membership` builds the fact from its parts, as a step naming it
        // does, from the lines this one cites.
        if closure == "membership" {
            return match self.member_of(&self.to_term(&term), scope, facts, step)? {
                Built(p) => Ok(Built(p)),
                Declined(d) => Err(self.defect(
                    self.at,
                    format!(
                        "{} is not built from what the requires line cites: {}",
                        self.render(&term),
                        self.say(&d)
                    ),
                )),
            };
        }
        // A line naming a method is discharged by the method it names. A
        // closed numeral inequality is what `arithmetic` decides outright.
        if closure == "arithmetic" {
            // Said in the page's words where the line is in hand.
            let mut written = None;
            if let Some(step) = step {
                for r in &step.requires {
                    if self.claim_of(&r.fact)? == term {
                        written = Some(r.fact.clone());
                        break;
                    }
                }
            }
            let said = match (&written, step) {
                (Some(w), Some(step)) => format!(
                    "the requires line of step {} claims {}",
                    fmt(&step.number),
                    str::trim(w)
                ),
                _ => format!("the requires line {}", self.render(&term)),
            };
            self.worked_out(&term, &said)?;
            if let Built(p) = self.prove_numeral(&term, scope, facts)? {
                return Ok(Built(p));
            }
        }
        // A line naming an item is that item cited, the same as a step naming
        // it, and only where the item has a target: citing one without is
        // assuming it. The name ends at the first space, because what follows
        // it is the instantiation.
        if let Some(step) = step {
            if let Some((_, name)) = closure.split_once(':') {
                if item_prefix(&closure).is_some() {
                    let first = name.split_whitespace().next().unwrap_or("");
                    let full = self.thm.names.full(first);
                    if let Some(item) = self.items.get(&full).copied() {
                        if !item_clauses(item).is_empty() {
                            // What the line cites is taken apart as a step's
                            // citations are.
                            let given =
                                self.with_cited(Some(step), scope, facts, Some(&refs));
                            return self.cite_item(
                                step,
                                &term,
                                scope,
                                &given,
                                item,
                                Some(how),
                            );
                        }
                    }
                }
            }
        }
        if closure == "arithmetic" {
            // A value is the other thing `arithmetic` decides, and a closed one
            // is an identity of the field with no atoms in it.
            let lines = self.lines.clone();
            if let Built(p) = self.prove_field(None, &term, scope, facts, &lines)? {
                return Ok(Built(p));
            }
            return Err(self
                .unshown(&term, &format!("the requires line {}", self.render(&term))));
        }
        if closure == "inequalities" {
            // A side condition resting on a method is proved the way a step
            // resting on it is, where the method can prove one at all.
            let lines = self.lines.clone();
            if let Built(p) =
                self.prove_order(&refs, &term, scope, facts, &lines, &[])?
            {
                return Ok(Built(p));
            }
        }
        // Nothing generic stands here. What is left is a method saying at the
        // head of the file that it was not expanded, or an error naming the
        // line.
        if closure == "inequalities" || closure == "algebra" {
            // A side condition resting on a closure method rests on it the
            // same way a step does, and is listed the same way: under what the
            // line cites, and under nothing else.
            let mut asks: Vec<(String, Proof)> = Vec::new();
            for r in &refs {
                if let Some(line) = self.lines.get(r) {
                    asks.push((line.term.clone(), self.carried(r, facts, &self.lines)));
                }
            }
            let mut statement = term.clone();
            for (one, _given) in asks.iter().rev() {
                statement = t!(one, statement, "wi");
            }
            let prefix = &closure[..3];
            let mut proof =
                self.stated(prefix, &format!("|- {}", self.render(&statement)))?;
            if asks.is_empty() {
                return Ok(Built(pf!(self.b; term, scope, proof, "a1i")));
            }
            for (i, (one, given)) in asks.iter().enumerate() {
                let mut rest = term.clone();
                for (later, _p) in asks[i + 1..].iter().rev() {
                    rest = t!(later, rest, "wi");
                }
                let fold = if i == 0 { "syl" } else { "mpd" };
                proof = pf!(self.b; scope, one, rest, given, proof, fold);
            }
            return Ok(Built(proof));
        }
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
            let node = self.read(&r.fact)?;
            written.insert(self.term(&node)?);
        }
        // The scope's copy of a claim is taken only where no line of the step
        // writes it.
        if !written.contains(goal) {
            if let Some(p) = facts.get(goal) {
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
            let node = self.read(&r.fact)?;
            if self.term(&node)? == goal {
                // `side` is where a line is discharged by what it names, so
                // it is given `how` as well as the claim.
                return match self.side(&node, &r.how, scope, facts, Some(step))? {
                    Built(made) => self.discharged_by(made, step, &r.how, r.line),
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

    /// The `requires` lines of this theorem never proved from their reasons.
    ///
    /// Each is proved from its reason once, when its step starts, and checked
    /// then to rest on nothing else. A line never proved is one whose reason
    /// nothing checked.
    pub fn unproved_requires(&self) -> Vec<usize> {
        let mut out: Vec<usize> = self
            .thm
            .steps
            .iter()
            .flat_map(|s| s.requires.iter())
            .filter(|r| !self.rests_on.contains_key(&requirement(r.line)))
            .map(|r| r.line)
            .collect();
        out.sort();
        out
    }
}
