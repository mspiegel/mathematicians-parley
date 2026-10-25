//! The proved lines of a theorem, and how a step reads one it cites.
//!
//! A line's fields are private to this module. A step citing a line reads
//! it through one of the readers here, which say what each gives, as the
//! checker's `Known::says`, `supplied`, `writes` and `sentences` do
//! (`SYNTAX.md`, What a cited line says):
//!
//! - `line_says`: everything the line says, what it implies among it;
//! - `line_supplies`: what it says but what it only implies, for a method
//!   or an item, which add implied facts themselves (`with_cited`);
//! - `line_writes`: the parts it writes, for a route that puts written
//!   lines together, as `join` and a method combining equations do;
//! - `line_written`: the line whole, as its step proved it;
//! - `line_sentences`: the sentences it was read from.

use super::state::{Elaborator, ProvedClaim};
use super::{Facts, Lines};
use crate::corpus::Step;
use crate::formula::Node;
use crate::mm::spell::Proof;
use crate::mm::Rpn;
use crate::outcome::{Built, Checked};
use crate::{pf, t};

/// A claim, a proof of it at one scope, and the sentences it was read from.
///
/// A line may say several things, and a substitution may land in one of
/// them, so what is kept is every sentence rather than the claim as one
/// tree. A line read from no text at all keeps none.
#[derive(Clone)]
pub struct Line {
    term: Rpn,
    proof: Proof,
    sentences: Vec<Node>,
}

impl Line {
    pub fn new(term: Rpn, proof: Proof, sentences: Vec<Node>) -> Line {
        Line {
            term,
            proof,
            sentences,
        }
    }

    /// The same line, read from the same sentences, as claiming `term` by
    /// `proof`: the line with its names written out, or carried to the
    /// claim a block owes.
    pub fn restated(&self, term: Rpn, proof: Proof) -> Line {
        Line {
            term,
            proof,
            sentences: self.sentences.clone(),
        }
    }
}

impl<'a> Elaborator<'a> {
    /// The line `cite` whole, as its step proved it, with the proof its
    /// step made: what a block closes on, what `join` puts together, and
    /// what a route matching the line as written compares. A route taking
    /// what the line says reads `line_says`. None where `cite` names no
    /// line.
    pub fn line_written(&self, cite: &str, lines: &Lines) -> Option<ProvedClaim> {
        lines.get(cite).map(|l| ProvedClaim {
            claim: l.term,
            proof: l.proof,
        })
    }

    /// The parts the line `cite` writes, each sentence and each part of a
    /// sentence joined by "and", the line itself where it is one: what a
    /// route putting written lines together takes, `join`, and a method
    /// combining the equations its lines write, which counts a chain's
    /// equations once. Empty where `cite` names no line.
    pub fn line_writes(&self, cite: &str, lines: &Lines) -> Vec<Rpn> {
        match lines.get(cite) {
            Some(l) => self.parts(&l.term),
            None => Vec::new(),
        }
    }

    /// The sentences the line `cite` was read from, for a route asking how
    /// the page writes it: the names a hypothesis speaks of, the sentence a
    /// substitution lands in. Empty where `cite` names no line, or one read
    /// from no text.
    pub fn line_sentences(&self, cite: &str, lines: &Lines) -> Vec<Node> {
        lines.get(cite).map(|l| l.sentences).unwrap_or_default()
    }

    /// A cited line's proof, said where the citing step sits: a line proved
    /// before a block opened holds inside it too, and the scope carries a
    /// copy that says so.
    ///
    /// The copy is the line's own claim, carried in as it is spelt when the
    /// scope opened, so it is the fact with the line's key spelt as the line.
    pub fn carried(&mut self, cite: &str, facts: &Facts, lines: &Lines) -> Proof {
        let held = lines
            .get(cite)
            .unwrap_or_else(|| panic!("no line {cite} to carry"));
        // The scope's copy of this line's own proof: another line saying the
        // same is another line, which a step naming this one does not rest on.
        facts.line_proof(cite, &held.term).unwrap_or(held.proof)
    }

    /// What the cited line `cite` says but what it only implies, each with
    /// its proof under `scope`: the line, each part of it (`unpack_all`) and
    /// the equation between any two terms of each chain of equations it
    /// writes (`know_chains`). Inside a block the line already says its
    /// reading at the block's letter (`know_in_scope_at_letters`). Empty
    /// where `cite` names no line.
    pub fn line_supplies(
        &mut self,
        cite: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Facts> {
        let out = Facts::new();
        let Some(line) = lines.get(cite) else {
            return Ok(out);
        };
        let whole = self.carried(cite, facts, lines);
        self.know(&out, line.term.clone(), whole.clone());
        self.unpack_all(&line.term, &whole, scope, &out);
        self.know_chains(&line.sentences, &line.term, &whole, scope, &out);
        for (claim, proof) in out.entries() {
            if let Some(members) = self.subset_members(&claim, &proof, scope) {
                if !self.holds(&out, &members.claim) {
                    self.know(&out, members.claim.clone(), members.proof.clone());
                }
                // Read at a block's letter, as a "for all" the line writes is
                // (`know_in_scope_at_letters`); one that does not fit gives
                // nothing.
                self.know_at_letters(&members.claim, &members.proof, scope, &out)?;
            }
        }
        Ok(out)
    }

    /// What a subset says of its members (`SYNTAX.md`, What a cited line
    /// says): `A ⊆ B`, or `A ∈ 𝒫B` as a `let A ⊆ B` is read, says "for all
    /// x ∈ A, x ∈ B", over a letter nothing in `scope` or the claim holds.
    /// None for any other claim, or where no letter is left.
    fn subset_members(
        &mut self,
        claim: &Rpn,
        proof: &Proof,
        scope: &Rpn,
    ) -> Option<ProvedClaim> {
        let node = self.to_term(claim);
        let [part, whole] = node.children() else {
            return None;
        };
        let (part, whole) = (self.rpn(part), self.rpn(whole));
        let (whole, inside) = match node.label() {
            Some("wss") => (whole, proof.clone()),
            Some("wcel") => {
                let set = self.to_term(&whole);
                let ([within], Some("cpw")) = (set.children(), set.label()) else {
                    return None;
                };
                let within = self.rpn(within);
                let inside = pf!(self.b; scope, part, within, proof, "elpwid");
                (within, inside)
            }
            _ => return None,
        };
        let letter = self.unheld(&[&self.to_term(scope), &node])?;
        let spare = self.rpn(&letter);
        let x = t!(spare, "cv");
        let member = t!(x, whole, "wcel");
        let at_one = pf!(self.b; scope, part, whole, x, inside, "sselda");
        let every = pf!(self.b; scope, member, spare, part, at_one, "ralrimiva");
        Some(ProvedClaim {
            claim: t!(member, spare, part, "wral"),
            proof: every,
        })
    }

    /// Everything the cited line `cite` says (`SYNTAX.md`, What a cited line
    /// says), each with its proof under `scope`: what it supplies
    /// (`line_supplies`), and what each of those implies (`implied`), a
    /// membership's and a range's bounds among it. The line is read from
    /// `lines`, which a route reading the theorem's hypotheses over the
    /// names it defines has rewritten (`hypotheses_by_their_names`). Empty
    /// where `cite` names no line.
    pub fn line_says(
        &mut self,
        cite: &str,
        scope: &Rpn,
        facts: &Facts,
        lines: &Lines,
    ) -> Checked<Facts> {
        let out = self.line_supplies(cite, scope, facts, lines)?;
        for (claim, proof) in out.entries() {
            let implied = self.implied(&claim, &proof, scope, facts)?;
            for (said, given) in implied.entries() {
                if !self.holds(&out, &said) {
                    self.know(&out, said, given);
                }
            }
            // A congruence says itself with its sides the other way round,
            // the lemma exchanging them asking that each is a number.
            // Held by its standard form already, the turned one is known by
            // its own spelling, which a route matching terms as written asks.
            let read = self.to_term(&claim);
            if let Some(turned) = self.pair_turned(&read) {
                let other = self.rpn(&turned);
                // Each side's being a number is the letter's membership said
                // once, which a step rests on unnamed (`rests_on_named`), not
                // the line introducing it.
                let said_once = facts.filtered(|_, p| {
                    p.origin
                        .iter()
                        .all(|o| o.starts_with(super::provenance::MEMBERSHIP))
                });
                if !out.keys().contains(&other) {
                    if let Built(alike) =
                        self.same(&read, &turned, scope, &said_once, None)?
                    {
                        let given =
                            pf!(self.b; scope, claim, other, proof, alike, "mpbid");
                        self.know(&out, other, given);
                    }
                }
            }
        }
        Ok(out)
    }

    /// The facts a lemma is answered from, what the step cites first: its
    /// justification's lines, or `refs` where a `requires` line names its
    /// own. Each line the step cites is taken apart on its own
    /// (`line_supplies`) and laid over the scope's copies of the same
    /// claims, and first in order as well, because a lemma's open
    /// antecedent takes the first fact that fits.
    ///
    /// A lemma proved in an outer scope (`allowed`) is offered only what that
    /// scope holds.
    pub fn with_cited(
        &mut self,
        step: Option<&Step>,
        scope: &Rpn,
        known: &Facts,
        refs: Option<&[String]>,
    ) -> Checked<Facts> {
        let outer = !self.frames.is_empty()
            && *scope != self.frames[self.frames.len() - 1].scope;
        let cited = Facts::new();
        let refs: Vec<String> = match refs {
            Some(r) => r.to_vec(),
            None => step.map(|s| s.just.refs.clone()).unwrap_or_default(),
        };
        let lines = self.lines.clone();
        for r in &refs {
            let Some(line) = lines.get(r) else {
                continue;
            };
            if outer && !self.holds(known, &line.term) {
                continue;
            }
            let parts = self.line_supplies(r, scope, known, &lines)?;
            for (k, v) in parts.entries() {
                self.know(&cited, k, v);
            }
        }
        let out = cited.copy();
        for (k, v) in known.entries() {
            if !self.holds(&cited, &k) {
                self.know(&out, k, v);
            }
        }
        Ok(out)
    }

    /// Each line written above a block's `let x ∈ X` read as the checker
    /// reads it inside the block (`SYNTAX.md`): a line with a part "for all
    /// a ∈ X, P(a)" says P(x) as well, so inside the block it is the line
    /// and P(x) together, whatever method a step citing it runs. Closing the
    /// block gives the lines back as they were (`Block::lines`).
    pub fn know_in_scope_at_letters(
        &mut self,
        scope: &Rpn,
        facts: &Facts,
    ) -> Checked<()> {
        for (label, line) in self.lines.entries() {
            let Some(whole) = facts.line_proof(&label, &line.term) else {
                continue;
            };
            let parts = Facts::new();
            self.know(&parts, line.term.clone(), whole.clone());
            self.unpack_all(&line.term, &whole, scope, &parts);
            let mut term = line.term.clone();
            let mut proof = whole.clone();
            let mut instances = Vec::new();
            for part in self.parts(&line.term) {
                let Some(held) = self.held(&parts, &part, scope)? else {
                    continue;
                };
                let Some(at) = self.know_at_letters(&part, &held, scope, &parts)?
                else {
                    continue;
                };
                let given = self
                    .held(&parts, &at, scope)?
                    .expect("the instance just known");
                proof = pf!(self.b; scope, term, at, proof, given, "jca");
                term = t!(term, at, "wa");
                instances.push(at);
            }
            if instances.is_empty() {
                continue;
            }
            self.at_letters_of.insert(term.clone(), instances);
            let proof = Proof {
                items: proof.items,
                origin: whole.origin.clone(),
            };
            self.know(facts, term.clone(), proof.clone());
            self.unpack_all(&term, &proof, scope, facts);
            self.lines.set(label, line.restated(term, proof));
        }
        Ok(())
    }
}
