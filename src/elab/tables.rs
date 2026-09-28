//! Reading the rule tables: a fact the page leaves out, built by table.
//!
//! The rule tables are the fourth of the elaborator's six parts
//! (`ELABORATION.md`, "How the elaborator is built"), and `rules` holds them
//! as data. This is the code that reads them. Given what is wanted — an
//! equation lifted through a term, a term's membership of a number system, a
//! numeral's, a term's sethood — it looks up the lemma the table names for
//! that shape and builds the proof from it. Nothing here searches: what a
//! table has no entry for is declined, and left to what is tried after.

use std::collections::BTreeSet;

use indexmap::IndexMap;
use num_traits::ToPrimitive;

use super::field::{self, Value};
use super::linear;
use super::provenance::{from_requires, rests_on_only};
use super::state::{fit, names_of, Binding, Elaborator};
use super::{Facts, Lines};
use crate::binds;
use crate::corpus::Step;
use crate::formula::Node;
use crate::mm::kernel::Term;
use crate::mm::spell::Proof;
use crate::outcome::{Built, Checked, Declined, Route};
use crate::rules::{self, lookup, numeral_label};
use crate::{pf, t, take};

/// One kind of difference the walk in `congruence` closes where two terms
/// are both known and differ in places.
#[derive(Clone, Debug)]
pub enum Row {
    /// An equation in hand says the two are equal.
    Held,
    /// The equation a step cites, which rewrote the place: the line says
    /// `was = now`, or `now = was` where `flip`.
    Cited {
        was: String,
        now: String,
        said: String,
        flip: bool,
    },
    /// The equation a lemma's own hypothesis assumes.
    Assumed {
        was: String,
        now: String,
        under: String,
    },
    /// The two have one standard form.
    Standard,
    /// A term carried to its standard form.
    Toward,
}

/// What the walk asks where two terms differ.
#[derive(Clone, Debug)]
pub enum Leaf {
    /// Each row in turn; the first that closes the difference gives the
    /// proof there, and where none does the walk goes a level in.
    Rows(Vec<Row>),
    /// A piece of numerals alone that changed, proved where it stands as a
    /// closed fact: a link of a calculation naming `arithmetic`.
    Arithmetic { what: String, step: Box<Step> },
}

/// A chain of lemmas carrying a membership to what it also says: each
/// lemma, what it was bound to, and what it reaches.
#[derive(Clone)]
pub struct Link {
    pub lemma: String,
    pub binding: Option<Binding>,
    pub reached: Term,
}

/// How a caller proves one part of a compound in a number system.
pub type Parts<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &str, &str) -> Checked<Route<Proof>> + 'p;
/// How a caller proves a divisor is not zero.
pub type Nonzero<'p, 'a> =
    dyn FnMut(&mut Elaborator<'a>, &str) -> Checked<Route<Proof>> + 'p;

impl<'a> Elaborator<'a> {
    /// Run `f` with what the step's requires lines made offered to the
    /// membership lookup and the one-lemma bridge, which read these before
    /// any search, and which a search never does. `keep` lays these over
    /// what is already offered rather than in its place.
    pub fn writing<T>(
        &mut self,
        scope: &str,
        known: &Facts,
        keep: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let kept = self.written.clone();
        let made: IndexMap<String, (String, Proof)> = known
            .entries()
            .into_iter()
            .filter(|(_, v)| from_requires(v))
            .map(|(k, v)| (k, (scope.to_string(), v)))
            .collect();
        self.written = if keep {
            let mut out = kept.clone();
            for (k, v) in made {
                out.insert(k, v);
            }
            out
        } else {
            made
        };
        let out = f(self);
        self.written = kept;
        out
    }

    /// `said ∈ system` searched for, at the depth the caller gives.
    pub fn within(
        &mut self,
        said: &str,
        system: &str,
        scope: &str,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let wanted = self.to_term(&t!(said, system, "wcel"));
        self.settle(&wanted, scope, facts, depth, None, None)
    }

    /// ( scope -> given = want ), or `<->` for statements, where the walk
    /// would go under a binder whose letter the scope spells: the lemma that
    /// carries a change under a binder keeps its letter apart from the
    /// scope. Each side's letter at `place` is moved to one nothing holds,
    /// closed (`renaming` for a statement, `class_alpha` for a class), the
    /// two are walked there, and the result is moved back.
    #[allow(clippy::too_many_arguments)]
    fn over_spare_letter(
        &mut self,
        given: &Term,
        want: &Term,
        place: usize,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        // Looked at, not taken: the letter stands inside this one statement
        // and nowhere else.
        let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
            return Ok(Route::no("no letter left to walk under this binder by"));
        };
        let moved_to = |term: &Term| {
            let mut put = Binding::new();
            put.insert(
                term.children()[place].variable().unwrap_or("").to_string(),
                fresh.clone(),
            );
            term.substitute(&put)
        };
        let (moved, moved_want) = (moved_to(given), moved_to(want));
        let walked =
            take!(self.congruence(&moved, &moved_want, scope, facts, step, leaf)?);
        let wff = self.is_wff(given);
        let (there, back) = if wff {
            (
                self.renaming(given, &moved)?,
                self.renaming(&moved_want, want)?,
            )
        } else {
            (
                self.class_alpha(given, &moved)?,
                self.class_alpha(&moved_want, want)?,
            )
        };
        let (Some(there), Some(back)) = (there, back) else {
            return Ok(Route::no("the binder is not renamed apart from the scope"));
        };
        let join = if wff { "wb" } else { "wceq" };
        let (a, b) = (self.rpn(given), self.rpn(&moved));
        let (c, d) = (self.rpn(&moved_want), self.rpn(want));
        let first = pf!(self.b; t!(a, b, join), scope, there, "a1i");
        let last = pf!(self.b; t!(c, d, join), scope, back, "a1i");
        Ok(Built(self.chained(
            scope,
            &[
                (given.clone(), moved.clone(), first),
                (moved, moved_want.clone(), walked),
                (moved_want, want.clone(), last),
            ],
        )))
    }

    /// Carry one change up to the whole term it sits in.
    ///
    /// Two terms that differ in one place are walked in step, and the lemma
    /// that lifts each level is the one the tree names. What counts as the
    /// change, and what proves it there, is the caller's `leaf`. What it
    /// refuses is a route declining and not a defect, however it was
    /// reached.
    pub fn congruence(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
    ) -> Checked<Route<Proof>> {
        if let Some(found) = self.leaf(leaf, given, want, scope, facts)? {
            return Ok(found);
        }
        if given.label() != want.label()
            || given.children().len() != want.children().len()
        {
            return Ok(self.no(
                "{} and {} differ by more than the change being carried",
                &[&self.rpn(given), &self.rpn(want)],
            ));
        }
        let label = given.label().unwrap_or("").to_string();
        let g: Vec<String> = given.children().iter().map(|c| self.rpn(c)).collect();
        let w: Vec<String> = want.children().iter().map(|c| self.rpn(c)).collect();
        let words: Vec<&str> = scope.split_whitespace().collect();
        // Only the body is carried under the binder here; a domain that
        // changes with the body kept is the branch for domains below.
        if label == "wrex" && w[1..] == g[1..] {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            // `rexbidva` keeps its letter apart from the scope it carries.
            if words.contains(&name.as_str()) {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(format!("{name} cv"), runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(
                pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, "rexbidva"),
            ));
        }
        // A sum's summand is carried the same way, under its index's range.
        if label == "csu" && g[0] == w[0] && g[2] == w[2] && g[1] != w[1] {
            let kids = given.children();
            let (runs, body, name) = (g[0].clone(), &kids[1], g[2].clone());
            if words.contains(&name.as_str()) {
                return self
                    .over_spare_letter(given, want, 2, scope, facts, step, leaf);
            }
            let member = t!(format!("{name} cv"), runs, "wcel");
            let other = want.children()[1].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "sumeq2dv",
                &binds! {"ph" => scope, "A" => &runs, "B" => self.rpn(body), "C" => self.rpn(&other), "k" => &name},
                &[&made],
            )));
        }
        // A set-builder's condition is carried the same way, under its
        // letter's membership of the domain.
        if label == "crab" && g[1] == w[1] && g[2] == w[2] && g[0] != w[0] {
            let kids = given.children();
            let (body, name, runs) = (&kids[0], g[1].clone(), g[2].clone());
            if words.contains(&name.as_str()) {
                // The scope holds D's own equation, which binds this letter,
                // so the condition is carried over a spare the scope does not
                // spell and the builder renamed to it and back.
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let member = t!(format!("{name} cv"), runs, "wcel");
            let other = want.children()[0].clone();
            let made = self.frames_kept(|me| {
                let (inner, lifted) = me.widen(scope, facts, &member, None);
                me.congruence(body, &other, &inner, &lifted, step, leaf)
            })?;
            let made = take!(made);
            return Ok(Built(self.b.ap(
                "rabbidva",
                &binds! {"ph" => scope, "ps" => self.rpn(body), "ch" => self.rpn(&other), "x" => &name, "A" => &runs},
                &[&made],
            )));
        }
        // A "for every" or "there is" whose domain changes, its letter and
        // its body kept.
        if (label == "wral" || label == "wrex")
            && g[0] == w[0]
            && g[1] == w[1]
            && g[2] != w[2]
        {
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma =
                rules::congruence(&label, &[2]).expect("a congruence for a domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&moved],
            )));
        }
        // And its domain and body together.
        if (label == "wral" || label == "wrex")
            && g[1] == w[1]
            && g[0] != w[0]
            && g[2] != w[2]
        {
            let kids = given.children().to_vec();
            if words.contains(&g[1].as_str()) {
                return self
                    .over_spare_letter(given, want, 1, scope, facts, step, leaf);
            }
            let over = take!(self.congruence(
                &kids[2],
                &want.children()[2],
                scope,
                facts,
                step,
                leaf
            )?);
            let said = take!(self.congruence(
                &kids[0],
                &want.children()[0],
                scope,
                facts,
                step,
                leaf
            )?);
            let lemma = rules::congruence(&label, &[0, 2])
                .expect("a congruence for a domain and a body");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "ps" => &g[0], "ch" => &w[0], "x" => &g[1], "A" => &g[2], "B" => &w[2]},
                &[&over, &said],
            )));
        }
        // A map whose domain changes, its letter and its rule kept.
        if (label == "cmpt" || label == "ciun")
            && g[0] == w[0]
            && g[2] == w[2]
            && g[1] != w[1]
        {
            let kids = given.children().to_vec();
            let moved = take!(self.congruence(
                &kids[1],
                &want.children()[1],
                scope,
                facts,
                step,
                leaf
            )?);
            if let Some(wider) = self.domain_holding(given, want, scope, &moved) {
                return Ok(Built(wider));
            }
            let lemma = rules::congruence(&label, &[1])
                .expect("a congruence for a map's domain");
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "x" => &g[0], "A" => &g[1], "B" => &w[1], "C" => &g[2]},
                &[&moved],
            )));
        }
        let wrapped = rules::WRAPS.contains(&label.as_str());
        let n = if wrapped { g.len() - 1 } else { g.len() };
        let kids: Vec<Term> = given.children()[..n].to_vec();
        let wants: Vec<Term> = want.children()[..n].to_vec();
        let (spelt, other) = (&g[..n], &w[..n]);
        let slots: Vec<usize> = (0..n).filter(|&i| spelt[i] != other[i]).collect();
        if slots.is_empty() {
            return Ok(Route::no("nothing changed under this term"));
        }
        // A rule by cases changes in its condition and its two values at
        // once, and `ifbieq12d` takes both old values before the new ones,
        // so it is given its parts by name; a part that stays the same is
        // carried by `biidd` or `eqidd`.
        if label == "cif" {
            let mut parts = Vec::new();
            for i in 0..3 {
                let one = if slots.contains(&i) {
                    take!(
                        self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?
                    )
                } else if i == 0 {
                    self.b
                        .ap("biidd", &binds! {"ph" => scope, "ps" => &spelt[0]}, &[])
                } else {
                    self.b
                        .ap("eqidd", &binds! {"ph" => scope, "A" => &spelt[i]}, &[])
                };
                parts.push(one);
            }
            return Ok(Built(self.b.ap(
                "ifbieq12d",
                &binds! {"ph" => scope, "ps" => &spelt[0], "ch" => &other[0], "A" => &spelt[1],
                "B" => &spelt[2], "C" => &other[1], "D" => &other[2]},
                &[&parts[0], &parts[1], &parts[2]],
            )));
        }
        // A function spelt as its define's name against the map it names:
        // `feq1d`, and for one-to-one `f1eq1` after the equation by `syl`.
        if (label == "wf" || label == "wf1") && slots == [2] {
            let moved =
                take!(self.congruence(&kids[2], &wants[2], scope, facts, step, leaf)?);
            let parts = binds! {"A" => &spelt[0], "B" => &spelt[1], "F" => &spelt[2], "G" => &other[2]};
            if label == "wf" {
                let mut all = parts.clone();
                all.insert("ph".to_string(), scope.to_string());
                return Ok(Built(self.b.ap("feq1d", &all, &[&moved])));
            }
            let law = self.b.ap("f1eq1", &parts, &[]);
            return Ok(Built(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => t!(spelt[2], other[2], "wceq"),
                "ch" => t!(self.rpn(given), self.rpn(want), "wb")},
                &[&moved, &law],
            )));
        }
        // What lifts the change is the lemma for this constructor and these
        // places, and the operation it lifts under must be the same one.
        let lifting = rules::congruence(&label, &slots);
        let Some(lifting) =
            lifting.filter(|_| !(wrapped && g[g.len() - 1] != w[w.len() - 1]))
        else {
            return Ok(Route::no("no lemma carries this change up"));
        };
        // The lemmas that carry a change under a binder keep its letter
        // apart from the scope.
        if lookup(rules::BOUND, &label).is_some()
            && g.len() >= 2
            && words.contains(&g[1].as_str())
        {
            return self.over_spare_letter(given, want, 1, scope, facts, step, leaf);
        }
        let moved: Vec<&String> =
            slots.iter().flat_map(|&i| [&spelt[i], &other[i]]).collect();
        let rest: Vec<&String> = spelt
            .iter()
            .enumerate()
            .filter(|(i, _)| !slots.contains(i))
            .map(|(_, s)| s)
            .collect();
        let head = if wrapped {
            g[g.len() - 1].clone()
        } else {
            String::new()
        };
        let mut under = Vec::new();
        for &i in &slots {
            under.push(self.congruence(&kids[i], &wants[i], scope, facts, step, leaf)?);
        }
        let mut proofs = Vec::new();
        for one in under {
            match one {
                Built(p) => proofs.push(p),
                Declined(d) => {
                    // The body of a "for every" may change only for a member
                    // of its domain, so it is carried again under that
                    // membership, as a "there is" is.
                    if label == "wral" && slots == [0] {
                        return self
                            .under_member(given, want, scope, facts, step, leaf, d);
                    }
                    return Ok(Declined(d));
                }
            }
        }
        let mut all: Vec<crate::mm::spell::Part> = vec![crate::elab::part(scope)];
        all.extend(moved.iter().map(|m| crate::elab::part(*m)));
        all.extend(rest.iter().map(|r| crate::elab::part(*r)));
        all.push(crate::elab::part(&head));
        all.extend(proofs.iter().map(|p| crate::elab::part(p)));
        all.push(crate::elab::part(lifting));
        let parts: Vec<_> = all
            .into_iter()
            .filter(|p| !matches!(p, crate::mm::spell::Part::Text("")))
            .collect();
        Ok(Built(self.b.proof(&parts)))
    }

    /// ( scope -> given = want ), a map whose domain changes to one spelling
    /// its letter, by `mpteq12dv` with its rule kept; None where neither
    /// domain spells the letter.
    pub fn domain_holding(
        &self,
        given: &Term,
        want: &Term,
        scope: &str,
        moved: &Proof,
    ) -> Option<Proof> {
        if given.label() != Some("cmpt") {
            return None;
        }
        let kids: Vec<String> = given.children().iter().map(|c| self.rpn(c)).collect();
        let (letter, over, rule) = (&kids[0], &kids[1], &kids[2]);
        let new = self.rpn(&want.children()[1]);
        let spells = |t: &str| t.split_whitespace().any(|w| w == letter.as_str());
        if !spells(over) && !spells(&new) {
            return None;
        }
        let kept = self
            .b
            .ap("eqidd", &binds! {"ph" => scope, "A" => rule}, &[]);
        Some(self.b.ap(
            "mpteq12dv",
            &binds! {"ph" => scope, "x" => letter, "A" => over, "B" => rule, "C" => &new, "D" => rule},
            &[moved, &kept],
        ))
    }

    /// ( scope -> ( A. x e. A ph <-> A. x e. A ps ) ), the body carried with
    /// x ∈ A in scope (`ralbidva`); `why` where that fails too.
    #[allow(clippy::too_many_arguments)]
    fn under_member(
        &mut self,
        given: &Term,
        want: &Term,
        scope: &str,
        facts: &Facts,
        step: Option<&Step>,
        leaf: &Leaf,
        why: crate::outcome::Decline,
    ) -> Checked<Route<Proof>> {
        let kids = given.children().to_vec();
        let (body, variable, over) = (&kids[0], &kids[1], &kids[2]);
        let (name, runs) = (self.rpn(variable), self.rpn(over));
        if scope.split_whitespace().any(|w| w == name.as_str()) {
            // `ralbidva` keeps its letter apart from the scope, so where the
            // scope spells it the two are carried over a spare and renamed
            // back.
            let Some(fresh) = self.unheld(&[&self.to_term(scope), given, want]) else {
                return Ok(Declined(why));
            };
            let mut put = Binding::new();
            put.insert(variable.variable().unwrap_or("").to_string(), fresh);
            let moved = given.substitute(&put);
            let moved_want = want.substitute(&put);
            let walked = self.under_member(
                &moved,
                &moved_want,
                scope,
                facts,
                step,
                leaf,
                why.clone(),
            )?;
            let there = self.renamed_apart(given, &moved)?;
            let back = self.renamed_apart(&moved_want, want)?;
            let (Built(walked), Some(there), Some(back)) = (walked, there, back) else {
                return Ok(Declined(why));
            };
            let (a, b) = (self.rpn(given), self.rpn(&moved));
            let (c, d) = (self.rpn(&moved_want), self.rpn(want));
            let first = pf!(self.b; t!(a, b, "wb"), scope, there, "a1i");
            let last = pf!(self.b; t!(c, d, "wb"), scope, back, "a1i");
            let middle = self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &b, "th" => &c},
                &[&first, &walked],
            );
            return Ok(Built(self.b.ap(
                "bitrd",
                &binds! {"ph" => scope, "ps" => &a, "ch" => &c, "th" => &d},
                &[&middle, &last],
            )));
        }
        let member = t!(format!("{name} cv"), runs, "wcel");
        let other = want.children()[0].clone();
        let made = self.frames_kept(|me| {
            let (inner, lifted) = me.widen(scope, facts, &member, None);
            me.congruence(body, &other, &inner, &lifted, step, leaf)
        })?;
        let Built(made) = made else {
            return Ok(Declined(why));
        };
        Ok(Built(
            pf!(self.b; scope, self.rpn(body), self.rpn(&other), name, runs, made, "ralbidva"),
        ))
    }

    /// ( scope -> t e. S ), for a term built from numerals alone: a digit
    /// set.mm names in the system is its label, and anything else built only
    /// from numerals is settled from the declared closure lemmas, which is
    /// working it out and not searching.
    pub fn numeral_within(
        &mut self,
        goal: &Term,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let named = self.digit_within(goal, scope, facts)?;
        if !named.is_declined() {
            return Ok(named);
        }
        let said = self.rpn(&goal.children()[0]);
        if said.split_whitespace().any(|t| !rules::numeric(t)) {
            return Ok(named);
        }
        // One level deeper than `settle`'s default. Nothing in it is a
        // proof's own, so what it comes to is the same wherever it is asked
        // under this scope, and is worked out once — only where it rests on
        // nothing on the page.
        let want = self.rpn(goal);
        let key = (want.clone(), scope.to_string());
        if let Some(found) = self.numbers.get(&key) {
            return Ok(found.clone());
        }
        self.numbering.insert(want.clone());
        let found = (|| -> Checked<Route<Proof>> {
            let found = self.settle(goal, scope, &Facts::new(), 4, None, None)?;
            if found.is_declined() {
                return self.by_value(goal, scope);
            }
            Ok(found)
        })();
        self.numbering.shift_remove(&want);
        let found = found?;
        let keep = match &found {
            Declined(_) => true,
            Built(p) => p.origin.is_empty(),
        };
        if keep {
            self.numbers.insert(key, found.clone());
        }
        Ok(found)
    }

    /// ( scope -> t e. S ) for a closed t, through the digit it comes to: the
    /// equation is worked out as `arithmetic` works one out, and the
    /// membership is the digit's, carried across it by `eqeltrd`.
    fn by_value(&mut self, goal: &Term, scope: &str) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let value = take!(field::closed_value(&said));
        let digit = match value {
            Value::Exact(v)
                if v.is_integer() && v >= field::q(0) && v <= field::q(9) =>
            {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("it does not come to a digit")),
        };
        let digit = numeral_label(digit).expect("a digit");
        if self.rpn(&said) == digit {
            return Ok(Route::no("it is a digit already"));
        }
        let member_goal = self.to_term(&t!(digit, self.rpn(&system), "wcel"));
        let member = take!(self.digit_within(&member_goal, scope, &Facts::new())?);
        let lines = Lines::new();
        let same = take!(self.prove_field(
            None,
            &t!(self.rpn(&said), digit, "wceq"),
            scope,
            &Facts::new(),
            &lines
        )?);
        Ok(Built(self.b.ap(
            "eqeltrd",
            &binds! {"ph" => scope, "A" => self.rpn(&said), "B" => digit, "C" => self.rpn(&system)},
            &[&same, &member],
        )))
    }

    /// ( scope -> ; A B e. S ), for a numeral of more than one digit, built
    /// from the digits' labels and brought into the scope once.
    fn decimal_within(&mut self, goal: &Term, scope: &str) -> Checked<Route<Proof>> {
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let Some(lift) = system.label().and_then(|l| lookup(rules::FROM_NN0, l)) else {
            return Ok(Route::no("a decimal is placed in ℕ₀, ℤ, ℝ and ℂ only"));
        };
        fn whole(me: &Elaborator, term: &Term) -> Route<Proof> {
            if let Some(d) = term.label().and_then(rules::digit_of) {
                if term.children().is_empty() {
                    return Built(me.step(&format!("{d}nn0")));
                }
            }
            if term.label() != Some("cdc") {
                return Route::no("not a numeral");
            }
            let (upper, last) = (&term.children()[0], &term.children()[1]);
            let parts = [whole(me, upper), whole(me, last)];
            if let Some(d) = parts.iter().find(|p| p.is_declined()) {
                return d.clone();
            }
            let [Built(a), Built(b)] = parts else {
                unreachable!("both parts are built")
            };
            Built(me.b.ap(
                "deccl",
                &binds! {"A" => me.rpn(upper), "B" => me.rpn(last)},
                &[&a, &b],
            ))
        }
        let mut closed = take!(whole(self, &said));
        if let Some(lift) = lift {
            let s = self.rpn(&said);
            closed = self.b.ap(lift, &binds! {"A" => &s, "N" => &s}, &[&closed]);
        }
        Ok(Built(pf!(self.b; self.rpn(goal), scope, closed, "a1i")))
    }

    /// ( scope -> d e. S ), for a digit and a system set.mm names it in.
    ///
    /// `ax-1cn` is the one place the library spells such a label otherwise,
    /// and where it names none the fact is one it does not state.
    pub fn digit_within(
        &mut self,
        goal: &Term,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let _ = facts;
        let (said, system) = (goal.children()[0].clone(), goal.children()[1].clone());
        let suffix = system.label().and_then(|l| lookup(rules::SYSTEMS, l));
        let Some(suffix) = suffix.filter(|_| system.children().is_empty()) else {
            return Ok(Route::no("not a number system set.mm names digits in"));
        };
        if said.label() == Some("cdc") {
            return self.decimal_within(goal, scope);
        }
        let value = linear::numeral(&said, self.flabel());
        let digit = match value {
            Some(v) if v.is_integer() && v >= field::q(0) && v <= field::q(9) => {
                v.to_integer().to_u32().unwrap_or(0)
            }
            _ => return Ok(Route::no("what belongs is not a single digit")),
        };
        // The side must *be* its digit. One that only works out to it is a
        // computation, and this is not the method that does computations.
        let numeral = numeral_label(digit).expect("a digit");
        if self.rpn(&said) != numeral {
            return Ok(Route::no(
                "a side works out to a digit but is one only after working out",
            ));
        }
        let system_label = system.label().unwrap_or("").to_string();
        let mut label = format!("{digit}{suffix}");
        if !self.b.sigs.contains_key(&label) {
            label = format!("ax-{label}");
        }
        if !self.b.sigs.contains_key(&label)
            && suffix == "z"
            && self.b.sigs.contains_key(&format!("{digit}nn0"))
        {
            // set.mm names every digit in ℕ₀ and only some in ℤ.
            let whole = self.step(&format!("{digit}nn0"));
            let closed = self.b.ap("nn0zi", &binds! {"N" => numeral}, &[&whole]);
            return Ok(Built(
                pf!(self.b; t!(numeral, system_label, "wcel"), scope, closed, "a1i"),
            ));
        }
        if !self.b.sigs.contains_key(&label) {
            return Ok(Route::no(format!(
                "set.mm does not state {}",
                self.render(&self.rpn(goal))
            )));
        }
        let held = self.step(&label);
        Ok(Built(self.b.ap(
            "a1i",
            &binds! {"ph" => t!(numeral, system_label, "wcel"), "ps" => scope},
            &[&held],
        )))
    }

    /// That a term belongs to a number system, which the text writes.
    ///
    /// Membership is a dull fact the page states rather than a step's to
    /// discover, so a term whose membership nothing supplies is a line the
    /// proof owes, and saying so is what this is for. A decline here would
    /// reach the caller as the method not covering the step, which is the
    /// one thing it does not mean.
    pub fn membership(
        &mut self,
        said: &str,
        system: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Proof> {
        let want = t!(said, system, "wcel");
        // What the step's own lines say, first; `part` says in what order.
        if let Built(p) = self.part(said, system, scope, facts)? {
            return Ok(p);
        }
        // What `part` cannot build is searched for, with the step's own
        // lines laid over the scope's copies of the same claims.
        let written = facts.filtered(|_, v| from_requires(v));
        for (k, (at, v)) in self.written.clone() {
            if let Some(lifted) = self.lifted_to(&k, &v, &at, scope) {
                written.set(k, lifted);
            }
        }
        let offered = facts.with(&written);
        match self.settle(&self.to_term(&want), scope, &offered, 3, None, None)? {
            Built(p) => Ok(p),
            Declined(_) => Err(self.defect(
                self.at,
                format!("nothing says {}, which this step needs", self.render(&want)),
            )),
        }
    }

    /// What a membership says of its term besides itself, as (claim, lemmas)
    /// pairs: the lemmas carry the membership to the claim one after another.
    pub fn implied_terms(&self, said: &str) -> Vec<(String, Vec<String>)> {
        self.implied_chains(said)
            .into_iter()
            .map(|(claim, chain)| (claim, chain.into_iter().map(|l| l.lemma).collect()))
            .collect()
    }

    /// `implied_terms` with each lemma's binding and what it reaches.
    fn implied_chains(&self, said: &str) -> Vec<(String, Vec<Link>)> {
        let node = self.to_term(said);
        if node.variable().is_some()
            || node.label() != Some("wcel")
            || node.children().len() != 2
        {
            return Vec::new();
        }
        let mut system = self.rpn(&node.children()[1]);
        let mut head: Vec<Link> = Vec::new();
        if lookup(rules::WITHIN, &system).is_none()
            && lookup(rules::IMPLIED, &system).is_none()
        {
            let where_ = &node.children()[1];
            if where_.variable().is_some()
                || where_.label() != Some("co")
                || where_.children().len() != 3
                || self.rpn(&where_.children()[2]) != "cfz"
            {
                return Vec::new();
            }
            let start = self.rpn(&where_.children()[0]);
            for (inside, first, lemma) in rules::RANGE_WITHIN {
                if first.is_none() || *first == Some(start.as_str()) {
                    if let Some(made) = self.lemma_step(lemma, &node) {
                        head = vec![made];
                        system = inside.to_string();
                        break;
                    }
                }
            }
            if head.is_empty() {
                return Vec::new();
            }
        }
        let mut out = Vec::new();
        if let Some(first) = head.first() {
            out.push((self.rpn(&first.reached), head.clone()));
        }
        let at = head
            .last()
            .map(|l| l.reached.clone())
            .unwrap_or_else(|| node.clone());
        for (_sign, big) in rules::SYSTEM_OF {
            let Some(path) =
                rules::within_path(Some(&system), Some(big)).filter(|p| !p.is_empty())
            else {
                continue;
            };
            let mut chain = head.clone();
            let mut here = at.clone();
            for lemma in path {
                let made = self.lemma_step(lemma, &here).unwrap_or_else(|| {
                    panic!("{lemma} does not take {}", self.rpn(&here))
                });
                here = made.reached.clone();
                chain.push(made);
            }
            out.push((self.rpn(&here), chain));
        }
        for (_page, lemma) in rules::implied(Some(&system)) {
            let made = self
                .lemma_step(lemma, &at)
                .unwrap_or_else(|| panic!("{lemma} does not take {}", self.rpn(&at)));
            let mut chain = head.clone();
            chain.push(made.clone());
            out.push((self.rpn(&made.reached), chain.clone()));
            // The page writes k ≠ 0 as a denied equation, `nnne0` as =/=.
            if made.reached.label() == Some("wne") {
                let kids = made.reached.children().to_vec();
                let denied = Term::apply("wn", vec![Term::apply("wceq", kids)]);
                chain.push(Link {
                    lemma: "neneqd".to_string(),
                    binding: None,
                    reached: denied.clone(),
                });
                out.push((self.rpn(&denied), chain));
            }
        }
        out
    }

    /// (lemma, binding, what it concludes) for a lemma `( P -> Q )` applied
    /// to a term matching P, or None where it does not match.
    fn lemma_step(&self, lemma: &str, fact: &Term) -> Option<Link> {
        let whole = self.statement(lemma);
        let binding = fit(
            &whole.children()[0],
            fact,
            &Binding::new(),
            &names_of(&whole),
        )?;
        let reached = whole.children()[1].substitute(&binding);
        Some(Link {
            lemma: lemma.to_string(),
            binding: Some(binding),
            reached,
        })
    }

    /// Each thing a membership line also says, with its proof under `scope`
    /// from the line's own `proof`.
    pub fn implied(
        &self,
        said: &str,
        proof: &Proof,
        scope: &str,
    ) -> IndexMap<String, Proof> {
        let mut out = IndexMap::new();
        for (claim, chain) in self.implied_chains(said) {
            let mut held = proof.clone();
            let mut at = said.to_string();
            for link in chain {
                let after = self.rpn(&link.reached);
                if link.lemma == "neneqd" {
                    let node = self.to_term(&at);
                    let (a, b) =
                        (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
                    held = self.b.ap(
                        "neneqd",
                        &binds! {"ph" => scope, "A" => &a, "B" => &b},
                        &[&held],
                    );
                } else {
                    let binding = link.binding.as_ref().expect("a lemma's binding");
                    let binds = self.spelt(binding);
                    let law = self.b.ap(&link.lemma, &binds, &[]);
                    held = pf!(self.b; scope, at, after, held, law, "syl");
                }
                at = after;
            }
            out.insert(claim, held);
        }
        out
    }

    /// `said ∈ system`, carried in one lemma from a membership written: only
    /// the lemmas `rules::MEMBERSHIP` declares that take a thing in one
    /// number system to another, and only one of them.
    pub fn bridged(
        &mut self,
        said: &str,
        system: &str,
        scope: &str,
        written: &Facts,
    ) -> Option<Proof> {
        if self.bridges.is_none() {
            let mut bridges = IndexMap::new();
            for label in self.declared_as(super::state::Role::Carrier) {
                let whole = self.statement(&label);
                let (given, gives) = (&whole.children()[0], &whole.children()[1]);
                bridges
                    .entry((
                        self.rpn(&given.children()[1]),
                        self.rpn(&gives.children()[1]),
                    ))
                    .or_insert(label);
            }
            self.bridges = Some(bridges);
        }
        let bridges = self.bridges.clone().unwrap_or_default();
        for ((source, target), label) in bridges {
            if target != system {
                continue;
            }
            let claim = t!(said, source, "wcel");
            let mut proof = written.get(&claim);
            if proof.is_none() {
                if let Some((at, held)) = self.written.get(&claim).cloned() {
                    proof = self.lifted_to(&claim, &held, &at, scope);
                }
            }
            // What a requires line wrote, or what a line being cited says.
            let Some(proof) = proof else {
                continue;
            };
            let origin = &proof.origin;
            let cited =
                !origin.is_empty() && origin.iter().all(|o| self.citing.contains(o));
            if !(from_requires(&proof) || cited) {
                continue;
            }
            let push = self.sig(&label).push()[0].to_string();
            let law = self.b.ap(&label, &binds! {push => said}, &[]);
            return Some(self.b.ap(
                "syl",
                &binds! {"ph" => scope, "ps" => &claim, "ch" => t!(said, system, "wcel")},
                &[&proof, &law],
            ));
        }
        None
    }

    /// The sethood of each class a statement's `let` lines introduce, in the
    /// kernel's sense, which the page never says: each goes into `facts`
    /// sealed as `sethood@<label>`, and those origins are what this gives
    /// back, for `sorts`.
    pub fn sethoods(
        &mut self,
        nodes: &[Node],
        terms: &[String],
        scope: &str,
        facts: &Facts,
    ) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        let hypotheses = self.thm.hypotheses.clone();
        for ((h, node), t) in hypotheses.iter().zip(nodes).zip(terms) {
            let Some(label) = h.label.clone().filter(|l| !l.is_empty()) else {
                continue;
            };
            if h.kind != crate::corpus::Intro::Let || h.text.contains(" be a set") {
                continue;
            }
            let subject = super::reading::subject_of(node).text.clone();
            let Some(kernel) = self.names.get(&subject).cloned() else {
                continue;
            };
            let said = t!(kernel, "cvv", "wcel");
            let origin = format!("sethood@{label}");
            if let Some(held) = facts.get(&said) {
                let sealed = self.seal(held, &origin);
                facts.set(said, sealed);
            } else if let (true, Some(held)) =
                (node.notation == "membership", facts.get(t))
            {
                let parts = self.to_term(t);
                let (a, b) = (
                    self.rpn(&parts.children()[0]),
                    self.rpn(&parts.children()[1]),
                );
                let law = self.b.ap("elex", &binds! {"A" => &a, "B" => &b}, &[]);
                let made = pf!(self.b; scope, t, said, held, law, "syl");
                let sealed = self.seal(made, &origin);
                facts.set(said, sealed);
            } else {
                continue;
            }
            out.insert(origin);
        }
        out
    }

    /// `term ∈ V` from the constructor at the term's head; else a decline.
    /// `SETHOOD` names the lemma, and `apply_lemma` asks what it asks — the
    /// parts' sethood — of `settle`, which comes back here for each part.
    pub fn made_a_set(
        &mut self,
        wanted: &Term,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let head = &wanted.children()[0];
        let lemma = if head.variable().is_none() {
            head.label().and_then(|l| lookup(rules::SETHOOD, l))
        } else {
            None
        };
        let Some(lemma) = lemma else {
            return Ok(Route::no(format!(
                "no lemma makes a {} a set",
                head.label().unwrap_or("None")
            )));
        };
        self.apply_lemma(lemma, wanted, scope, facts, None, false, None)
    }

    /// `said ∈ system` for a compound, from its parts; else a decline.
    ///
    /// What each part is proved by is the caller's: `parts(term, system)`. A
    /// fixed table and no search, so nothing it cannot build costs more than
    /// a lookup. A quotient is built only where `nonzero(divisor)` is given
    /// to prove its divisor is not zero.
    pub fn built(
        &mut self,
        said: &str,
        system: &str,
        scope: &str,
        parts: &mut Parts<'_, 'a>,
        nonzero: Option<&mut Nonzero<'_, 'a>>,
    ) -> Checked<Route<Proof>> {
        let node = self.to_term(said);
        if node.variable().is_none()
            && node.label() == Some("co")
            && node.children().len() == 3
        {
            let (left, right) =
                (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
            let op = self.rpn(&node.children()[2]);
            let divided = lookup(rules::DIVIDED, system);
            if let (true, Some(nonzero), Some(lemma)) = (op == "cdiv", nonzero, divided)
            {
                let pa = take!(parts(self, &left, system)?);
                let pb = take!(parts(self, &right, system)?);
                let pn = take!(nonzero(self, &right)?);
                return Ok(Built(self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "A" => &left, "B" => &right},
                    &[&pa, &pb, &pn],
                )));
            }
            let Some(lemma) = rules::closed(&op, system) else {
                return Ok(Route::no(format!("no closure lemma for {op} in {system}")));
            };
            let pa = take!(parts(self, &left, system)?);
            let into = if op == "cexp" { "cn0" } else { system };
            let pb = take!(parts(self, &right, into)?);
            let key = if op == "cexp" { "N" } else { "B" };
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "A" => &left, key => &right},
                &[&pa, &pb],
            )));
        }
        if node.variable().is_none()
            && node.label() == Some("cneg")
            && node.children().len() == 1
        {
            let Some(lemma) = lookup(rules::NEGATED, system) else {
                return Ok(Route::no(format!(
                    "no closure lemma for negation in {system}"
                )));
            };
            let a = self.rpn(&node.children()[0]);
            let pa = take!(parts(self, &a, system)?);
            return Ok(Built(self.b.ap(
                lemma,
                &binds! {"ph" => scope, "A" => &a},
                &[&pa],
            )));
        }
        Ok(Route::no(
            "not a sum, difference, product, power or negation",
        ))
    }

    /// A compound's membership of a number system, from its parts': there is
    /// one way to build a product from its factors, and the factors are
    /// smaller, so walking the term spends no depth. Each factor is settled
    /// in turn with the depth the whole was given.
    pub fn closed_under(
        &mut self,
        wanted: &Term,
        scope: &str,
        facts: &Facts,
        depth: i32,
    ) -> Checked<Route<Proof>> {
        let (said, system) = (
            self.rpn(&wanted.children()[0]),
            self.rpn(&wanted.children()[1]),
        );
        self.built(
            &said,
            &system,
            scope,
            &mut |me, term, system| {
                let goal = me.to_term(&t!(term, system, "wcel"));
                me.settle(&goal, scope, facts, depth, None, None)
            },
            Some(&mut |me, divisor| {
                let goal = me.to_term(&t!(divisor, "cc0", "wne"));
                me.settle(&goal, scope, facts, depth, None, None)
            }),
        )
    }

    /// ( scope -> d =/= 0 ) from what the step wrote, or a decline: the
    /// divisor not being zero is the page's to say, in a requires line or a
    /// line the step cites, and is not searched for.
    pub fn divisor_written(
        &mut self,
        divisor: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let apart = t!(divisor, "cc0", "wne");
        // A digit other than zero says so itself: a closed numeral fact,
        // which a method may use unwritten.
        if let Some(value) = rules::digit_of(divisor).filter(|v| *v != 0) {
            let label = if value == 1 {
                "ax-1ne0".to_string()
            } else {
                format!("{value}ne0")
            };
            return Ok(Built(pf!(self.b; apart, scope, label, "a1i")));
        }
        let denied = t!(t!(divisor, "cc0", "wceq"), "wn");
        for want in [&apart, &denied] {
            let mut found = facts.get(want);
            if found.is_none() {
                if let Some((at, held)) = self.written.get(want).cloned() {
                    found = self.lifted_to(want, &held, &at, scope);
                }
            }
            let Some(found) = found else {
                continue;
            };
            if *want == apart {
                return Ok(Built(found));
            }
            return Ok(Built(pf!(self.b; scope, divisor, "cc0", found, "neqned")));
        }
        // A cited line whose membership says so: `let k ∈ ℕ` says k ≠ 0.
        let citing: Vec<String> = self.citing.iter().cloned().collect();
        for r in citing {
            let Some(line) = self.lines.get(&r) else {
                continue;
            };
            let carried = self.carried(&r, facts, &self.lines);
            for (said, proof) in self.stated_by(&r, facts, &self.lines.clone()) {
                let proof = if said == line.term {
                    Some(carried.clone())
                } else {
                    proof
                };
                let Some(proof) = proof else {
                    continue;
                };
                let more = self.implied(&said, &proof, scope);
                if let Some(p) = more.get(&apart) {
                    return Ok(Built(p.clone()));
                }
            }
        }
        // A divisor built in ℕ is not zero (`nnne0`).
        if let Built(natural) = self.part(divisor, "cn", scope, facts)? {
            let law = self.b.ap("nnne0", &binds! {"A" => divisor}, &[]);
            return Ok(Built(
                pf!(self.b; scope, t!(divisor, "cn", "wcel"), apart, natural, law, "syl"),
            ));
        }
        // A product or quotient is not zero when its parts are not.
        let node = self.to_term(divisor);
        if node.variable().is_none()
            && node.label() == Some("co")
            && node.children().len() == 3
        {
            let how = self.rpn(&node.children()[2]);
            let lemma = match how.as_str() {
                "cmul" => Some("mulne0d"),
                "cdiv" => Some("divne0d"),
                _ => None,
            };
            if let Some(lemma) = lemma {
                let (a, b) =
                    (self.rpn(&node.children()[0]), self.rpn(&node.children()[1]));
                let mut parts = Vec::new();
                for one in [&a, &b] {
                    parts.push(self.part(one, "cc", scope, facts)?);
                }
                for one in [&a, &b] {
                    parts.push(self.divisor_written(one, scope, facts)?);
                }
                let mut proofs = Vec::new();
                for one in parts {
                    proofs.push(take!(one));
                }
                return Ok(Built(self.b.ap(
                    lemma,
                    &binds! {"ph" => scope, "A" => &a, "B" => &b},
                    &proofs.iter().collect::<Vec<_>>(),
                )));
            }
        }
        Ok(Route::no(format!(
            "nothing the step wrote says {}",
            self.render(&apart)
        )))
    }

    /// One part of a compound, in a number system, or a decline.
    ///
    /// The step's own line first, then that line carried by one lemma, then
    /// the part built in turn if it is a compound. A numeral is the
    /// library's. What the scope holds is last, and only exactly: it is a
    /// line the page wrote, and a step using it without naming it is what
    /// provenance is there to see.
    pub fn part(
        &mut self,
        said: &str,
        system: &str,
        scope: &str,
        facts: &Facts,
    ) -> Checked<Route<Proof>> {
        let want = t!(said, system, "wcel");
        let found = facts.get(&want);
        if let Some(f) = &found {
            if from_requires(f) {
                return Ok(Built(f.clone()));
            }
        }
        if let Some((at, held)) = self.written.get(&want).cloned() {
            if let Some(lifted) = self.lifted_to(&want, &held, &at, scope) {
                return Ok(Built(lifted));
            }
        }
        if let Some(carried) = self.bridged(said, system, scope, facts) {
            return Ok(Built(carried));
        }
        let term = self.to_term(said);
        if linear::numeral(&term, self.flabel()).is_some() {
            return self.settle(&self.to_term(&want), scope, facts, 3, None, None);
        }
        let made = self.built(
            said,
            system,
            scope,
            &mut |me, term, into| me.part(term, into, scope, facts),
            Some(&mut |me, divisor| me.divisor_written(divisor, scope, facts)),
        )?;
        if !made.is_declined() {
            return Ok(made);
        }
        if let Some(f) = found {
            return Ok(Built(f));
        }
        Ok(Route::no(format!(
            "nothing written says {}",
            self.render(&want)
        )))
    }

    /// What a line states, sentence by sentence, with each proof where
    /// `facts` holds one: its own sentences, and where it obtained names,
    /// their memberships, which the scope holds with the line as their
    /// origin.
    pub fn stated_by(
        &self,
        r: &str,
        facts: &Facts,
        lines: &Lines,
    ) -> IndexMap<String, Option<Proof>> {
        let term = lines.get(r).map(|l| l.term).unwrap_or_default();
        let mut out: IndexMap<String, Option<Proof>> = IndexMap::new();
        for said in self.parts(&term) {
            let held = facts.get(&said);
            out.insert(said, held);
        }
        for (said, proof) in facts.entries() {
            if rests_on_only(&proof, r) {
                out.entry(said).or_insert(Some(proof));
            }
        }
        out
    }
}
