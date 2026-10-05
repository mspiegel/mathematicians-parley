//! Where the elaborator and the checker answer one question differently,
//! listed for `tests/agree.rs` (`Options::list_answers`).
//!
//! Two answers are compared as kernel terms: the checker answers in the
//! page's notation, and one fact has several spellings there, k ≥ 0 and
//! 0 ≤ k, which are one term. Only the elaborator turns page text into kernel
//! terms, so the comparison is made here, with the checker's answer asked of
//! the same line. Each difference is one line, `path:line | fact | which
//! tool | answer`, with the answer in the page's notation (`spoken`).

use std::collections::BTreeSet;

use crate::citing::{asked, claimed_member, filled, finished, implied_facts, obtained};
use crate::corpus::proof::requires_item;
use crate::corpus::{references, Item, Record, Step};
use crate::formula::Node;
use crate::matching::{instantiation, Binding};
use crate::outcome::{Built, Checked, Declined, Route};
use crate::sorts::Env;

use super::state::Elaborator;

impl<'a> Elaborator<'a> {
    /// What the item each requires line cites asks for, as this elaborator
    /// answers it (`asked_by_requires`): one line per hypothesis, `path:line
    /// | asked | item | fact`, for the requires line's step.
    /// The member a claim said of every member names is named first, as
    /// `does_work` names it. Where the elaborator cannot answer, what stops
    /// it is listed as its answer, since that is what a comparison is of.
    pub fn list_asked(&mut self, step: &Step) -> Checked<()> {
        let path = self.thm.path.clone();
        let letter = if step.requires.is_empty() {
            None
        } else {
            self.member_letter(step)?
        };
        let mut out = Vec::new();
        for o in &step.requires {
            let Some((named, _)) = requires_item(&o.how) else {
                continue;
            };
            let (asks, shared) = self.aside(|me| {
                if let Some((page, kernel)) = &letter {
                    if !me.names.contains_key(page) {
                        me.names.insert(page.clone(), kernel.clone());
                    }
                }
                let asks = me.asked_by_requires(step, &o.how, &o.fact);
                let shared = me.shared_asked(step, o.line, &o.how, &o.fact);
                (asks, shared)
            });
            let mut mine: BTreeSet<String> = BTreeSet::new();
            match asks {
                Ok(asks) => {
                    for fact in asks {
                        out.push(format!(
                            "{path}:{} | asked | {named} | {}",
                            o.line,
                            self.render(&fact)
                        ));
                        mine.insert(fact);
                    }
                }
                Err(problem) => out.push(format!(
                    "{path}:{} | asked | {named} | cannot answer: {}",
                    o.line, problem.message
                )),
            }
            // Where the shared answer (`citing::asked`) differs from this one.
            let at = format!("{path}:{} | {named} asks", o.line);
            match shared {
                Err(problem) => {
                    out.push(format!("{at} | shared cannot read | {}", problem.message))
                }
                Ok(Declined(d)) => {
                    out.push(format!("{at} | shared declines | {}", d.reason()))
                }
                Ok(Built(theirs)) => {
                    let theirs: BTreeSet<String> = theirs.into_iter().collect();
                    for (who, only) in [
                        ("elaborator", mine.difference(&theirs)),
                        ("shared", theirs.difference(&mine)),
                    ] {
                        for t in only {
                            out.push(format!("{at} | {who} only | {}", self.render(t)));
                        }
                    }
                }
            }
        }
        if let Some(list) = &mut self.answers {
            list.extend(out);
        }
        Ok(())
    }

    /// What the item a requires line cites asks, as the shared matcher
    /// answers it (`citing::asked`), each hypothesis as a term; declined
    /// where the line cites no record or no group of it concludes the line's
    /// fact. The citation's parts are those the checker gives it: the lines
    /// it names, the requires lines above it, the member a claim said of
    /// every member names, and its written instantiation.
    fn shared_asked(
        &mut self,
        step: &Step,
        line: usize,
        how: &str,
        fact: &str,
    ) -> Checked<Route<Vec<String>>> {
        let Some((cited, _)) = requires_item(how) else {
            return Ok(Route::no("the line cites no item"));
        };
        let name = cited.split_once(':').map_or(cited.as_str(), |(_, n)| n);
        let full = self.thm.names.full(name);
        let Some(Item::Record(item)) = self.items.get(&full).copied() else {
            return Ok(Route::no("the line cites no record"));
        };
        let library = self.item_library();
        let mut facts = self.cited_sentences(&references(how).0)?;
        for above in step.requires_above(line) {
            facts.push(self.read(&above.fact)?);
        }
        if step.openers.is_empty() {
            if let [claim] = self.said(step)?.as_slice() {
                if let Some((member, _)) =
                    claimed_member(claim, &library, &self.sorts_now)
                {
                    facts.push(member);
                }
            }
        }
        let claims = self
            .sentences(fact)
            .iter()
            .map(|s| self.read(s))
            .collect::<Checked<Vec<Node>>>()?;
        let mut seed = Binding::new();
        for (name, value) in instantiation(how) {
            seed.insert(name, self.read(&value)?);
        }
        let parts = finished(facts, claims, seed, &library, &self.sorts_now);
        let asks = match asked(&item.qualified(), &parts, &library) {
            Built(a) => a,
            Declined(d) => return Ok(Declined(d)),
        };
        // Each letter the binding fixes is already replaced in the hypotheses
        // (`citing::filled`), so they are terms in the item's names as they
        // stand.
        self.in_its_names(Item::Record(item), |me| {
            asks.hypotheses
                .iter()
                .map(|h| me.term(h))
                .collect::<Checked<Vec<String>>>()
        })
        .map(Built)
    }

    /// Where the shared matcher (`citing::obtained`) says an obtain claims
    /// something other than `node`, what this elaborator says it claims: two
    /// lines, one for each answer. The citation's parts are those the checker
    /// gives it: the lines the step names, its requires lines, and its
    /// written instantiation.
    pub fn list_obtained(
        &mut self,
        step: &Step,
        item: &'a Record,
        cites: &str,
        node: &Node,
    ) {
        let at = format!(
            "{}:{} | {} obtains",
            self.thm.path,
            step.line,
            item.qualified()
        );
        let found = self.aside(|me| -> Checked<Route<(String, String)>> {
            let library = me.item_library();
            let Some(groups) = library.groups(&item.qualified()) else {
                return Ok(Route::no("no item has that name"));
            };
            let mut facts = me.cited_sentences(&step.just.refs)?;
            for r in &step.requires {
                facts.push(me.read(&r.fact)?);
            }
            let mut seed = Binding::new();
            for (name, value) in instantiation(cites) {
                seed.insert(name, me.read(&value)?);
            }
            let parts = finished(facts, Vec::new(), seed, &library, &me.sorts_now);
            let taken = match obtained(&groups, &parts.facts, &parts.seed, &library) {
                Built(t) => t,
                Declined(d) => return Ok(Declined(d)),
            };
            let said = Self::claimed_by(Item::Record(item));
            let read = me.in_its_names(Item::Record(item), |me| me.read(&said))?;
            let theirs = filled(&read, &taken.binding, &library.ctx);
            let theirs = (me.term(&theirs)?, me.g.print(&theirs));
            Ok(Built(theirs))
        });
        let mine = self.aside(|me| me.term(node));
        let lines = match (found, mine) {
            (Err(problem), _) => {
                vec![format!("{at} | shared cannot read | {}", problem.message)]
            }
            (Ok(Declined(d)), _) => {
                vec![format!("{at} | shared declines | {}", d.reason())]
            }
            (Ok(Built((term, _))), Ok(own)) if term == own => Vec::new(),
            (Ok(Built((_, said))), _) => vec![
                format!("{at} | elaborator | {}", self.g.print(node)),
                format!("{at} | shared | {said}"),
            ],
        };
        if let Some(list) = &mut self.answers {
            list.extend(lines);
        }
    }

    /// What each sentence implies besides itself: the elaborator's answer
    /// (`implied_terms`) against the checker's (`implied_facts`). The step's
    /// claims and its requires lines are read with the member a claim said
    /// of every member names, as `does_work` reads them.
    pub fn list_implied(&mut self, step: &Step, sentences: &[String]) -> Checked<()> {
        let path = self.thm.path.clone();
        let line = step.line;
        let letter = if step.requires.is_empty() {
            None
        } else {
            self.member_letter(step)?
        };
        let found = self.aside(|me| -> Checked<Vec<String>> {
            if let Some((page, kernel)) = &letter {
                if !me.names.contains_key(page) {
                    me.names.insert(page.clone(), kernel.clone());
                }
            }
            let env = Env {
                g: me.g,
                scopes: me.scopes,
            };
            let mut out = Vec::new();
            for sentence in sentences {
                let node = me.read(sentence)?;
                let kernel = me.term(&node)?;
                // What the page can say: `nnne0` concludes set.mm's =/=, which
                // the page writes as a denied equation, and that is listed too.
                let mine: BTreeSet<String> = me
                    .implied_terms(&kernel)
                    .into_iter()
                    .map(|(implied, _)| implied)
                    .filter(|implied| me.spoken(implied).is_some())
                    .collect();
                let mut theirs: BTreeSet<String> = BTreeSet::new();
                for implied in implied_facts(&node, env, &me.sorts_now) {
                    theirs.insert(me.term(&implied)?);
                }
                let fact = me.render(&kernel);
                for (who, only) in [
                    ("elaborator", mine.difference(&theirs)),
                    ("checker", theirs.difference(&mine)),
                ] {
                    for t in only {
                        out.push(format!(
                            "{path}:{line} | {fact} | {who} only | {}",
                            me.render(t)
                        ));
                    }
                }
            }
            Ok(out)
        })?;
        if let Some(list) = &mut self.answers {
            list.extend(found);
        }
        Ok(())
    }
}
