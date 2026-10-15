//! What the elaborator answers to questions the checker also answers,
//! listed for `tests/agree.rs` (`Options::list_answers`).
//!
//! What a line implies is compared here, as kernel terms: the checker
//! answers in the page's notation, and one fact has several spellings there,
//! k ≥ 0 and 0 ≤ k, which are one term. Only the elaborator turns page text
//! into kernel terms, so the comparison is made here, with the checker's
//! answer asked of the same line. Each difference is one line, `path:line |
//! fact | which tool | answer`, with the answer in the page's notation
//! (`spoken`).
//!
//! What a cited record asks, and what an obtain says there is, both tools
//! answer with `citing` from their own reading of the page, and each lists
//! its answers as trees printed in the page's notation; the test compares
//! the two lists (`list_asked`, `checker::answers`).

use std::collections::BTreeSet;

use crate::citing::implied_facts;
use crate::corpus::{Item, Step};
use crate::formula::page::Sentence;
use crate::outcome::{Built, Checked, Declined};
use crate::sorts::Env;

use super::state::Elaborator;

impl Elaborator<'_> {
    /// What the record each requires line cites asks for, as this
    /// elaborator answers it (`asked_here`): one line per hypothesis,
    /// `path:line | asked | item | fact` in the page's notation, or one
    /// saying the shared matcher declines. The checker lists its own answer
    /// the same way (`checker::answers`), and `tests/agree.rs` compares the
    /// two.
    pub fn list_asked(&mut self, step: &Step) -> Checked<()> {
        let path = self.thm.path.clone();
        let mut out = Vec::new();
        for o in &step.requires {
            let Some((named, _)) = o.cited_item() else {
                continue;
            };
            let name = named.split_once(':').map_or(named.as_str(), |(_, n)| n);
            let full = self.thm.names.full(name);
            if !matches!(self.items.get(&full), Some(Item::Record(_))) {
                continue;
            }
            let at = format!("{path}:{} | asked | {named}", o.line);
            match self.asked_here(o) {
                Built(here) => {
                    // With the file's defines written out, as the checker
                    // reads the page (`Known::read_citing`), so that one fact
                    // is printed one way: s(t) + 1 ∈ ℤ is (t + 1) mod 10 + 1 ∈ ℤ.
                    let outside = crate::sorts::file_definitions(self.thm, self.env());
                    for fact in &here.hypotheses {
                        let read = crate::matching::expand(fact, &outside);
                        out.push(format!("{at} | {}", self.g.print(&read)));
                    }
                }
                Declined(_) => out.push(format!("{at} | declines")),
            }
        }
        if let Some(list) = &mut self.answers {
            list.extend(out);
        }
        Ok(())
    }

    /// What each sentence implies besides itself: the elaborator's answer
    /// (`implied_terms`) against the checker's (`implied_facts`). The step's
    /// claims and its requires lines are read with the member a claim said
    /// of every member names, as `does_work` reads them.
    pub fn list_implied(&mut self, step: &Step, sentences: &[Sentence]) -> Checked<()> {
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
                // Each answer spelt as the page spells it, and nothing else
                // forgiven: `nnne0` concludes set.mm's =/=, the elaborator
                // holds the page's denied equation as well, and the two are
                // one answer (`standard_spelling`).
                let spelt = |me: &Elaborator, t: &str| {
                    let term = me.standard_spelling(&me.to_term(t));
                    me.rpn(&term)
                };
                let mine: BTreeSet<String> = me
                    .implied_terms(&kernel)
                    .into_iter()
                    .map(|(implied, _)| spelt(me, &implied))
                    .collect();
                let mut theirs: BTreeSet<String> = BTreeSet::new();
                for implied in implied_facts(&node, env, &me.sorts_now) {
                    let term = me.term(&implied)?;
                    theirs.insert(spelt(me, &term));
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
