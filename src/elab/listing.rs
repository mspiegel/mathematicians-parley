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

use crate::check::implied_facts;
use crate::corpus::Step;
use crate::outcome::Checked;
use crate::sorts::Env;

use super::state::Elaborator;

impl Elaborator<'_> {
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
