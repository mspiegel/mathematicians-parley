//! Every library item is cited by something that elaborates.
//!
//! An item's statement is written by hand and names the set.mm lemma it
//! means. The labels stage asks only that the lemma exists; whether the
//! statement says what the lemma says is found when a proof cites the item,
//! the elaborator applies the lemma, and the result verifies. An item
//! nothing cites has never been asked, and it can say anything.
//!
//! So each item is cited by a proof under `proof/`, or by its test under
//! `tests/stdlib/`: a theorem whose one step cites it. A test takes the
//! item's hypotheses as its own and claims the item's conclusion, or for a
//! definition the right side of it from the left. One direction is enough:
//! the lemma applied either way has the whole statement to match.
//!
//! An item marked `open` has no lemma to be asked against, and is not asked.
//! Nor is a definition that only introduces a symbol: it has no `then` line
//! for a step to claim, and what it says, the `defines` field, is written
//! into the library's definitions, which the verifier reads.

use indexmap::IndexSet;

use crate::corpus::{cited_items, corpus};
use crate::said::Said;
use crate::source::Source;

/// The items nothing cites, by full name.
pub fn untested(source: &dyn Source) -> Result<Vec<String>, crate::Problem> {
    let c = corpus(source)?;
    let cited: IndexSet<String> = c
        .theorems
        .iter()
        .flat_map(|t| cited_items(t).into_iter().map(|(full, _)| full))
        .collect();
    Ok(c.records
        .iter()
        .filter(|r| {
            r.kind.is_item()
                && !r.fields.contains_key("open")
                && !r.conclusions.is_empty()
                && !cited.contains(&r.qualified())
        })
        .map(|r| r.qualified())
        .collect())
}

pub fn run(source: &dyn Source) -> Said {
    let missing = match untested(source) {
        Ok(missing) => missing,
        Err(trouble) => {
            return Said {
                printed: String::new(),
                complained: format!("{trouble}\n"),
                status: 1,
            }
        }
    };
    let mut printed = String::new();
    for name in &missing {
        printed.push_str(&format!(
            "{name} is cited by no proof and has no test in tests/stdlib/\n"
        ));
    }
    if !missing.is_empty() {
        return Said {
            printed,
            complained: String::new(),
            status: 1,
        };
    }
    printed.push_str("every library item is cited by a proof or a test\n");
    Said {
        printed,
        complained: String::new(),
        status: 0,
    }
}
