//! Which theorems the Lean build covers.
//!
//! A theorem is in the Lean build exactly when every notation its page uses
//! and every item it cites has a Lean form: a notation with a `lean-builds`
//! field, a record with a `lean-proof` field, or a theorem of the corpus that
//! is itself in. Nothing lists the theorems; the build grows as fields are
//! added. A theorem left
//! out is reported with what keeps it out.

use indexmap::IndexMap;

use super::templates::Templates;
use crate::checker::CheckedCorpus;
use crate::corpus::cited_items;

/// Whether a theorem is in the Lean build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Covered {
    In,
    /// Left out, and the first thing found that keeps it out.
    Out {
        reason: String,
    },
}

/// The notations the writer reads in code rather than by a `lean-builds` field:
/// letters, numerals, relations, memberships and quantifiers, whose Lean
/// form depends on the number types around them.
pub const IN_CODE: &[&str] = &[
    "name",
    "numeral",
    "equality",
    "order",
    "membership",
    "number-systems",
    "there-is",
    "for-all",
    "integer-range",
    "comma-conjunction",
    "function-type",
    "composition",
];

/// Every theorem of the corpus, in or out.
pub fn coverage(
    checked: &CheckedCorpus,
    templates: &Templates,
) -> IndexMap<String, Covered> {
    let mut out: IndexMap<String, Covered> = IndexMap::new();
    // A theorem citing another of the corpus is in only once that one is;
    // each pass settles at least the theorems whose citations are settled.
    loop {
        let mut changed = false;
        for thm in &checked.corpus.theorems {
            let name = thm.qualified();
            let covered = covered(checked, templates, &name, &out);
            if out.get(&name) != Some(&covered) {
                out.insert(name, covered);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    out
}

fn covered(
    checked: &CheckedCorpus,
    templates: &Templates,
    name: &str,
    so_far: &IndexMap<String, Covered>,
) -> Covered {
    let Some(thm) = checked
        .corpus
        .theorems
        .iter()
        .find(|t| t.qualified() == name)
    else {
        return Covered::Out {
            reason: "not a theorem of the corpus".to_string(),
        };
    };
    let Some(rec) = checked.theorems.get(name) else {
        return Covered::Out {
            reason: "the checker has not read it".to_string(),
        };
    };
    if !rec.problems.is_empty() {
        return Covered::Out {
            reason: "the checker refuses it".to_string(),
        };
    }
    // A letter the page gives a function type, `f : ℝ → ℝ`, is a Lean
    // function of its own; a composite of such is one too.
    let own: std::collections::BTreeSet<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter(|n| n.notation() == crate::notations::FUNCTION_TYPE)
        .filter_map(|n| {
            n.children
                .first()
                .filter(|f| f.is_name())
                .map(|f| f.text.to_string())
        })
        .collect();
    // A library function applied is in where its definition says what it
    // is in Lean (`lean-builds`).
    let mut notations: Vec<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter_map(|n| {
            let name = n.notation_name().to_string();
            if matches!(name.as_str(), "application" | "application-to-two") {
                let head = n.children.first()?;
                if !head.is_name() || own.contains(head.text.as_str()) {
                    return None;
                }
                let f = head.text.to_string();
                return templates.function(&f).is_none().then(|| {
                    format!("{f}, applied, whose definition has no lean-builds field")
                });
            }
            if n.notation() == crate::notations::FUNCTION_TYPE {
                let typed = matches!(n.children.as_slice(), [_, from, to]
                    if super::expr::function_systems(from, to).is_some());
                return (!typed).then(|| {
                    "a function type between sets Lean has no type for yet".to_string()
                });
            }
            (!IN_CODE.contains(&name.as_str()) && !templates.maps(&name))
                .then(|| format!("notation {name}, which has no lean-builds field"))
        })
        .collect();
    notations.sort();
    if let Some(first) = notations.first() {
        return Covered::Out {
            reason: format!("it writes {first}"),
        };
    }
    // A letter whose sort Lean has no type for yet: the writer types
    // numbers only.
    let mut letters: Vec<(String, String)> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter(|n| n.is_name() && templates.function(&n.text).is_none())
        .filter(|n| !own.contains(n.text.as_str()))
        .filter_map(|n| {
            let sort = rec.sorts.get(n.text.as_str())?;
            (!sort.is("number")).then(|| (n.text.to_string(), sort.describe()))
        })
        .collect();
    letters.sort();
    if let Some((letter, sort)) = letters.first() {
        return Covered::Out {
            reason: format!("{letter} is {sort}, which has no Lean type yet"),
        };
    }
    for (full, _) in cited_items(thm) {
        if let Some(record) = super::items::record_of(checked, &full) {
            if record.lean_target().is_none() {
                return Covered::Out {
                    reason: format!("{full} has no lean-proof field"),
                };
            }
            continue;
        }
        match so_far.get(&full) {
            Some(Covered::In) => {}
            _ => {
                return Covered::Out {
                    reason: format!("{full} is not in the Lean build"),
                }
            }
        }
    }
    Covered::In
}
