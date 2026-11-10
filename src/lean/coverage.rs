//! Which theorems the Lean build covers, by its fields.
//!
//! A theorem is taken in when every notation its page uses, every library
//! function it applies and every item it cites has a Lean form: a notation
//! with a `lean-builds` field, a function whose definition has one, a record
//! with a `lean-proof` field, or a theorem of the corpus that is itself in.
//! Nothing lists the theorems; the build grows as fields are added. These
//! are lookups of fields only. A form the writer has no way to write yet is
//! its own to find, where it meets it, as a decline that leaves the theorem
//! out (`Decline::left_out`). This module is scaffolding while the Lean
//! build covers less than the Metamath build, and goes at parity
//! (`docs/LEAN.md`, "Which theorems are in").

use indexmap::IndexMap;

use super::templates::Templates;
use crate::checker::CheckedCorpus;
use crate::corpus::cited_items;

/// Whether a theorem is in the Lean build.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Covered {
    In,
    /// Left out, and the first thing found that keeps it out: what the Lean
    /// build does not cover yet.
    Out {
        reason: String,
    },
    /// Not built because of a failure: the checker refuses it, or it cites
    /// a theorem not built because of one.
    Failed {
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
    "function-on",
    "composition",
    "sum",
    "product",
    "tends-to",
    "series",
    "integral",
    "derivative",
    "function-limit",
    "continuous",
    "closed-interval",
    "there-is-some",
    "holds-of",
    "subset",
    "set-operations",
    "empty-set",
    "powerset",
    "set-builder",
    "singleton",
    "listed-two",
    "listed-three",
    "listed-four",
    "image",
    "one-to-one",
    "onto",
    "one-to-one-onto",
    "inverse",
    "set-image",
    "cardinality",
    "finite",
    "group-operation",
    "group-inverse",
    "subgroup",
    "coset",
    "polynomials",
    "functions-from",
    "is-a-polynomial",
    "sum-over",
    "product-over",
    "differentiable",
    "open",
    "open-interval",
    "indexed-union",
    "bijection",
];

/// Every theorem of the corpus, in or out.
/// `stated` are the library's items whose statements the build wrote.
pub fn coverage(
    checked: &CheckedCorpus,
    templates: &Templates,
    stated: &std::collections::BTreeSet<String>,
) -> IndexMap<String, Covered> {
    let mut out: IndexMap<String, Covered> = IndexMap::new();
    // A theorem citing another of the corpus is in only once that one is;
    // each pass settles at least the theorems whose citations are settled.
    loop {
        let mut changed = false;
        for thm in &checked.corpus.theorems {
            let name = thm.qualified();
            let covered = covered(checked, templates, stated, &name, &out);
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
    stated: &std::collections::BTreeSet<String>,
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
    // Its file's functions written out where applied, as the writer reads
    // it (`CheckedTheorem::written`).
    let rec = super::theorem::as_written(rec);
    if !rec.problems.is_empty() {
        return Covered::Failed {
            reason: "the checker refuses it".to_string(),
        };
    }
    // A notation is in where its record says what it is in Lean
    // (`lean-builds`), and a library function applied where its definition
    // does.
    let functions = &checked.grammar.functions;
    let mut notations: Vec<String> = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .filter_map(|n| {
            let name = n.notation_name().to_string();
            if matches!(name.as_str(), "application" | "application-to-two") {
                let head = n.children.first()?;
                let f = head.text.to_string();
                let library = head.is_name() && functions.contains_key(&f);
                return (library && templates.function(&f).is_none()).then(|| {
                    format!("{f}, applied, whose definition has no lean-builds field")
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
    for (full, _) in cited_items(thm) {
        if let Some(record) = super::items::record_of(checked, &full) {
            // An item the Lean build cannot use yet keeps out what cites
            // it, and so does one proved by a Parley proof the build
            // leaves out; one with nothing to prove, or with Mathlib's
            // proof or a bridge, does not.
            use crate::corpus::records::Provided;
            match record.lean_provided() {
                Some(Provided::NotYet) | None => {
                    return Covered::Out {
                        reason: format!("{full}'s lean-proof is not yet implemented"),
                    };
                }
                Some(Provided::Proof(proof)) => {
                    if !matches!(so_far.get(proof), Some(Covered::In)) {
                        return Covered::Out {
                            reason: format!(
                                "{full} is proved by {proof}, which is not in the Lean build"
                            ),
                        };
                    }
                }
                // A proof whose item's statement the build could not write,
                // a phrase whose meaning it cannot state, is no proof yet.
                Some(Provided::By(_)) if !stated.contains(&full) => {
                    return Covered::Out {
                        reason: format!("{full}'s statement is not in the Lean build"),
                    };
                }
                Some(Provided::By(_) | Provided::Nothing) => {}
            }
            continue;
        }
        match so_far.get(&full) {
            Some(Covered::In) => {}
            Some(Covered::Failed { .. }) => {
                return Covered::Failed {
                    reason: format!("it cites {full}, which was not built"),
                }
            }
            _ => {
                return Covered::Out {
                    reason: format!("{full} is not in the Lean build"),
                }
            }
        }
    }
    Covered::In
}
