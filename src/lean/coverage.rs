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
    "sum",
    "product",
    "tends-to",
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

/// Whether any reason of the theorem is the method `real arithmetic`: a
/// step's own, a requires line's, a calculation row's, or the equation a
/// substitution works out where it stands; or a line said to be impossible,
/// which arithmetic works out false.
fn uses_real_arithmetic(thm: &crate::corpus::Theorem) -> bool {
    use crate::corpus::Method;
    let real = |j: &crate::corpus::Justification| {
        j.head.method() == Some(Method::RealArithmetic)
    };
    thm.steps.iter().any(|step| {
        let rows = match crate::corpus::proof::chain(&step.just, &thm.path) {
            Some(Ok(chain)) => chain.lines.iter().any(|l| {
                l.cite == Method::RealArithmetic.as_str()
                    || l.reason
                        .as_ref()
                        .is_some_and(|r| r.by.as_ref().is_ok_and(real))
            }),
            _ => false,
        };
        let in_place = matches!(
            step.just.source,
            Some(crate::corpus::skeleton::Source::RealArithmetic)
        );
        real(&step.just)
            || rows
            || in_place
            || step.impossible
            || step.requires.iter().any(|r| r.by.as_ref().is_ok_and(real))
    })
}

/// The function a proof's define line gives, where the Lean build writes it
/// (`Proof::define_function`): one argument, running over a number system,
/// `let S(m) = …, for m ∈ ℕ`. None for any other line.
pub fn defined_function(
    line: &crate::corpus::DefineLine,
    rec: &crate::checker::CheckedTheorem,
) -> Option<String> {
    let crate::outcome::Route::Built(crate::corpus::DefineParts::One(def)) =
        crate::corpus::define_parts(&line.text)
    else {
        return None;
    };
    let [param] = def.params.as_slice() else {
        return None;
    };
    let read: Vec<&crate::formula::Node> = rec
        .page
        .entries()
        .filter(|(key, _)| key.line == line.line)
        .map(|(_, node)| node)
        .collect();
    let over_numbers = read.iter().any(|n| {
        n.notation() == crate::notations::NUMBER_SYSTEMS
            && super::expr::system_of(n).is_some()
    });
    let values = read
        .iter()
        .filter(|n| n.notation() != crate::notations::NUMBER_SYSTEMS)
        .filter(|n| !(n.is_name() && *n.text == *param.name))
        .count();
    (over_numbers && values == 1).then(|| def.name.clone())
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
    // A `let` that says a property beside a type, `let a : A → B be
    // one-to-one`, is read part by part, which the writer does not read yet.
    let in_parts = thm.hypotheses.iter().any(|h| {
        h.body(&thm.path)
            .sentences()
            .iter()
            .any(|s| rec.page.get(s).is_none())
    });
    if in_parts {
        return Covered::Out {
            reason: "a let line says a property beside a type, which the Lean build does not read yet"
                .to_string(),
        };
    }
    // Real arithmetic of √, π, ln, exp, sin or cos, √8 = 2√2 or 3 < π, has
    // no Lean tactic yet that decides it.
    let transcendental =
        rec.page
            .entries()
            .flat_map(|(_, node)| node.walk())
            .any(|n| {
                matches!(&*n.notation_name(), "square-root" | "pi")
                    || (matches!(
                        n.notation(),
                        crate::notations::APPLICATION
                            | crate::notations::APPLICATION_TO_TWO
                    ) && n.children.first().is_some_and(|f| {
                        matches!(&*f.text, "cos" | "sin" | "exp" | "ln" | "tan")
                    }))
            });
    // A limit's proof writes its claims of natural numbers, |1/n − 1| < 1/2,
    // in ℚ, their least type, beside the sequence's lines in ℝ, and Lean does
    // not carry one to the other under the quantifiers.
    let limit = rec
        .page
        .entries()
        .flat_map(|(_, node)| node.walk())
        .any(|n| &*n.notation_name() == "tends-to");
    if limit {
        return Covered::Out {
            reason: "a limit, whose claims of natural numbers the Lean build writes in ℚ beside the sequence's lines in ℝ"
                .to_string(),
        };
    }
    if transcendental && uses_real_arithmetic(thm) {
        return Covered::Out {
            reason: "real arithmetic of √, π, ln, exp, sin or cos, which the Lean build cannot yet decide"
                .to_string(),
        };
    }
    // A letter the page gives a function type, `f : ℝ → ℝ`, is a Lean
    // function of its own; a composite of such is one too; and so is a
    // function the proof defines, `let S(m) = …, for m ∈ ℕ`.
    let mut own: std::collections::BTreeSet<String> = rec
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
    // Only a define in the proof below the statement: one in the statement
    // is part of what the theorem says, which the statement writer reads.
    for line in thm.defines.iter().filter(|d| d.line > thm.conclusion_line) {
        if let Some(name) = defined_function(line, rec) {
            own.insert(name);
        }
    }
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
                Some(Provided::By(_) | Provided::Nothing) => {}
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
