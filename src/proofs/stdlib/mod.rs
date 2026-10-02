//! `proved.mm`: what the library proves below the readable layer.
//!
//! The corpus supplies an item in one of three ways: a set.mm label, a proof
//! file in the readable layer, or a Metamath proof here, for what set.mm does
//! not state and the readable layer cannot. Each group of them is a module
//! of its own, and each is written in a block of its own, so what one group
//! holds apart (`$d`) holds nothing apart in another. A label is global all
//! the same, and a proof file that cites any of them includes this one file.

pub mod calculus;
pub mod divisors;
pub mod functions;
pub mod geometry;
pub mod groups;
pub mod numbers;
pub mod series;
pub mod sets;

use crate::mm::compress::{compressed, shapes_of};
use crate::mm::{Builder, Signatures};

use super::Lemma;

/// One group: what its block says first, and its lemmas.
struct Group {
    head: &'static str,
    proofs: fn(&mut Builder) -> Vec<Lemma>,
}

/// The groups, in the order they are written: a later group may take a
/// label an earlier one proved.
const GROUPS: [Group; 8] = [
    Group {
        head: geometry::HEAD,
        proofs: geometry::proofs,
    },
    Group {
        head: series::HEAD,
        proofs: series::proofs,
    },
    Group {
        head: functions::HEAD,
        proofs: functions::proofs,
    },
    Group {
        head: sets::HEAD,
        proofs: sets::proofs,
    },
    Group {
        head: groups::HEAD,
        proofs: groups::proofs,
    },
    Group {
        head: numbers::HEAD,
        proofs: numbers::proofs,
    },
    Group {
        head: divisors::HEAD,
        proofs: divisors::proofs,
    },
    Group {
        head: calculus::HEAD,
        proofs: calculus::proofs,
    },
];

const HEAD: &str = "$( stdlib/proved, built by parley build.

   What the library proves below the readable layer: facts this corpus
   needs, set.mm does not state, and the readable layer cannot. Each group
   stands in a block of its own. $)

$[ stdlib/definitions.mm $]

";

/// The text of `proved.mm`, from the library read alongside the corpus's
/// definitions: the angle is a constant this corpus introduces, `angval`
/// says what a value of it is, and discharging that needs `df-ang`.
pub fn proved(sigs: Signatures) -> String {
    let mut b = Builder::new(sigs);
    let mut out = String::from(HEAD);
    for group in &GROUPS {
        out.push_str("${\n");
        out.push_str(group.head);
        for lemma in (group.proofs)(&mut b) {
            // A lemma may state hypotheses (`$e`), as set.mm's deductions
            // do; they stand in a block of their own with it.
            let hyps = &lemma.hyps;
            if !hyps.is_empty() {
                out.push_str("  ${\n");
                for (said, stated) in hyps {
                    out.push_str(&format!("    {said} $e {stated} $.\n"));
                }
            }
            out.push_str(&format!("  {} $p {} $=\n", lemma.label, lemma.statement));
            // Compressed, as the elaborator writes its proofs. What a lemma
            // takes is the variables of its statement and hypotheses, then
            // the hypotheses.
            let words: Vec<&str> = std::iter::once(lemma.statement.as_str())
                .chain(hyps.iter().map(|(_, s)| s.as_str()))
                .flat_map(|s| s.split_whitespace())
                .collect();
            let mut floats: Vec<String> = words
                .iter()
                .filter_map(|t| b.flabel.get(t).cloned())
                .collect::<std::collections::BTreeSet<_>>()
                .into_iter()
                .collect();
            floats.sort_by_key(|one| b.forder[one]);
            let mut mandatory = floats;
            mandatory.extend(hyps.iter().map(|(said, _)| said.clone()));
            let (root, kinds) = shapes_of(&lemma.proof.items)
                .unwrap_or_else(|e| panic!("{}: {e}", lemma.label));
            let said = compressed(root, &kinds, &mandatory);
            let mut line = String::from("   ");
            for token in said.split_whitespace() {
                if line.len() + token.len() > 76 {
                    out.push_str(&line);
                    out.push('\n');
                    line = String::from("   ");
                }
                line.push(' ');
                line.push_str(token);
            }
            out.push_str(&format!("{line} $.\n"));
            if !hyps.is_empty() {
                out.push_str("  $}\n");
            }
            out.push('\n');
        }
        out.push_str("$}\n\n");
    }
    out
}
