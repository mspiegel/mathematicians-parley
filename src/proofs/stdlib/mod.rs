//! `proved.mm`: what the library proves below the readable layer.
//!
//! The corpus supplies an item in one of three ways: a set.mm label, a proof
//! file in the readable layer, or a Metamath proof here, for what set.mm does
//! not state and the readable layer cannot. Each group of them is a text
//! file in `corpus/proved/`, written as a proof worksheet (`worksheet`), and
//! each is written in a block of its own, so what one group holds apart
//! (`$d`) holds nothing apart in another. A label is global all the same,
//! and a proof file that cites any of them includes this one file.

use crate::mm::compress::{compressed, shapes_of};
use crate::mm::{Builder, Signatures};
use crate::outcome::{Checked, Problem};

use super::Lemma;

/// The groups, in the order they are written: a later group may take a
/// label an earlier one proved. Each is `corpus/proved/<name>.proved`.
const NAMES: [&str; 18] = [
    "geometry",
    "parallels",
    "triangles",
    "series",
    "functions",
    "sets",
    "groups",
    "numbers",
    "divisors",
    "powers",
    "calculus",
    "totient",
    "bounds",
    "ranges",
    "polynomials",
    "counts",
    "graphs",
    "fractions",
];

const HEAD: &str = "$( stdlib/proved, built by parley build.

   What the library proves below the readable layer: facts this corpus
   needs, set.mm does not state, and the readable layer cannot. Each group
   stands in a block of its own. $)

$[ stdlib/definitions.mm $]

";

/// Where the worksheets `proved` reads are, each by its name.
pub const WORKSHEETS: &str = "corpus/proved/";

/// The text of `proved.mm`, from each group's worksheet, which `read` gives
/// by its path, and the library read alongside the corpus's definitions:
/// the angle is a constant this corpus introduces, `angval` says what a
/// value of it is, and discharging that needs `df-ang`.
pub fn proved(
    sigs: Signatures,
    read: &dyn Fn(&str) -> Option<String>,
) -> Checked<String> {
    let mut b = Builder::new(sigs);
    let mut out = String::from(HEAD);
    for name in NAMES {
        let path = format!("{WORKSHEETS}{name}.proved");
        let text =
            read(&path).ok_or_else(|| Problem::new(&path, 0, "cannot read it"))?;
        let group = super::worksheet::read(&path, &text, &mut b)?;
        out.push_str("${\n");
        out.push_str(&group.head);
        for lemma in &group.lemmas {
            out.push_str(&written(lemma, &b));
        }
        out.push_str("$}\n\n");
    }
    Ok(out)
}

/// One lemma as `proved.mm` writes it: in a block of its own where it
/// states hypotheses (`$e`), as set.mm's deductions do, and its proof
/// compressed, as the elaborator writes its proofs.
fn written(lemma: &Lemma, b: &Builder) -> String {
    let mut out = String::new();
    let hyps = &lemma.hyps;
    if !hyps.is_empty() {
        out.push_str("  ${\n");
        for (said, stated) in hyps {
            out.push_str(&format!("    {said} $e {stated} $.\n"));
        }
    }
    out.push_str(&format!("  {} $p {} $=\n", lemma.label, lemma.statement));
    // What a lemma takes is the variables of its statement and hypotheses,
    // then the hypotheses.
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
    out
}
