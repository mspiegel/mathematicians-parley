//! Set.mm's compressed proof format, which writes a repeated subproof once.
//!
//! A proof in normal format is a flat run of labels, and a subproof used
//! twice is written out twice. The corpus does that a great deal: in
//! deduction form every line carries the whole scope as an antecedent, so
//! the same membership is re-proved under the same scope wherever it is
//! wanted.
//!
//! The compressed format is what set.mm itself is stored in, and it says the
//! same proof with a way to point back. A step marked `Z` is kept, and a
//! later step that would repeat it names it instead. Nothing about the proof
//! changes and no verifier has to be told.
//!
//! What is kept is decided by counting. A subproof that stands in more than
//! one place is worth a name; one that stands in a single place is not, and
//! a subproof of one token is never worth it, since naming it costs as much
//! as writing it again.
//!
//! Indices are written in the format's own base: twenty values in `A` to `T`
//! for the last digit, and a bijective base five in `U` to `Y` above it. The
//! first indices are the theorem's own hypotheses, in the order the database
//! declares them; then the labels named in the parentheses; then, past
//! those, the steps that were kept.

use std::rc::Rc;

use indexmap::{IndexMap, IndexSet};

use super::library::Signatures;
use super::spell::{Step, StepRef};

/// 0 to 19: the last digit of an index.
pub const LAST: &[u8; 20] = b"ABCDEFGHIJKLMNOPQRST";
/// 1 to 5: the digits above it.
pub const HIGH: &[u8; 5] = b"UVWXY";

/// One index, written the way the format reads it.
pub fn letters(index: usize) -> String {
    let (mut high, last) = (index / 20, index % 20);
    let mut out = Vec::new();
    while high > 0 {
        let digit = (high - 1) % 5;
        high = (high - 1) / 5;
        out.push(HIGH[digit]);
    }
    out.reverse();
    out.push(LAST[last]);
    String::from_utf8(out).unwrap()
}

/// A subproof: its label and the numbers of its parts.
pub type Shape = (Rc<str>, Vec<usize>);

/// Every subproof of a proof in normal format, numbered so that two alike
/// share a number: the root's number, and the subproofs in the order each
/// is first finished.
pub fn shapes(proof: &str, sigs: &Signatures) -> Result<(usize, Vec<Shape>), String> {
    let mut seen: IndexMap<Shape, usize> = IndexMap::new();
    let mut kinds: Vec<Shape> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    for token in proof.split_whitespace() {
        let sig = sigs.get(token).ok_or_else(|| format!("no label {token}"))?;
        let count = sig.floats.len() + sig.essentials.len();
        let kids = stack.split_off(stack.len() - count);
        let key: Shape = (Rc::from(token), kids);
        let at = *seen.entry(key.clone()).or_insert_with(|| {
            kinds.push(key);
            kinds.len() - 1
        });
        stack.push(at);
    }
    if stack.len() != 1 {
        return Err(format!(
            "the proof leaves {} things on the stack",
            stack.len()
        ));
    }
    Ok((stack[0], kinds))
}

/// `shapes`, read off the steps a proof was built as.
///
/// The same numbering the text gives: each subproof numbered when it is
/// first finished, walking the parts left to right, which is the order the
/// text writes them in. A step reached again through another place that
/// uses it is already numbered, and so is one built apart but alike, by the
/// label and the numbers of its parts.
pub fn shapes_of(items: &[StepRef]) -> Result<(usize, Vec<Shape>), String> {
    if items.len() != 1 {
        return Err(format!(
            "the proof leaves {} things on the stack",
            items.len()
        ));
    }
    let mut seen: IndexMap<Shape, usize> = IndexMap::new();
    let mut kinds: Vec<Shape> = Vec::new();
    let mut number: IndexMap<*const Step, usize> = IndexMap::new();
    let mut work: Vec<(&StepRef, bool)> = vec![(&items[0], false)];
    while let Some((step, done)) = work.pop() {
        let id = Rc::as_ptr(step);
        if number.contains_key(&id) {
            continue;
        }
        if !step.kids.is_empty() && !done {
            work.push((step, true));
            work.extend(step.kids.iter().rev().map(|k| (k, false)));
            continue;
        }
        let key: Shape = (
            step.label.clone(),
            step.kids.iter().map(|k| number[&Rc::as_ptr(k)]).collect(),
        );
        let at = *seen.entry(key.clone()).or_insert_with(|| {
            kinds.push(key);
            kinds.len() - 1
        });
        number.insert(id, at);
    }
    Ok((number[&Rc::as_ptr(&items[0])], kinds))
}

/// How many places each subproof stands in, counted no higher than two.
///
/// Two is all the decision needs, and the true count is past counting. A
/// subproof is numbered after everything it holds, so one pass from the top
/// down reaches each before the things under it.
fn standing(root: usize, kinds: &[Shape]) -> Vec<u8> {
    let mut out = vec![0u8; kinds.len()];
    out[root] = 1;
    for at in (0..kinds.len()).rev() {
        if out[at] > 0 {
            for &kid in &kinds[at].1 {
                out[kid] = (out[kid] + out[at]).min(2);
            }
        }
    }
    out
}

/// One proof in normal format, said in the compressed one.
pub fn compress(
    proof: &str,
    mandatory: &[String],
    sigs: &Signatures,
) -> Result<String, String> {
    let (root, kinds) = shapes(proof, sigs)?;
    Ok(compressed(root, &kinds, mandatory))
}

/// Every label a proof applies, read off its shapes rather than its text.
pub fn labels(kinds: &[Shape]) -> IndexSet<Rc<str>> {
    kinds.iter().map(|(t, _)| t.clone()).collect()
}

/// The compressed format of a proof already read into its shapes.
pub fn compressed(root: usize, kinds: &[Shape], mandatory: &[String]) -> String {
    let often = standing(root, kinds);
    let keeping: IndexSet<usize> = kinds
        .iter()
        .enumerate()
        .filter(|(n, (_, kids))| !kids.is_empty() && often[*n] > 1)
        .map(|(n, _)| n)
        .collect();

    // The labels the parentheses name, in the order they are first written.
    // A theorem's own hypotheses are not among them: they are the indices
    // below, and naming them again would shift everything.
    let mut order: Vec<&str> = Vec::new();
    let mut seen: IndexSet<&str> = mandatory.iter().map(String::as_str).collect();
    for (token, _) in kinds {
        if seen.insert(token) {
            order.push(token);
        }
    }
    let mut index: IndexMap<&str, usize> = IndexMap::new();
    for (n, label) in mandatory.iter().enumerate() {
        index.insert(label, n);
    }
    for (n, label) in order.iter().enumerate() {
        index.insert(label, mandatory.len() + n);
    }
    let past = mandatory.len() + order.len();

    // Written without recursion. These run to millions of steps.
    let mut kept: IndexMap<usize, usize> = IndexMap::new();
    let mut out = String::new();
    let mut work: Vec<(usize, bool)> = vec![(root, false)];
    while let Some((at, done)) = work.pop() {
        if done {
            out.push_str(&letters(index[&*kinds[at].0]));
            if keeping.contains(&at) {
                let n = kept.len();
                kept.insert(at, n);
                out.push('Z');
            }
            continue;
        }
        if let Some(&n) = kept.get(&at) {
            out.push_str(&letters(past + n));
            continue;
        }
        work.push((at, true));
        work.extend(kinds[at].1.iter().rev().map(|&k| (k, false)));
    }
    format!("( {} ) {out}", order.join(" "))
}

/// The numbers a compressed proof's letters spell, a `Z` as None.
fn numbers(letters: &str) -> Vec<Option<usize>> {
    let mut out = Vec::new();
    let mut running = 0usize;
    for c in letters.bytes().filter(|c| !c.is_ascii_whitespace()) {
        if c == b'Z' {
            out.push(None);
        } else if let Some(at) = LAST.iter().position(|&l| l == c) {
            out.push(Some(20 * running + at));
            running = 0;
        } else if let Some(at) = HIGH.iter().position(|&h| h == c) {
            running = 5 * running + at + 1;
        }
    }
    out
}

fn block(said: &str, mandatory: &[String]) -> (Vec<String>, String) {
    let (head, rest) = said.split_once(')').unwrap_or((said, ""));
    let mut block: Vec<String> = mandatory.to_vec();
    block.extend(head.replace('(', "").split_whitespace().map(String::from));
    (block, rest.to_string())
}

/// A compressed proof read back as the steps it was written from, a
/// subproof the format saves being one step wherever it is used again.
pub fn expand_steps(
    said: &str,
    mandatory: &[String],
    sigs: &Signatures,
) -> Vec<StepRef> {
    let (block, rest) = block(said, mandatory);
    let mut stack: Vec<StepRef> = Vec::new();
    let mut saved: Vec<StepRef> = Vec::new();
    for number in numbers(&rest) {
        let Some(number) = number else {
            saved.push(stack[stack.len() - 1].clone());
            continue;
        };
        if number >= block.len() {
            stack.push(saved[number - block.len()].clone());
            continue;
        }
        let label = &block[number];
        let sig = &sigs[label.as_str()];
        let count = sig.floats.len() + sig.essentials.len();
        let kids = stack.split_off(stack.len() - count);
        stack.push(Rc::new(Step {
            label: Rc::from(label.as_str()),
            kids,
            typecode: Rc::from(sig.statement[0].as_str()),
        }));
    }
    stack
}

/// A compressed proof read back in normal format, for checking that it
/// says the same. Nothing in the build needs this.
pub fn expand(said: &str, mandatory: &[String], sigs: &Signatures) -> String {
    let (block, rest) = block(said, mandatory);
    let mut stack: Vec<String> = Vec::new();
    let mut saved: Vec<String> = Vec::new();
    for number in numbers(&rest) {
        match number {
            None => saved.push(stack[stack.len() - 1].clone()),
            Some(n) if n < block.len() => {
                let label = &block[n];
                let sig = &sigs[label.as_str()];
                let count = sig.floats.len() + sig.essentials.len();
                let mut args = stack.split_off(stack.len() - count);
                args.push(label.clone());
                stack.push(args.join(" "));
            }
            Some(n) => stack.push(saved[n - block.len()].clone()),
        }
    }
    stack.into_iter().next().unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One index read back the way a verifier reads it.
    fn decoded(said: &str) -> usize {
        numbers(said)[0].unwrap()
    }

    #[test]
    fn every_index_reads_back() {
        for index in (0..4000).chain([100_000, 1_000_000]) {
            assert_eq!(decoded(&letters(index)), index, "{}", letters(index));
        }
    }
}
