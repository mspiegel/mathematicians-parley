//! A compressed proof is the proof it was made from.
//!
//! The compressed format rewrites a proof into the form set.mm is stored in,
//! and the whole of what makes that safe is that nothing about the proof
//! changes. A verifier is the other half of the answer and the gate runs
//! one, but a verifier says only that what it read is a proof; it cannot say
//! that what it read is the proof the elaborator built. This can, because
//! the format is reversible.
//!
//! So every proof in the corpus is read back into the steps it was written
//! from and written out again, and the two compressed forms must be the same
//! text; one small enough to write out in normal format is read back as that
//! too. A round trip through both directions catches an index written wrong,
//! a saved step named before it was kept, and a label block out of order.
//!
//! This reads set.mm, and fails if set.mm cannot be found: a test that
//! skipped would say green about a thing it had not looked at.

use std::collections::BTreeSet;
use std::path::Path;
use std::rc::Rc;

use parley::mm::compress::{
    compress, compressed, expand, expand_steps, shapes, shapes_of,
};
use parley::mm::{read, where_set_mm, Builder, Kind, Layered, Signature, StepRef};
use parley::source::{Disk, Source};

/// The most labels a proof is also written out in normal format at.
const STEPPED: usize = 1_000_000;

/// How many labels the steps come to written out, counted without writing
/// them: each step's length once, however often it is used.
fn written_length(items: &[StepRef]) -> usize {
    let mut length: indexmap::IndexMap<*const parley::mm::Step, usize> =
        indexmap::IndexMap::new();
    let mut work: Vec<(&StepRef, bool)> = items.iter().map(|s| (s, false)).collect();
    while let Some((step, done)) = work.pop() {
        let id = std::rc::Rc::as_ptr(step);
        if length.contains_key(&id) {
            continue;
        }
        if !step.kids.is_empty() && !done {
            work.push((step, true));
            work.extend(step.kids.iter().map(|k| (k, false)));
            continue;
        }
        let n = 1 + step
            .kids
            .iter()
            .map(|k| length[&std::rc::Rc::as_ptr(k)])
            .sum::<usize>();
        length.insert(id, n);
    }
    items.iter().map(|s| length[&std::rc::Rc::as_ptr(s)]).sum()
}

parley::regex!(PROVED, r"(?ms)^\s*(\S+)\s+\$p\s+(.*?)\$=(.*?)\$\.");
parley::regex!(HYPOTHESIS, r"(?ms)^\s*(\S+)\s+\$e\s+(.*?)\$\.");

#[test]
fn every_compressed_proof_survives_a_round_trip() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let setmm = where_set_mm(None, root)
        .expect("set.mm not found; say where it is with SET_MM, or leave a copy or a link at the root of the working tree");
    let disk = Disk::new(root);
    let built: Vec<String> = disk
        .found(".mm")
        .into_iter()
        .filter(|p| p.starts_with("elaboration/"))
        .collect();
    let mut paths: Vec<std::path::PathBuf> = vec![setmm];
    paths.extend(built.iter().map(|p| root.join(p)));
    let refs: Vec<&Path> = paths.iter().map(|p| p.as_path()).collect();
    // Read once and shared: each proof layers its own hypotheses over it.
    let sigs = Rc::new(read(&refs).unwrap());
    let spell = Builder::new(Layered::new(Rc::clone(&sigs)));

    let (mut passed, mut stepped) = (0, 0);
    let mut failed: Vec<String> = Vec::new();
    for rel in &built {
        let whole = disk.read_text(rel).unwrap();
        for found in PROVED.captures_iter(&whole) {
            let start = found.get(0).unwrap().start();
            let label = &found[1];
            let says = &found[2];
            let said = found[3].split_whitespace().collect::<Vec<_>>().join(" ");
            if !said.starts_with('(') {
                continue; // normal format, nothing to check
            }
            // A lemma may state hypotheses in a block of its own: they come
            // after its variables among what the compressed format takes as
            // given.
            let opened = [whole[..start].rfind("${"), whole[..start].rfind("$}")]
                .into_iter()
                .flatten()
                .max();
            let block = opened.map_or("", |at| &whole[at..start]);
            let hyps: Vec<(String, String)> = HYPOTHESIS
                .captures_iter(block)
                .map(|c| (c[1].to_string(), c[2].to_string()))
                .collect();
            let mut local = Layered::new(Rc::clone(&sigs));
            for (h, s) in &hyps {
                local.insert(
                    h.clone(),
                    Signature {
                        label: h.clone(),
                        kind: Kind::Essential,
                        statement: s.split_whitespace().map(String::from).collect(),
                        floats: Vec::new(),
                        essentials: Vec::new(),
                        disjoint: BTreeSet::new(),
                    },
                );
            }
            // The same reckoning the elaborator makes when it writes one.
            let words: Vec<&str> = std::iter::once(says)
                .chain(hyps.iter().map(|(_, s)| s.as_str()))
                .flat_map(|s| s.split_whitespace())
                .collect();
            let floats: BTreeSet<&String> =
                words.iter().filter_map(|t| spell.flabel.get(t)).collect();
            let mut mandatory: Vec<String> = floats.into_iter().cloned().collect();
            mandatory.sort_by_key(|one| spell.forder[one]);
            mandatory.extend(hyps.iter().map(|(h, _)| h.clone()));
            // Read back as the steps it was written from, which is how the
            // elaborator writes it, and written again from those.
            let items = expand_steps(&said, &mandatory, &local);
            let (r, kinds) = shapes_of(&items).unwrap();
            if compressed(r, &kinds, &mandatory) == said {
                passed += 1;
            } else {
                failed.push(format!("  NOT THE SAME  {label} in {rel}"));
            }
            // And, where it is small enough to write out, read back as text
            // too: the two readings must number the proof alike.
            if written_length(&items) < STEPPED {
                let text = expand(&said, &mandatory, &local);
                let again = compress(&text, &mandatory, &local).unwrap();
                if again == said && shapes_of(&items) == shapes(&text, &local) {
                    stepped += 1;
                } else {
                    failed
                        .push(format!("  STEPS NUMBERED OTHERWISE  {label} in {rel}"));
                }
            }
        }
    }
    println!(
        "{passed} proof(s) survive a round trip, {} do not; {stepped} numbered alike from their steps",
        failed.len()
    );
    assert!(failed.is_empty(), "{}", failed.join("\n"));
    assert!(passed > 0, "no compressed proof was found to check");
}
