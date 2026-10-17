//! What the checker hands the build, for a few theorems, as the build reads
//! it.
//!
//! The build decides nothing of the page: the checker's record of each
//! theorem says it (`record`). Each theorem's record is printed in the
//! page's notation and compared with the one kept under `tests/records/`,
//! so a change to any decision the build is handed shows as a changed line,
//! read in review as any other. Set `PARLEY_RECORD_WRITE=1` to write the
//! kept records anew.
//!
//! The theorems are chosen for the decisions they hold between them: an
//! induction and its parts, cases, both directions, citations read
//! forwards and backwards, a sum said once, and a chain.

use std::path::Path;

use parley::checker::checked;
use parley::source::Disk;

mod record;

/// The theorems whose records are kept, by full name.
const KEPT: [&str; 5] = [
    "proofs/wiedijk/euclid/euclid",
    "proofs/setmm/floor-quotient-zero/floor-quotient-zero",
    "proofs/wiedijk/triangular-reciprocals/triangular-reciprocals",
    "tests/docs/syntax/triangle-by-cases",
    "proofs/hammack/abs-limit-zero/abs-limit-zero",
];

/// Where a theorem's kept record is.
fn kept_at(root: &Path, name: &str) -> std::path::PathBuf {
    root.join("tests/records")
        .join(format!("{}.txt", name.replace('/', "--")))
}

#[test]
fn the_record_the_build_is_handed_is_the_one_kept() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let read = match checked(&Disk::new(root.to_path_buf())) {
        Ok(read) => read,
        Err(out) => panic!("the corpus does not check: {}", out.printed),
    };
    let write = std::env::var("PARLEY_RECORD_WRITE").is_ok();
    let mut differ = Vec::new();
    for name in KEPT {
        let now = record::printed_but(&read, name, &|_| false);
        let at = kept_at(root, name);
        if write {
            std::fs::create_dir_all(at.parent().unwrap()).unwrap();
            std::fs::write(&at, &now).unwrap();
            continue;
        }
        let kept = std::fs::read_to_string(&at).unwrap_or_default();
        if kept != now {
            differ.push(format!(
                "{name}: the record differs from {}\n--- kept\n{kept}--- now\n{now}",
                at.display()
            ));
        }
    }
    assert!(differ.is_empty(), "{}", differ.join("\n"));
}
