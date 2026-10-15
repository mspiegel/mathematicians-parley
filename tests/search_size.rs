//! The citation search over the corpus stays small.
//!
//! The search for which facts supply an item's hypotheses backtracks, and a
//! backtracking search can grow with every arrangement of the facts. A
//! search that has grown is slow before it is wrong, and a slow check is
//! found by waiting; this finds it by count. The count is how many times
//! one search asked a hypothesis of the facts (`largest_search`).

use std::path::Path;

use parley::citing::largest_search;
use parley::source::Disk;

/// The most one search over the corpus may ask, with room above what the
/// corpus asks for proofs still to be written.
const LIMIT: usize = 1_000;

#[test]
fn no_citation_search_over_the_corpus_grows_large() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let said = parley::checker::run(&Disk::new(root));
    assert!(said.green(), "the corpus checks:\n{}", said.printed);
    let largest = largest_search();
    println!("the largest citation search asked {largest} hypotheses");
    assert!(
        largest <= LIMIT,
        "a citation search asked {largest} hypotheses, more than {LIMIT}"
    );
}
