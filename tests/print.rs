//! A formula the tools print reads back as the formula printed.
//!
//! Messages name facts the checker built rather than cut from the page, so
//! they print them (`Grammar::print`). Every sentence the corpus claims or
//! requires is read, printed, and read again, and the two trees must agree.

use std::path::Path;

use parley::check::printed_back;
use parley::source::Disk;

#[test]
fn every_formula_prints_as_it_reads() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let (read, differ) = match printed_back(&Disk::new(root.to_path_buf())) {
        Ok(found) => found,
        Err(out) => panic!("the corpus does not read: {}", out.complained),
    };
    // A test over nothing says nothing: the corpus has well over a thousand.
    assert!(read > 1000, "only {read} formulas were read");
    println!("{read} formulas read, printed and read again");
    assert!(
        differ.is_empty(),
        "{} formula(s) print as something else:\n{}",
        differ.len(),
        differ.join("\n")
    );
}
