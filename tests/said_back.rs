//! A term the elaborator names in a message is said as the page says it.
//!
//! Messages say kernel terms back in the page's notation (`spoken`), and a
//! translation that read back as another term would name the wrong fact.
//! Every theorem is elaborated with each sentence its steps claim said back
//! and read again, and the two terms must agree. This reads set.mm, and fails
//! if set.mm cannot be found.

use std::path::Path;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{library, Loaded};

#[test]
fn every_claim_is_said_back_as_itself() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let tree = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let names: Vec<String> = corpus(&tree)
        .expect("the corpus reads")
        .theorems
        .iter()
        .map(|t| t.qualified())
        .collect();
    let options = Options {
        say_back: true,
        ..Options::default()
    };
    let lib = library(root, None).expect(
        "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
    );
    let loaded = Loaded::new(&tree).expect("the corpus reads");
    let mut differ: Vec<String> = Vec::new();
    for name in &names {
        match loaded.elaborate(name, &lib, options) {
            Ok(done) => differ.extend(done.said_back),
            Err(p) => differ.push(format!("{name} fails: {p}")),
        }
    }
    println!("{} theorems said back", names.len());
    assert!(
        differ.is_empty(),
        "{} sentence(s) are said back as something else:\n{}",
        differ.len(),
        differ.join("\n")
    );
}
