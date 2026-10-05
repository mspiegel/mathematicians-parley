//! A term the elaborator names in a message is said as the page says it.
//!
//! Messages say kernel terms back in the page's notation (`spoken`), and a
//! translation that read back as another term would name the wrong fact.
//! Every theorem is elaborated with each sentence its steps claim said back
//! and read again, and the two terms must agree. This reads set.mm, and fails
//! if set.mm cannot be found.

use std::path::Path;
use std::sync::Mutex;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::source::{Disk, Memory};
use parley::tools::build::{elaborate_one, library};

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
    let differ = Mutex::new(Vec::new());
    let next = Mutex::new(names.iter());
    // Each worker loads set.mm once for itself: the library is not shared
    // between threads.
    let workers = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .clamp(1, 8);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                let lib = library(root, None).expect(
                    "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
                );
                loop {
                    let Some(name) = next.lock().unwrap().next() else {
                        break;
                    };
                    match elaborate_one(&tree, name, &lib, options) {
                        Ok(done) => differ.lock().unwrap().extend(done.said_back),
                        Err(p) => {
                            differ.lock().unwrap().push(format!("{name} fails: {p}"))
                        }
                    }
                }
            });
        }
    });
    let differ = differ.into_inner().unwrap();
    println!("{} theorems said back", names.len());
    assert!(
        differ.is_empty(),
        "{} sentence(s) are said back as something else:\n{}",
        differ.len(),
        differ.join("\n")
    );
}
