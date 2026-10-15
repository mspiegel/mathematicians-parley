//! The deciders read kernel terms without set.mm, so `methods::terms`
//! declares each label it builds and how many terms it takes
//! (`VOCABULARY`). A label set.mm does not declare, or one it declares with
//! another number of variables, would build terms the build's set.mm terms
//! never match, and the checker and the build would read one line two
//! ways. This reads set.mm, and fails if set.mm cannot be found.

use std::path::Path;

use parley::methods::terms::VOCABULARY;
use parley::mm::{read, where_set_mm};

#[test]
fn every_label_the_deciders_build_is_set_mms_with_its_arity() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let setmm = where_set_mm(None, root).expect(
        "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
    );
    let sigs = read(&[setmm.as_path()]).expect("set.mm reads");
    let mut wrong = Vec::new();
    for (label, arity) in VOCABULARY {
        match sigs.get(*label) {
            None => wrong.push(format!("{label}: set.mm declares no such label")),
            Some(sig) if sig.floats.len() != *arity => wrong.push(format!(
                "{label}: VOCABULARY says {arity} terms, set.mm's statement takes {}",
                sig.floats.len()
            )),
            Some(_) => {}
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
}
