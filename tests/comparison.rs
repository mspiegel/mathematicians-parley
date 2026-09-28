//! Each hand-written comparison proof writes the file committed for it.

use std::path::Path;

use parley::proofs::comparison::COMPARISONS;

#[test]
fn every_comparison_writes_its_committed_file() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("corpus/elaboration");
    let mut differ = Vec::new();
    for c in &COMPARISONS {
        let path = root.join(format!("{}.mm", c.name));
        let committed = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        if (c.text)() != committed {
            differ.push(c.name);
        }
    }
    assert!(
        differ.is_empty(),
        "differ from the committed files: {differ:?}"
    );
}
