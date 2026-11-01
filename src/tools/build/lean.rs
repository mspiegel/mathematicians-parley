//! `parley build lean`: every theorem the Lean build covers, written as a
//! Lean file over Mathlib under `lean/`.

use std::path::Path;

use crate::said::Said;

/// Build the theorem `wanted`, or every theorem the Lean build covers, in
/// the tree at `root`, writing each file that changed.
pub fn run(_root: &Path, _wanted: Option<&str>) -> Said {
    Said {
        complained: "the Lean writer is not built yet\n".to_string(),
        status: 2,
        ..Said::default()
    }
}
