//! `parley build metamath` and `parley build lean`: the two backends, and
//! what they share.
//!
//! Each backend reads the page through the checker and writes one file for
//! each artifact it makes. What both need is here: an artifact and the
//! artifacts it waits on, the order they are made in, and writing a file
//! only where its text changed.

use std::collections::BTreeSet;
use std::path::Path;

use crate::outcome::{Checked, Problem};

pub mod lean;
pub mod metamath;

pub use metamath::*;

/// The check a build begins with (`checker::front`): what `parley check`
/// prints, which is the start of what the build prints, and the corpus as
/// read and recorded, which the backend builds from. A theorem the check
/// refuses is a failure the backend reports with what depends on it, and
/// the status is the check's. A problem outside every theorem has every
/// theorem depending on it, so the build ends with the check, and that is
/// the outcome.
pub fn checked_first(
    source: &dyn crate::source::Source,
) -> Result<(crate::said::Said, crate::checker::CheckedCorpus), crate::said::Said> {
    let all = |_: &crate::corpus::Theorem| true;
    let ask = crate::checker::Ask {
        wanted: &all,
        pairs: crate::checker::PairsAsked::Yes,
    };
    let front = crate::checker::front(source, &ask)?;
    let said = front.said();
    if !front.outside.problems.is_empty() {
        return Err(said);
    }
    Ok((said, front.checked))
}

/// One generated file: its name, what makes it, and the artifacts whose
/// files it reads or imports.
pub struct Artifact<R> {
    /// The artifact's name, which the backend turns into its path.
    pub name: String,
    pub recipe: R,
    pub needs: Vec<String>,
}

/// The artifacts in the order they are made: groups in which none reads
/// another's file, each group after every group it reads.
///
/// A `needs` naming something not being made is not waited for: asking for
/// one theorem remakes that theorem and not the library it reads.
///
/// Artifacts that wait on one another round a cycle can never be made. The
/// checker refuses theorems that cite one another so, and every caller
/// checks first, so a cycle here is a fault of the tool's.
pub fn waves<'a, R>(wanted: &[&'a Artifact<R>]) -> Checked<Vec<Vec<&'a Artifact<R>>>> {
    let here: BTreeSet<&str> = wanted.iter().map(|a| a.name.as_str()).collect();
    let mut done: BTreeSet<&str> = BTreeSet::new();
    let mut left: Vec<&Artifact<R>> = wanted.to_vec();
    let mut out = Vec::new();
    while !left.is_empty() {
        let (ready, rest): (Vec<&Artifact<R>>, Vec<&Artifact<R>>) =
            left.into_iter().partition(|a| {
                a.needs
                    .iter()
                    .all(|n| !here.contains(n.as_str()) || done.contains(n.as_str()))
            });
        if ready.is_empty() {
            let stuck: Vec<&str> = rest.iter().map(|a| a.name.as_str()).collect();
            return Err(Problem::internal(
                &rest[0].name,
                0,
                format!(
                    "these wait on one another and none can be built first: {}",
                    stuck.join(", ")
                ),
            ));
        }
        done.extend(ready.iter().map(|a| a.name.as_str()));
        out.push(ready);
        left = rest;
    }
    Ok(out)
}

/// Whether writing a file changed it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Written {
    Changed,
    Same,
}

/// Write `text` to `path` under `root`, making its directory, unless the
/// file already holds that text.
pub fn write_changed(root: &Path, path: &str, text: &str) -> Checked<Written> {
    let full = root.join(path);
    let before = std::fs::read_to_string(&full).ok();
    if before.as_deref() == Some(text) {
        return Ok(Written::Same);
    }
    full.parent()
        .map_or(Ok(()), std::fs::create_dir_all)
        .and_then(|()| std::fs::write(&full, text))
        .map_err(|e| Problem::new(full.display().to_string(), 0, e.to_string()))?;
    Ok(Written::Changed)
}
