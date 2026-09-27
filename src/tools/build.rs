//! Building what this project generates: each theorem's elaborated file.

use std::path::Path;

use crate::corpus::{corpus, index};
use crate::elab::elaborate::Options;
use crate::elab::{elaborate, statement_of, Elaborated, Library};
use crate::formula::Grammar;
use crate::mm::library::where_set_mm;
use crate::outcome::{Checked, Problem};
use crate::source::{Disk, Source};

use super::path_of;

/// The library a build reads: set.mm, where the command line, the
/// environment or the root of the tree says, and the corpus's `proved.mm`
/// where it has been built.
pub fn library(root: &Path, setmm: Option<&str>) -> Checked<Library> {
    let Some(setmm) = where_set_mm(setmm, root) else {
        return Err(Problem::new(
            "set.mm",
            0,
            "no set.mm: pass one, or set SET_MM",
        ));
    };
    let proved = root.join(path_of("stdlib/proved"));
    let proved = proved.exists().then_some(proved);
    Library::read(&setmm, proved.as_deref())
}

/// Elaborate the theorem `name` of the corpus `source` holds.
///
/// A theorem it cites is read from the file already written for it in the
/// same tree, for the order of what a citation pushes.
pub fn elaborate_one(
    source: &dyn Source,
    name: &str,
    library: &Library,
    options: Options,
) -> Checked<Elaborated> {
    let found = corpus(source)?;
    let g = Grammar::load(&found.records)?;
    let items = index(&found.records, &found.theorems);
    let Some(thm) = found.theorems.iter().find(|t| t.qualified() == name) else {
        return Err(Problem::new(name, 0, format!("no theorem {name}")));
    };
    let statements = |cited: &str| -> Option<String> {
        let text = source.read_text(&path_of(cited)).ok()?;
        statement_of(&text)
    };
    elaborate(&found, &g, &items, thm, library, &statements, options)
}

/// Elaborate one theorem of the corpus at `root` and write its file, giving
/// back whether the file changed.
pub fn build_one(root: &Path, name: &str, setmm: Option<&str>) -> Checked<bool> {
    let source = Disk::new(root.to_path_buf());
    let library = library(root, setmm)?;
    let made = elaborate_one(&source, name, &library, Options::default())?;
    let path = root.join(path_of(name));
    let before = std::fs::read_to_string(&path).ok();
    if before.as_deref() == Some(made.text.as_str()) {
        return Ok(false);
    }
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir)
            .map_err(|e| Problem::new(path.display().to_string(), 0, e.to_string()))?;
    }
    std::fs::write(&path, &made.text)
        .map_err(|e| Problem::new(path.display().to_string(), 0, e.to_string()))?;
    Ok(true)
}
