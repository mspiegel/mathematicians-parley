//! Where the tools read the working tree from.
//!
//! Everything a tool reads, it reads through a [`Source`], by the file's
//! path from the root of the working tree. [`Disk`] is the tree itself.
//! [`Overlay`] is a tree with some files replaced or added in memory, which
//! is how a planted-defect test edits one file without copying the corpus:
//! it applies its edit to an overlay and runs the tool over that.

use std::cmp::Ordering;
use std::io;
use std::path::{Path, PathBuf};

use indexmap::IndexMap;

pub trait Source {
    /// A file's bytes, by its path from the root.
    fn read(&self, rel: &str) -> io::Result<Vec<u8>>;

    /// Every file under the root outside a directory whose name starts with
    /// a dot, by path from the root with `/` between parts, in the order
    /// [`path_order`] sorts them.
    fn files(&self) -> Vec<String>;

    /// Whether a file is there.
    fn exists(&self, rel: &str) -> bool;

    /// The root on disk, where a tool has to hand a path to another program.
    fn root(&self) -> &Path;

    /// The files directly in `dir` whose name ends with `suffix`, sorted.
    fn listed(&self, dir: &str, suffix: &str) -> Vec<String> {
        let prefix = format!("{dir}/");
        self.files()
            .into_iter()
            .filter(|f| {
                f.strip_prefix(&prefix)
                    .is_some_and(|name| !name.contains('/') && name.ends_with(suffix))
            })
            .collect()
    }

    /// Every file anywhere under the root whose name ends with `suffix`.
    fn found(&self, suffix: &str) -> Vec<String> {
        self.files()
            .into_iter()
            .filter(|f| f.ends_with(suffix))
            .collect()
    }

    /// A file's text, which the corpus requires to be UTF-8.
    fn read_text(&self, rel: &str) -> io::Result<String> {
        let raw = self.read(rel)?;
        String::from_utf8(raw)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }
}

/// How paths are sorted: part by part, so that
/// `proof/a/x.proof` comes before `proof/a-b.proof`, which comparing the
/// whole strings would put the other way round.
pub fn path_order(a: &str, b: &str) -> Ordering {
    a.split('/').cmp(b.split('/'))
}

/// The working tree on disk.
pub struct Disk {
    root: PathBuf,
}

impl Disk {
    pub fn new(root: impl Into<PathBuf>) -> Self {
        Disk { root: root.into() }
    }
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if name.starts_with('.') {
            continue;
        }
        let path = entry.path();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            walk(root, &path, out);
        } else if let Ok(rel) = path.strip_prefix(root) {
            if let Some(rel) = rel.to_str() {
                out.push(rel.replace(std::path::MAIN_SEPARATOR, "/"));
            }
        }
    }
}

impl Source for Disk {
    fn read(&self, rel: &str) -> io::Result<Vec<u8>> {
        std::fs::read(self.root.join(rel))
    }

    fn files(&self) -> Vec<String> {
        let mut out = Vec::new();
        walk(&self.root, &self.root, &mut out);
        out.sort_by(|a, b| path_order(a, b));
        out
    }

    fn exists(&self, rel: &str) -> bool {
        self.root.join(rel).is_file()
    }

    fn root(&self) -> &Path {
        &self.root
    }
}

/// Some directories of a tree, held in memory.
///
/// What a planted-defect test starts from: the corpus, read once, which each
/// case then edits through an [`Overlay`] of its own.
pub struct Memory {
    root: PathBuf,
    files: IndexMap<String, Vec<u8>>,
}

impl Memory {
    /// The files under `dirs` of another source, as they are now.
    pub fn copy(from: &dyn Source, dirs: &[&str]) -> io::Result<Memory> {
        let mut files = IndexMap::new();
        for rel in from.files() {
            let top = rel.split('/').next().unwrap_or("");
            if dirs.contains(&top) {
                let bytes = from.read(&rel)?;
                files.insert(rel, bytes);
            }
        }
        Ok(Memory {
            root: from.root().to_path_buf(),
            files,
        })
    }
}

impl Source for Memory {
    fn read(&self, rel: &str) -> io::Result<Vec<u8>> {
        self.files
            .get(rel)
            .cloned()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotFound, rel.to_string()))
    }

    fn files(&self) -> Vec<String> {
        self.files.keys().cloned().collect()
    }

    fn exists(&self, rel: &str) -> bool {
        self.files.contains_key(rel)
    }

    fn root(&self) -> &Path {
        &self.root
    }
}

/// A tree with some files replaced or added in memory.
pub struct Overlay<'a> {
    base: &'a dyn Source,
    changed: IndexMap<String, Vec<u8>>,
}

impl<'a> Overlay<'a> {
    pub fn new(base: &'a dyn Source) -> Self {
        Overlay {
            base,
            changed: IndexMap::new(),
        }
    }

    /// Replace a file, or add one that is not there.
    pub fn write(&mut self, rel: &str, bytes: Vec<u8>) {
        self.changed.insert(rel.to_string(), bytes);
    }
}

impl Source for Overlay<'_> {
    fn read(&self, rel: &str) -> io::Result<Vec<u8>> {
        match self.changed.get(rel) {
            Some(bytes) => Ok(bytes.clone()),
            None => self.base.read(rel),
        }
    }

    fn files(&self) -> Vec<String> {
        let mut out = self.base.files();
        for rel in self.changed.keys() {
            let hidden = rel.split('/').any(|part| part.starts_with('.'));
            if !hidden && !out.contains(rel) {
                out.push(rel.clone());
            }
        }
        out.sort_by(|a, b| path_order(a, b));
        out
    }

    fn exists(&self, rel: &str) -> bool {
        self.changed.contains_key(rel) || self.base.exists(rel)
    }

    fn root(&self) -> &Path {
        self.base.root()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paths_sort_part_by_part() {
        let mut paths = vec!["proof/a-b.proof", "proof/a/x.proof", "db/n.records"];
        paths.sort_by(|a, b| path_order(a, b));
        assert_eq!(
            paths,
            vec!["db/n.records", "proof/a/x.proof", "proof/a-b.proof"]
        );
    }
}
