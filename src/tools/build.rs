//! Every file this project generates, what generates it, and where it goes.
//!
//! What there is to build is read off the tree rather than listed. Every
//! theorem of a `.proof` file is elaborated; the library's definitions and
//! the proofs below the readable layer are written first; and the
//! hand-written comparison proofs are written beside them. A file's path
//! under `corpus/elaboration/` is its name with `.mm`, so the theorem
//! `proofs/bezout/bezout` is written to
//! `corpus/elaboration/proofs/bezout/bezout.mm`, and a file including it says
//! so.
//!
//! Which artifact has to exist before which is a real constraint, and
//! `needs` is where it is written. `stdlib/definitions` comes before
//! `stdlib/proved`, which reads it for the constant it introduces; every
//! library file comes before any theorem, because a `target` may name one of
//! their labels; and a theorem waits for the theorems it cites. What an
//! artifact reads is taken from what this run made, and otherwise from the
//! file already in the tree.
//!
//! Nothing here notices that an artifact is out of date on its own; the gate
//! does, by building every artifact and comparing it with the committed file.

use std::collections::BTreeSet;
use std::path::Path;

use indexmap::IndexMap;

use crate::corpus::{cited_items, corpus, in_stdlib, index, Corpus, Item};
use crate::elab::definitions::write_definitions;
use crate::elab::elaborate::Options;
use crate::elab::{elaborate, statement_of, Elaborated, Library};
use crate::formula::Grammar;
use crate::mm::library::where_set_mm;
use crate::mm::read_texts;
use crate::outcome::{Checked, Problem};
use crate::proofs::comparison::COMPARISONS;
use crate::said::Said;
use crate::source::{Disk, Source};

use super::path_of;

/// The library's definitions, which everything reads.
pub const DEFINITIONS: &str = "stdlib/definitions";
/// What the library proves below the readable layer.
pub const PROVED: &str = "stdlib/proved";

/// What the process may take at its peak before the build fails. A proof is
/// built as steps that share their parts (`spell::Step`); built as text,
/// with every shared part written out again, the intermediate value theorem
/// took 6GB. The limit is well above what a build needs and well below that,
/// so a build that grows past it is reported rather than left to the
/// machine.
pub const MEMORY_LIMIT: u64 = 2 << 30;

/// How an artifact is made.
#[derive(Clone, Copy)]
pub enum Recipe {
    /// `definitions.mm`, from the records and set.mm.
    Definitions,
    /// `proved.mm`, from `proofs::stdlib` over set.mm and the definitions.
    Proved,
    /// A theorem of the corpus, elaborated.
    Theorem,
    /// A hand-written comparison proof, which reads nothing.
    ByHand(fn() -> String),
}

/// One generated file: what makes it, and the artifacts whose files it
/// reads.
pub struct Artifact {
    /// Its path under `corpus/elaboration/`, without `.mm`.
    pub name: String,
    pub recipe: Recipe,
    pub needs: Vec<String>,
}

impl Artifact {
    pub fn path(&self) -> String {
        path_of(&self.name)
    }

    fn wants_library(&self) -> bool {
        !matches!(self.recipe, Recipe::ByHand(_))
    }
}

/// Every file this project generates, read off the corpus.
///
/// In the order they are reported: the library's files, the theorems in the
/// order their proof files are read, and the hand-written proofs that
/// `ELABORATION.md` compares with the elaborated ones.
pub fn artifacts(found: &Corpus) -> Vec<Artifact> {
    let mut out = vec![
        Artifact {
            name: DEFINITIONS.to_string(),
            recipe: Recipe::Definitions,
            needs: Vec::new(),
        },
        Artifact {
            name: PROVED.to_string(),
            recipe: Recipe::Proved,
            needs: vec![DEFINITIONS.to_string()],
        },
    ];
    let reads: Vec<String> = out.iter().map(|a| a.name.clone()).collect();
    let ours: BTreeSet<String> = found.theorems.iter().map(|t| t.qualified()).collect();
    for thm in &found.theorems {
        let name = thm.qualified();
        // A proof citing another proof's theorem pushes a term for each
        // variable of that statement in the order that theorem's file
        // declares them, and two proofs need not spell a statement's bound
        // names alike. So that theorem is made first. Which theorems those
        // are is read off the citations, the same way the checker reads
        // them.
        let mut needs = reads.clone();
        for (full, _line) in cited_items(thm) {
            if ours.contains(&full)
                && full != name
                && !in_stdlib(&full)
                && !needs.contains(&full)
            {
                needs.push(full);
            }
        }
        out.push(Artifact {
            name,
            recipe: Recipe::Theorem,
            needs,
        });
    }
    for c in &COMPARISONS {
        out.push(Artifact {
            name: c.name.to_string(),
            recipe: Recipe::ByHand(c.text),
            needs: Vec::new(),
        });
    }
    out
}

/// The files the verifier is given: every artifact, the hand-written
/// comparisons among them, since a comparison that did not verify would be
/// no comparison.
pub fn verified(found: &Corpus) -> Vec<String> {
    artifacts(found).iter().map(Artifact::path).collect()
}

/// The artifacts in the order they are made: groups in which none reads
/// another's file, each group after every group it reads.
///
/// A `needs` naming something not being made is not waited for: asking for
/// one theorem remakes that theorem and not the library it reads.
pub fn waves<'a>(wanted: &[&'a Artifact]) -> Vec<Vec<&'a Artifact>> {
    let here: BTreeSet<&str> = wanted.iter().map(|a| a.name.as_str()).collect();
    let mut done: BTreeSet<&str> = BTreeSet::new();
    let mut left: Vec<&Artifact> = wanted.to_vec();
    let mut out = Vec::new();
    while !left.is_empty() {
        let (ready, rest): (Vec<&Artifact>, Vec<&Artifact>) =
            left.into_iter().partition(|a| {
                a.needs
                    .iter()
                    .all(|n| !here.contains(n.as_str()) || done.contains(n.as_str()))
            });
        done.extend(ready.iter().map(|a| a.name.as_str()));
        out.push(ready);
        left = rest;
    }
    out
}

/// What makes artifacts: the corpus read once, set.mm read once, and what
/// this run has made so far.
pub struct Maker<'a> {
    source: &'a dyn Source,
    found: &'a Corpus,
    g: Grammar,
    items: IndexMap<String, Item<'a>>,
    setmm: String,
    library: Option<Library>,
    made: IndexMap<String, String>,
}

impl<'a> Maker<'a> {
    pub fn new(
        source: &'a dyn Source,
        found: &'a Corpus,
        setmm: &Path,
    ) -> Checked<Maker<'a>> {
        let g = Grammar::load(&found.records)?;
        let items = index(&found.records, &found.theorems);
        let setmm = std::fs::read_to_string(setmm).map_err(|e| {
            Problem::new(
                setmm.display().to_string(),
                0,
                format!("cannot read set.mm: {e}"),
            )
        })?;
        Ok(Maker {
            source,
            found,
            g,
            items,
            setmm,
            library: None,
            made: IndexMap::new(),
        })
    }

    /// An artifact's text: what this run made, and otherwise its file.
    fn text_of(&self, name: &str) -> Option<String> {
        match self.made.get(name) {
            Some(text) => Some(text.clone()),
            None => self.source.read_text(&path_of(name)).ok(),
        }
    }

    /// Make one artifact, and keep what it made for the artifacts that read
    /// it.
    pub fn make(&mut self, artifact: &Artifact) -> Checked<String> {
        let text = match artifact.recipe {
            Recipe::Definitions => {
                let sigs = read_texts(&[&self.setmm]);
                write_definitions(&self.found.records, &sigs, self.setmm.as_bytes())?
            }
            Recipe::Proved => {
                // The angle is a constant this corpus introduces, so the
                // definitions are read alongside the library: `angval` says
                // what a value of it is, and discharging that needs `df-ang`.
                let definitions = self.text_of(DEFINITIONS).ok_or_else(|| {
                    Problem::new(
                        path_of(DEFINITIONS),
                        0,
                        "not built, and not in the tree",
                    )
                })?;
                let source = self.source;
                crate::proofs::stdlib::proved(
                    read_texts(&[&self.setmm, &definitions]),
                    &|path| source.read_text(path).ok(),
                )?
            }
            Recipe::Theorem => self.theorem(&artifact.name)?.text,
            Recipe::ByHand(text) => text(),
        };
        self.made.insert(artifact.name.clone(), text.clone());
        Ok(text)
    }

    fn theorem(&mut self, name: &str) -> Checked<Elaborated> {
        if self.library.is_none() {
            let proved = self.text_of(PROVED);
            self.library = Some(Library::from_texts(&self.setmm, proved.as_deref()));
        }
        let Some(thm) = self.found.theorems.iter().find(|t| t.qualified() == name)
        else {
            return Err(Problem::new(name, 0, format!("no theorem {name}")));
        };
        let statements =
            |cited: &str| -> Option<String> { statement_of(&self.text_of(cited)?) };
        let library = self.library.as_ref().expect("read above");
        elaborate(
            self.found,
            &self.g,
            &self.items,
            thm,
            library,
            &statements,
            Options::default(),
        )
    }
}

/// The process's peak memory so far, in bytes.
fn peak() -> u64 {
    use nix::sys::resource::{getrusage, UsageWho};
    let rss = getrusage(UsageWho::RUSAGE_SELF)
        .map_or(0, |usage| u64::try_from(usage.max_rss()).unwrap_or(0));
    // `ru_maxrss` is in bytes on macOS and in kilobytes elsewhere.
    if cfg!(target_os = "macos") {
        rss
    } else {
        rss * 1024
    }
}

fn gb(bytes: u64) -> f64 {
    bytes as f64 / f64::from(1u32 << 30)
}

/// Build the artifact `wanted`, or every artifact, in the tree at `root`,
/// writing each file that changed.
pub fn run(root: &Path, wanted: Option<&str>, setmm: Option<&str>) -> Said {
    let mut said = Said::default();
    let source = Disk::new(root.to_path_buf());
    let found = match corpus(&source) {
        Ok(found) => found,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };
    let every = artifacts(&found);
    let asked = wanted;
    let wanted: Vec<&Artifact> = match asked {
        Some(name) => every.iter().filter(|a| a.name == name).collect(),
        None => every.iter().collect(),
    };
    if wanted.is_empty() {
        let names: Vec<&str> = every.iter().map(|a| a.name.as_str()).collect();
        said.printed = format!(
            "no artifact {}; there are: {}\n",
            crate::text::repr(asked.unwrap_or_default()),
            names.join(", ")
        );
        said.status = 2;
        return said;
    }
    let library = where_set_mm(setmm, root);
    let library = match library {
        Some(path) => path,
        None if wanted.iter().any(|a| a.wants_library()) => {
            said.printed = "set.mm not found; say where it is with SET_MM, or leave a \
                            copy or a link at the root of the working tree\n"
                .to_string();
            said.status = 2;
            return said;
        }
        None => root.join("set.mm"),
    };
    let mut maker = match Maker::new(&source, &found, &library) {
        Ok(maker) => maker,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };

    let mut changed = 0;
    let mut marks: IndexMap<String, char> = IndexMap::new();
    // The process's peak after each artifact. The one after which it first
    // reached its final value is the artifact that set it.
    let mut peaks: Vec<(String, u64)> = Vec::new();
    let mut failed = false;
    for wave in waves(&wanted) {
        for artifact in wave {
            let made = maker.make(artifact);
            peaks.push((artifact.name.clone(), peak()));
            let written = match made {
                Ok(text) => text,
                Err(problem) => {
                    said.complained +=
                        &format!("{}: failed\n{problem}\n", artifact.name);
                    failed = true;
                    continue;
                }
            };
            let path = root.join(artifact.path());
            let before = std::fs::read_to_string(&path).ok();
            if before.as_deref() != Some(written.as_str()) {
                let wrote = path
                    .parent()
                    .map_or(Ok(()), std::fs::create_dir_all)
                    .and_then(|()| std::fs::write(&path, &written));
                if let Err(e) = wrote {
                    said.complained += &format!("{}: {e}\n", path.display());
                    failed = true;
                    continue;
                }
                changed += 1;
                marks.insert(artifact.name.clone(), '*');
            } else {
                marks.insert(artifact.name.clone(), ' ');
            }
        }
        // The next wave reads what this one made, so a failure stops here.
        if failed {
            break;
        }
    }

    for artifact in &wanted {
        if let Some(mark) = marks.get(&artifact.name) {
            said.printed += &format!("{mark} {}\n", artifact.path());
        }
    }
    if marks.len() != wanted.len() {
        said.status = 1;
        return said;
    }

    // What the peak was and which artifact set it, always; and past the
    // limit, the build fails: the files are written, and what they cost is
    // the defect.
    let top = peaks.iter().map(|(_, p)| *p).max().unwrap_or(0);
    if let Some((heaviest, _)) = peaks.iter().find(|(_, p)| *p == top) {
        said.printed += &format!("\nlargest peak: {heaviest}, {:.1}GB\n", gb(top));
    }
    if let Some((first, p)) = peaks.iter().find(|(_, p)| *p > MEMORY_LIMIT) {
        said.complained += &format!(
            "{first} peaked at {:.1}GB, past the limit of {:.0}GB\n",
            gb(*p),
            gb(MEMORY_LIMIT)
        );
        said.status = 1;
        return said;
    }

    said.printed += &format!("\n{} built, {changed} changed\n", wanted.len());
    said
}

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
    let proved = root.join(path_of(PROVED));
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
