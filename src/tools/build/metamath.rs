//! Every file the Metamath build generates, what generates it, and where it
//! goes.
//!
//! What there is to build is read off the tree rather than listed. Every
//! theorem of a `.proof` file is elaborated; the library's definitions and
//! the proofs below the readable layer are written first; and the
//! hand-written comparison proofs are written beside them. A file's path
//! under `corpus/elaboration/` is its name with `.mm`, so the theorem
//! `proofs/wiedijk/bezout/bezout` is written to
//! `corpus/elaboration/proofs/wiedijk/bezout/bezout.mm`, and a file including it says
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
use std::rc::Rc;
use std::sync::{Arc, Mutex, OnceLock};

use indexmap::IndexMap;

use crate::checker::{CheckedCorpus, CheckedTheorem, LibraryReading};
use crate::corpus::{cited_items, index_built, Corpus, Item};
use crate::elab::definitions::write_definitions;
use crate::elab::elaborate::Options;
use crate::elab::{elaborate, statement_of, Elaborated, Library, ReadLibrary};
use crate::formula::Grammar;
use crate::mm::library::where_set_mm;
use crate::mm::read_texts;
use crate::outcome::{Checked, Problem};
use crate::proofs::comparison::COMPARISONS;
use crate::said::Said;
use crate::source::{Disk, Source};

use super::{waves, write_changed, Written};
use crate::tools::path_of;
use crate::tools::verify::Verifier;

/// The library's definitions, which everything reads.
pub const DEFINITIONS: &str = "stdlib/definitions";
/// What the library proves below the readable layer.
pub const PROVED: &str = "stdlib/proved";

/// What one artifact may hold at its peak while it is made, counted on its
/// own thread, before the build fails. A proof is
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

/// One generated file of the Metamath build.
pub type Artifact = super::Artifact<Recipe>;

impl Artifact {
    /// Its path under `corpus/elaboration/`.
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
            if ours.contains(&full) && full != name && !needs.contains(&full) {
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

/// The artifacts of `every` an edit to the files `edited` can change, with
/// every artifact they read, so that each is made from what a whole build
/// makes it from. An edited artifact's own file reaches that artifact, and
/// a library proof worksheet reaches `proved.mm`, the one recipe that reads
/// it; any other file is read by every recipe, through the corpus, and
/// reaches every artifact.
pub fn reached_by<'a>(every: &'a [Artifact], edited: &[String]) -> Vec<&'a Artifact> {
    let mut wanted: BTreeSet<&str> = BTreeSet::new();
    for path in edited {
        if let Some(artifact) = every.iter().find(|a| a.path() == *path) {
            wanted.insert(&artifact.name);
        } else if path.starts_with(crate::proofs::stdlib::WORKSHEETS) {
            wanted.insert(PROVED);
        } else {
            return every.iter().collect();
        }
    }
    loop {
        let needed: Vec<&str> = every
            .iter()
            .filter(|a| wanted.contains(a.name.as_str()))
            .flat_map(|a| a.needs.iter().map(String::as_str))
            .filter(|name| !wanted.contains(name))
            .collect();
        if needed.is_empty() {
            break;
        }
        wanted.extend(needed);
    }
    every
        .iter()
        .filter(|a| wanted.contains(a.name.as_str()))
        .collect()
}

/// The files the verifier is given: every artifact, the hand-written
/// comparisons among them, since a comparison that did not verify would be
/// no comparison.
pub fn verified(found: &Corpus) -> Vec<String> {
    artifacts(found).iter().map(Artifact::path).collect()
}

/// set.mm read once, and what it reads as with each `proved.mm` asked for,
/// kept by that text: a fresh build reads the `proved.mm` it has just made,
/// which a planted defect may change, and what was read is reused only for
/// the text it was read with. What is kept never changes, so the stages of a
/// gate and the workers of a stage share one, each building its own
/// [`Library`] on it. Reading set.mm takes about a second.
pub struct Libraries {
    /// set.mm's text.
    pub setmm: String,
    read: Mutex<IndexMap<Option<String>, Arc<ReadLibrary>>>,
    /// set.mm as the verifier has it, made the first time a run verifies,
    /// for a process that verifies often (`read_verifying_often`); None for
    /// one that verifies afresh each time.
    verifier: Option<OnceLock<Verifier>>,
}

impl Libraries {
    /// set.mm read from `path`.
    pub fn read(path: &Path) -> Checked<Libraries> {
        let setmm = std::fs::read_to_string(path).map_err(|e| {
            Problem::new(
                path.display().to_string(),
                0,
                format!("cannot read set.mm: {e}"),
            )
        })?;
        Ok(Libraries {
            setmm,
            read: Mutex::new(IndexMap::new()),
            verifier: None,
        })
    }

    /// `read`, for a process that verifies many trees against set.mm, which
    /// is then parsed and verified once for all of them
    /// (`verify::Verifier`).
    pub fn read_verifying_often(path: &Path) -> Checked<Libraries> {
        Ok(Libraries {
            verifier: Some(OnceLock::new()),
            ..Libraries::read(path)?
        })
    }

    /// set.mm parsed and verified once, where these libraries were read for
    /// verifying often; None where each run verifies afresh.
    pub fn shared_verifier(&self) -> Option<&Verifier> {
        let kept = self.verifier.as_ref()?;
        Some(kept.get_or_init(|| Verifier::of(&self.setmm)))
    }

    /// What set.mm and `proved` read as, read the first time it is asked
    /// for. The lock is held while reading, so a second stage asking for the
    /// same waits for it rather than reading it again.
    pub fn read_library(&self, proved: Option<&str>) -> Arc<ReadLibrary> {
        let mut read = self.read.lock().expect("no reader panicked");
        let key = proved.map(str::to_string);
        if let Some(found) = read.get(&key) {
            return Arc::clone(found);
        }
        let made = Arc::new(ReadLibrary::from_texts(&self.setmm, proved));
        read.insert(key, Arc::clone(&made));
        made
    }

    /// A library on set.mm and `proved`, with syntaxes of its own.
    pub fn library(&self, proved: Option<&str>) -> Library {
        Library::new(self.read_library(proved))
    }
}

/// What makes artifacts: the corpus as the checker read it, set.mm read
/// once, and what this run has made so far.
pub struct Maker<'a> {
    source: &'a dyn Source,
    found: &'a Corpus,
    g: Rc<Grammar>,
    items: IndexMap<String, Item<'a>>,
    libraries: &'a Libraries,
    library: Option<Library>,
    made: IndexMap<String, String>,
    /// Every theorem as the checker reads it (`checker::checked`), which the
    /// build is handed: one it refuses is not built.
    checked: &'a IndexMap<String, CheckedTheorem>,
    /// Every item a citation may name, as the checker read it.
    library_read: &'a LibraryReading,
}

/// What every `Maker` of a run reads, which threads share: all of the
/// corpus as the checker read it but its grammar, which a thread loads for
/// itself.
pub struct Shared<'a> {
    source: &'a dyn Source,
    found: &'a Corpus,
    checked: &'a IndexMap<String, CheckedTheorem>,
    library_read: &'a LibraryReading,
    libraries: &'a Libraries,
}

impl<'a> Shared<'a> {
    pub fn of(
        source: &'a dyn Source,
        checked: &'a CheckedCorpus,
        libraries: &'a Libraries,
    ) -> Shared<'a> {
        Shared {
            source,
            found: &checked.corpus,
            checked: &checked.theorems,
            library_read: &checked.library,
            libraries,
        }
    }
}

impl<'a> Maker<'a> {
    pub fn new(
        source: &'a dyn Source,
        checked: &'a CheckedCorpus,
        libraries: &'a Libraries,
    ) -> Maker<'a> {
        let shared = Shared::of(source, checked, libraries);
        Maker::of(&shared, Rc::clone(&checked.grammar), IndexMap::new())
    }

    /// A maker for a thread of its own, the grammar loaded for it, which
    /// knows what this run has made so far (`made`).
    pub fn on_thread(
        shared: &Shared<'a>,
        made: IndexMap<String, String>,
    ) -> Checked<Maker<'a>> {
        let g = Grammar::load(&shared.found.records)?;
        Ok(Maker::of(shared, g, made))
    }

    fn of(
        shared: &Shared<'a>,
        g: Rc<Grammar>,
        made: IndexMap<String, String>,
    ) -> Maker<'a> {
        let found = shared.found;
        Maker {
            source: shared.source,
            found,
            g,
            items: index_built(
                &found.records,
                &found.theorems,
                crate::corpus::Record::metamath_provided,
            ),
            libraries: shared.libraries,
            library: None,
            made,
            checked: shared.checked,
            library_read: shared.library_read,
        }
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
                let setmm = &self.libraries.setmm;
                let sigs = read_texts(&[setmm]);
                write_definitions(&self.found.records, &sigs, setmm.as_bytes())?
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
                    read_texts(&[&self.libraries.setmm, &definitions]),
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
            self.library = Some(self.libraries.library(proved.as_deref()));
        }
        let Some(thm) = self.found.theorems.iter().find(|t| t.qualified() == name)
        else {
            return Err(Problem::new(name, 0, format!("no theorem {name}")));
        };
        let Some(checked) = self.checked.get(name) else {
            return Err(Problem::new(
                name,
                0,
                format!("the checker has not read {name}"),
            ));
        };
        let statements =
            |cited: &str| -> Option<String> { statement_of(&self.text_of(cited)?) };
        // A theorem of another proof is cited by the statement its built file
        // holds, so one not built stops this one before the build starts:
        // nothing about this page or the build is wrong.
        for (full, line) in cited_items(thm) {
            let proof = self.found.theorems.iter().any(|t| t.qualified() == full);
            if proof && full != name && statements(&full).is_none() {
                return Err(Problem::new(
                    &thm.path,
                    line,
                    format!(
                        "{full}, which this step cites, has no built file under corpus/elaboration/: build it first, or build everything with `parley build metamath`"
                    ),
                ));
            }
        }
        let library = self.library.as_ref().expect("read above");
        elaborate(
            self.found,
            &self.g,
            &self.items,
            thm,
            checked,
            library,
            self.library_read,
            &statements,
            Options::default(),
        )
    }
}

/// What making one artifact came to (`made_in_waves`).
pub enum MadeAs {
    /// Its text, and the most it held at once while it was made, in bytes.
    Made { text: String, held: u64 },
    /// It could not be made.
    Failed(Problem),
    /// It reads `on`, which was not made, so it was not made either.
    After { on: String },
}

/// Every artifact of `wanted` made in the order `waves` gives: a wave's
/// artifacts, none of which reads another, side by side, each thread with a
/// maker of its own. An artifact that fails is not made, and nor is one that
/// reads it; every other is. `kept` is given each artifact as it comes to
/// something, in order, and says whether what was made is kept: one not
/// kept, as a file the build could not write, counts as not made for those
/// that read it. The order is the outcome where there is none.
pub fn made_in_waves<'w>(
    shared: &Shared<'_>,
    wanted: &[&'w Artifact],
    mut kept: impl FnMut(&'w Artifact, &MadeAs) -> bool,
) -> Checked<()> {
    // What this run has made, which a later wave's artifacts read.
    let mut made_so_far: IndexMap<String, String> = IndexMap::new();
    let mut not_made: BTreeSet<String> = BTreeSet::new();
    for wave in waves(wanted)? {
        let mut ready: Vec<&Artifact> = Vec::new();
        for artifact in wave {
            match artifact.needs.iter().find(|n| not_made.contains(*n)) {
                Some(on) => {
                    kept(artifact, &MadeAs::After { on: on.clone() });
                    not_made.insert(artifact.name.clone());
                }
                None => ready.push(artifact),
            }
        }
        let results = crate::threads::in_order(
            &ready,
            || Maker::on_thread(shared, made_so_far.clone()),
            made_measured,
        );
        for (artifact, (made, held)) in ready.into_iter().zip(results) {
            let made = match made {
                Ok(text) => MadeAs::Made { text, held },
                Err(problem) => MadeAs::Failed(problem),
            };
            let keep = kept(artifact, &made);
            match (made, keep) {
                (MadeAs::Made { text, .. }, true) => {
                    made_so_far.insert(artifact.name.clone(), text);
                }
                _ => {
                    not_made.insert(artifact.name.clone());
                }
            }
        }
    }
    Ok(())
}

/// An artifact made by this thread's maker, with the most it held at once
/// while it was made, in bytes, counted on this thread alone, so that other
/// artifacts made beside it do not count (`allocation_counter::measure`).
fn made_measured(
    maker: &mut Checked<Maker<'_>>,
    artifact: &&Artifact,
) -> (Checked<String>, u64) {
    let maker = match maker {
        Ok(maker) => maker,
        Err(problem) => return (Err(problem.clone()), 0),
    };
    let mut made = None;
    let held = allocation_counter::measure(|| made = Some(maker.make(artifact)));
    let made = made.expect("measure runs what it is given");
    (made, held.bytes_max)
}

fn gb(bytes: u64) -> f64 {
    bytes as f64 / f64::from(1u32 << 30)
}

/// Build the artifact `wanted`, or every artifact, in the tree at `root`,
/// writing each file that changed. set.mm is where the environment or the
/// root of the tree says (`where_set_mm`).
pub fn run(root: &Path, wanted: Option<&str>) -> Said {
    let source = Disk::new(root.to_path_buf());
    // The checker reads the page first, and the build builds only what it
    // accepts, from what it read.
    let (mut said, checked) = match super::checked_first(&source) {
        Ok(first) => first,
        Err(out) => return out,
    };
    let every = artifacts(&checked.corpus);
    let asked = wanted;
    let wanted: Vec<&Artifact> = match asked {
        Some(name) => every.iter().filter(|a| a.name == name).collect(),
        None => every.iter().collect(),
    };
    if wanted.is_empty() {
        let names: Vec<&str> = every.iter().map(|a| a.name.as_str()).collect();
        said.printed += &format!(
            "no artifact {}; there are: {}\n",
            crate::text::repr(asked.unwrap_or_default()),
            names.join(", ")
        );
        said.status = 2;
        return said;
    }
    let library = where_set_mm(None, root);
    let library = match library {
        Some(path) => path,
        None if wanted.iter().any(|a| a.wants_library()) => {
            said.printed +=
                "set.mm not found; say where it is with SET_MM, or leave a \
                             copy or a link at the root of the working tree\n";
            said.status = 2;
            return said;
        }
        None => root.join("set.mm"),
    };
    let libraries = match Libraries::read(&library) {
        Ok(libraries) => libraries,
        Err(problem) => {
            said.complained = format!("{problem}\n");
            said.status = 2;
            return said;
        }
    };
    let shared = Shared::of(&source, &checked, &libraries);

    let mut changed = 0;
    let mut marks: IndexMap<String, char> = IndexMap::new();
    // The most each artifact held at once while it was made, on its own
    // thread (`allocation_counter::measure`).
    let mut peaks: Vec<(String, u64)> = Vec::new();
    // Each artifact made is written; the old file of one not made is
    // removed, so that what is on disk is what this run made.
    let ordered = made_in_waves(&shared, &wanted, |artifact, made| match made {
        MadeAs::After { on } => {
            said.complained +=
                &format!("{}: not built, as {on} was not\n", artifact.name);
            remove_old(root, artifact, &mut said);
            false
        }
        MadeAs::Failed(problem) => {
            said.complained += &format!("{}: failed\n{problem}\n", artifact.name);
            remove_old(root, artifact, &mut said);
            false
        }
        MadeAs::Made { text, held } => {
            peaks.push((artifact.name.clone(), *held));
            match write_changed(root, &artifact.path(), text) {
                Ok(Written::Changed) => {
                    changed += 1;
                    marks.insert(artifact.name.clone(), '*');
                    true
                }
                Ok(Written::Same) => {
                    marks.insert(artifact.name.clone(), ' ');
                    true
                }
                Err(problem) => {
                    said.complained += &format!("{problem}\n");
                    false
                }
            }
        }
    });
    if let Err(problem) = ordered {
        said.complained = format!("{problem}\n");
        said.status = 2;
        return said;
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

/// The file of an artifact not built this run removed, where an earlier run
/// left one, so that no file on disk passes for one this run made.
fn remove_old(root: &Path, artifact: &Artifact, said: &mut Said) {
    let path = root.join(artifact.path());
    if !path.exists() {
        return;
    }
    if let Err(e) = std::fs::remove_file(&path) {
        said.complained += &format!("{}: {e}\n", artifact.path());
    }
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

/// The corpus a tree holds as the checker read it, with its grammar and the
/// checker's records, for elaborating as many of its theorems as are
/// wanted. The index, which borrows from the corpus, is a map of names and
/// cheap to make for each theorem.
pub struct Loaded<'s> {
    source: &'s dyn Source,
    checked: CheckedCorpus,
}

impl<'s> Loaded<'s> {
    /// The corpus `source` holds, read and checked.
    pub fn new(source: &'s dyn Source) -> Checked<Loaded<'s>> {
        Ok(Loaded::with_checked(source, checked_in(source, |_| true)?))
    }

    /// The corpus `source` holds as `checked` read it (`checked_in`), with
    /// the records of the theorems to be elaborated: what it leaves out
    /// cannot be elaborated. A caller elaborating a few theorems of many
    /// trees, or one tree again as files are built into it, checks those
    /// theorems once, since the checker reads proofs and records and no
    /// built file.
    pub fn with_checked(source: &'s dyn Source, checked: CheckedCorpus) -> Loaded<'s> {
        Loaded { source, checked }
    }

    /// Elaborate the theorem `name`.
    ///
    /// A theorem it cites is read from the file already written for it in
    /// the same tree, for the order of what a citation pushes.
    pub fn elaborate(
        &self,
        name: &str,
        library: &Library,
        options: Options,
    ) -> Checked<Elaborated> {
        let found = &self.checked.corpus;
        let Some(thm) = found.theorems.iter().find(|t| t.qualified() == name) else {
            return Err(Problem::new(name, 0, format!("no theorem {name}")));
        };
        let statements = |cited: &str| -> Option<String> {
            let text = self.source.read_text(&path_of(cited)).ok()?;
            statement_of(&text)
        };
        let items = index_built(
            &found.records,
            &found.theorems,
            crate::corpus::Record::metamath_provided,
        );
        let Some(checked) = self.checked.theorems.get(name) else {
            return Err(Problem::new(
                name,
                0,
                format!("the checker has not read {name}"),
            ));
        };
        elaborate(
            found,
            &self.checked.grammar,
            &items,
            thm,
            checked,
            library,
            &self.checked.library,
            &statements,
            options,
        )
    }
}

/// The corpus of `source` as the checker reads it, with its records of the
/// theorems whose full name `wanted` holds (`checker::checked_where`), a
/// corpus that does not read being a problem.
pub fn checked_in(
    source: &dyn Source,
    wanted: impl Fn(&str) -> bool + Sync,
) -> Checked<CheckedCorpus> {
    crate::checker::checked_where(source, wanted).map_err(|out| {
        Problem::new(
            source.root().display().to_string(),
            0,
            str::trim(&format!("{}{}", out.printed, out.complained)).to_string(),
        )
    })
}

/// Elaborate the theorem `name` of the corpus `source` holds, reading the
/// corpus for it alone and checking it alone.
pub fn elaborate_one(
    source: &dyn Source,
    name: &str,
    library: &Library,
    options: Options,
) -> Checked<Elaborated> {
    let checked = checked_in(source, |n| n == name)?;
    Loaded::with_checked(source, checked).elaborate(name, library, options)
}

#[cfg(test)]
mod tests {
    use super::{waves, Artifact, Recipe};

    fn theorem(name: &str, needs: &[&str]) -> Artifact {
        Artifact {
            name: name.to_string(),
            recipe: Recipe::Theorem,
            needs: needs.iter().map(|n| n.to_string()).collect(),
        }
    }

    #[test]
    fn artifacts_waiting_on_one_another_are_a_fault_not_a_hang() {
        let a = theorem("proofs/x/a", &["proofs/x/b"]);
        let b = theorem("proofs/x/b", &["proofs/x/a"]);
        let c = theorem("proofs/x/c", &[]);
        let Err(problem) = waves(&[&a, &b, &c]) else {
            panic!("a cycle of needs was put in waves");
        };
        assert!(problem.internal);
        assert!(
            problem.to_string().contains("proofs/x/a, proofs/x/b"),
            "{problem}"
        );
    }

    #[test]
    fn an_artifact_comes_after_what_it_needs() {
        let a = theorem("proofs/x/a", &["proofs/x/b"]);
        let b = theorem("proofs/x/b", &[]);
        let names: Vec<Vec<&str>> = waves(&[&a, &b])
            .unwrap()
            .iter()
            .map(|w| w.iter().map(|x| x.name.as_str()).collect())
            .collect();
        assert_eq!(names, vec![vec!["proofs/x/b"], vec!["proofs/x/a"]]);
    }
}
