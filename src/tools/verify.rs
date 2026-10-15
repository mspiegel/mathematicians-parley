//! Every elaborated proof, checked by a verifier rather than by this project.
//!
//! The checker reads the readable layer and the elaborator writes Metamath
//! from it. Neither is evidence that what came out is a proof: an elaborator
//! that emits a wrong step emits it confidently, and the assumption count at
//! the head of each file reports a proof that assumes nothing whether or not
//! it proves what it claims. Only a verifier settles that, and it is the one
//! part of this tool that was not written for this project: `metamath-rs`,
//! the verifier of metamath-knife, which the Metamath project maintains and
//! runs over set.mm itself.
//!
//! Which files there are comes from the build, which is what knows every
//! generated file, the hand-written comparisons among them; a file left in
//! the directory that the build does not make is not one of them. The files
//! are handed to the verifier as one, after set.mm, each once and after what
//! it includes (`joined`), and a problem is reported at the file and line it
//! is in. That each file reaches what it uses through its own inclusions is
//! checked here, before the verifier runs (`unreached`).
//!
//! Which of them to include is read off the inclusions rather than listed: a
//! proof that nothing else includes is a root, and from the roots every file
//! is reached. A new proof is covered the day it is written, where a list of
//! roots would leave the gate green and the new proof unread.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::LazyLock;
use std::time::Instant;

use annotate_snippets::Renderer;
use metamath_rs::database::DbOptions;
use metamath_rs::Database;
use regex::Regex;

use crate::said::Said;
use crate::source::Source;
use crate::tools::build::Libraries;

static INCLUDE: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"\$\[\s*(\S+)\s*\$\]").expect("a valid pattern"));
/// A labelled `$p`, which is what there is one of per theorem proved.
static PROVES: LazyLock<Regex> =
    LazyLock::new(|| Regex::new(r"(?m)^\s*(\S+)\s+\$p\s").expect("a valid pattern"));

/// A labelled statement, by its label.
static DECLARES: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?m)^\s*(\S+)\s+\$[apef]\s").expect("a valid pattern")
});
/// A proof, by the label it proves and what stands between `$=` and `$.`.
static PROOF: LazyLock<Regex> = LazyLock::new(|| {
    Regex::new(r"(?ms)^\s*(\S+)\s+\$p\s.*?\$=(.*?)\$\.").expect("a valid pattern")
});

/// The file the verifier starts from, which includes every root.
const JOINED: &str = "everything.mm";

/// How a file including this one names it: its path under
/// `corpus/elaboration/`.
fn included_as(path: &str) -> &str {
    path.strip_prefix(super::ELABORATION)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(path)
}

/// The files nothing else includes, which reach everything between them.
///
/// Read off the inclusions so that a proof added later is covered without
/// this being edited. set.mm is included too and is not one of these files,
/// so it falls out of the difference on its own.
fn roots(built: &[(String, String)]) -> Vec<String> {
    let here: BTreeSet<&str> = built.iter().map(|(p, _)| included_as(p)).collect();
    let mut included: BTreeSet<&str> = BTreeSet::new();
    for (_, text) in built {
        for c in INCLUDE.captures_iter(text) {
            let name = c.get(1).map_or("", |m| m.as_str());
            if here.contains(name) {
                included.insert(name);
            }
        }
    }
    here.difference(&included).map(|s| s.to_string()).collect()
}

/// The labels a text declares: each `$a`, `$p`, `$e` and `$f`.
fn declared(text: &str) -> BTreeSet<&str> {
    DECLARES
        .captures_iter(text)
        .filter_map(|c| c.get(1).map(|m| m.as_str()))
        .collect()
}

/// The labels each proof of a text uses, by the label it proves: a
/// compressed proof's list, or an uncompressed proof's steps.
fn used(text: &str) -> Vec<(&str, Vec<&str>)> {
    PROOF
        .captures_iter(text)
        .map(|c| {
            let label = c.get(1).map_or("", |m| m.as_str());
            let body = c.get(2).map_or("", |m| m.as_str()).trim_start();
            let labels = match body.strip_prefix('(') {
                Some(rest) => rest.split(')').next().unwrap_or("").split_whitespace(),
                None => body.split_whitespace(),
            };
            (label, labels.filter(|l| *l != "?").collect())
        })
        .collect()
}

/// Each proof using a label that neither set.mm nor any file its own file
/// reaches through its inclusions declares.
fn unreached(texts: &[(String, String)], base: &BTreeSet<String>) -> Vec<String> {
    let by_name: BTreeMap<&str, &str> = texts
        .iter()
        .map(|(p, t)| (included_as(p), t.as_str()))
        .collect();
    let mut out = Vec::new();
    for (path, text) in texts {
        let mut reached: BTreeSet<&str> = BTreeSet::new();
        let mut todo: Vec<&str> = vec![text];
        let mut seen: BTreeSet<&str> = BTreeSet::new();
        while let Some(here) = todo.pop() {
            reached.extend(declared(here));
            for c in INCLUDE.captures_iter(here) {
                let name = c.get(1).map_or("", |m| m.as_str());
                if let Some(next) = by_name.get(name) {
                    if seen.insert(name) {
                        todo.push(next);
                    }
                }
            }
        }
        for (proves, labels) in used(text) {
            let missing: Vec<&str> = labels
                .into_iter()
                .filter(|l| !base.contains(*l) && !reached.contains(l))
                .collect();
            if !missing.is_empty() {
                out.push(format!(
                    "{path}: the proof of {proves} uses {}, which nothing the file includes declares",
                    missing.join(", ")
                ));
            }
        }
    }
    out
}

/// Verify the files at `built`, paths in `source`, against set.mm as
/// `libraries` read it.
pub fn run(
    source: &dyn Source,
    built: &[String],
    libraries: Option<&Libraries>,
) -> Said {
    let mut said = Said::default();
    let Some(libraries) = libraries else {
        said.printed =
            "set.mm not found; say where it is with SET_MM, or leave a copy or \
                        a link at the root of the working tree\n"
                .into();
        said.status = 2;
        return said;
    };
    let missing: Vec<&String> = built.iter().filter(|p| !source.exists(p)).collect();
    if !missing.is_empty() {
        for path in missing {
            said.printed += &format!("not built: {path}\n");
        }
        said.printed += "\nrun parley build\n";
        said.status = 2;
        return said;
    }
    let mut texts = Vec::new();
    for path in built {
        match source.read_text(path) {
            Ok(text) => texts.push((path.clone(), text)),
            Err(e) => {
                said.printed += &format!("{path}: {e}\n");
                said.status = 2;
                return said;
            }
        }
    }
    let shared = libraries.shared_verifier();
    let afresh: BTreeSet<String>;
    let labels = match shared {
        Some(verifier) => &verifier.labels,
        None => {
            afresh = labels_of(&libraries.setmm);
            &afresh
        }
    };

    // Verified together, every file sees every other's labels; each must
    // reach the ones it uses through its own inclusions, as a reader
    // verifying that one file does.
    let unreached = unreached(&texts, labels);
    if !unreached.is_empty() {
        for u in &unreached {
            said.printed += &format!("{u}\n");
        }
        said.printed += &format!(
            "\n{} proof(s) use a label nothing their file includes declares\n",
            unreached.len()
        );
        said.status = 1;
        return said;
    }

    let top = roots(&texts);
    let proved: usize = texts.iter().map(|(_, t)| PROVES.find_iter(t).count()).sum();
    said.printed += &format!(
        "{proved} proofs in {} files, reached from {}\n",
        built.len(),
        top.join(", ")
    );

    let Joined { text, starts } = joined(&texts, &top);

    let began = Instant::now();
    let found = match shared {
        Some(verifier) => verifier.verified(&libraries.setmm, &text),
        None => verified_afresh(&libraries.setmm, &text),
    };
    let problems: Vec<String> = found.iter().map(|p| placed(p, &starts)).collect();
    let spent = began.elapsed().as_secs_f64();
    if !problems.is_empty() {
        for p in &problems {
            said.printed += &format!("\n{p}\n");
        }
        said.printed += &format!(
            "\nmetamath-rs rejected the proofs: {} problem(s)\n",
            problems.len()
        );
        said.status = 1;
        return said;
    }
    said.printed += &format!("\nall {proved} verify, in {spent:.0}s\n");
    said
}

/// The built files as one, and where each starts in it.
struct Joined {
    /// set.mm included, then every file once, after what it includes, its
    /// own inclusions blanked and their lines kept.
    text: String,
    /// Each file by the line of the joined text its first line is, in the
    /// order they stand.
    starts: Vec<(usize, String)>,
}

/// The files reached from `roots`, joined in the order their inclusions
/// put them.
///
/// metamath-rs scope-checks one segment at a time, an included file being
/// one, and copies its whole table of names for each (`scope_check` in its
/// `scopeck.rs`): set.mm's table copied once for every file of the corpus
/// cost 4.6s where set.mm alone is 0.8s. Joined, the files are one segment
/// and the table is copied once. What a file may use is still only what its
/// own inclusions reach, which `unreached` holds before the verifier runs.
fn joined(texts: &[(String, String)], roots: &[String]) -> Joined {
    let by_name: BTreeMap<&str, &str> = texts
        .iter()
        .map(|(p, t)| (included_as(p), t.as_str()))
        .collect();
    fn visit<'t>(
        name: &'t str,
        by_name: &BTreeMap<&'t str, &'t str>,
        seen: &mut BTreeSet<&'t str>,
        order: &mut Vec<&'t str>,
    ) {
        let Some(text) = by_name.get(name) else {
            return;
        };
        if !seen.insert(name) {
            return;
        }
        for c in INCLUDE.captures_iter(text) {
            if let Some(m) = c.get(1) {
                visit(m.as_str(), by_name, seen, order);
            }
        }
        order.push(name);
    }
    let mut order = Vec::new();
    let mut seen = BTreeSet::new();
    for root in roots {
        visit(root, &by_name, &mut seen, &mut order);
    }
    let mut text = String::from("$[ set.mm $]\n");
    let mut line = 2;
    let mut starts = Vec::new();
    for name in order {
        starts.push((line, name.to_string()));
        let body = INCLUDE.replace_all(by_name[name], "");
        line += body.lines().count();
        text += &body;
        if !body.ends_with('\n') {
            text.push('\n');
        }
    }
    Joined { text, starts }
}

/// A problem the verifier reports at a line of the joined file, said at
/// the file and line it is in: the place it names, and the line numbers in
/// the margin of the text it quotes.
fn placed(problem: &str, starts: &[(usize, String)]) -> String {
    static AT: LazyLock<Regex> = LazyLock::new(|| {
        Regex::new(&format!(r"{}:(\d+)", regex::escape(JOINED)))
            .expect("a valid pattern")
    });
    static MARGIN: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(r"(?m)^(\s*)(\d+)( \|)").expect("a valid pattern"));
    let file_of = |at: usize| starts.iter().rev().find(|(start, _)| *start <= at);
    let Some(at) = AT
        .captures(problem)
        .and_then(|c| c[1].parse::<usize>().ok())
    else {
        return problem.to_string();
    };
    let Some((start, _)) = file_of(at) else {
        return problem.to_string();
    };
    let named = AT.replace_all(problem, |c: &regex::Captures| {
        let at: usize = c[1].parse().unwrap_or(0);
        match file_of(at) {
            Some((start, name)) => format!("{name}:{}", at - start + 1),
            None => c[0].to_string(),
        }
    });
    MARGIN
        .replace_all(&named, |c: &regex::Captures| {
            let n: usize = c[2].parse().unwrap_or(0);
            let shown = n.checked_sub(start - 1).unwrap_or(n).to_string();
            format!("{}{:>width$}{}", &c[1], shown, &c[3], width = c[2].len())
        })
        .into_owned()
}

/// set.mm as the verifier has it, read and verified once, for a process
/// that verifies many trees against the same set.mm (`Libraries::
/// read_verifying_often`): the invariance test verifies one a rewrite,
/// about twenty, and spent a quarter of its time verifying set.mm again.
/// It costs memory that one or two runs do not win back: metamath-rs
/// records what each segment uses, and copies its tables of every label
/// when a run's file changes them, so `parley gate`, verifying twice at
/// once, held about 450 MB more and took no less time; a process that
/// verifies once or twice verifies afresh (`verified_afresh`).
pub struct Verifier {
    /// set.mm parsed and verified, with a joined file that includes it and
    /// nothing else. metamath-rs keeps what it worked out of each segment,
    /// so a run parsing its own joined file over a copy recomputes that
    /// file's segment and what reads it, and set.mm's chapters, unchanged,
    /// keep what they were found to be.
    base: Database,
    /// Every label set.mm declares (`unreached`).
    labels: BTreeSet<String>,
}

impl Verifier {
    pub fn of(setmm: &str) -> Verifier {
        // metamath-rs works segment by segment, and set.mm read whole is one
        // segment on one thread: split at its chapters, it is checked on
        // every core at once.
        let options = DbOptions {
            autosplit: true,
            incremental: true,
            jobs: std::thread::available_parallelism().map_or(1, |n| n.get()),
            ..DbOptions::default()
        };
        let mut base = Database::new(options);
        base.parse(JOINED.to_string(), files(setmm, "$[ set.mm $]\n"));
        base.verify_pass();
        Verifier {
            base,
            labels: labels_of(setmm),
        }
    }
}

/// Every label set.mm declares.
fn labels_of(setmm: &str) -> BTreeSet<String> {
    declared(setmm).into_iter().map(str::to_string).collect()
}

/// What the verifier reads: set.mm, and the joined file that includes it.
fn files(setmm: &str, joined: &str) -> Vec<(String, Vec<u8>)> {
    vec![
        ("set.mm".to_string(), setmm.as_bytes().to_vec()),
        (JOINED.to_string(), joined.as_bytes().to_vec()),
    ]
}

impl Verifier {
    /// Every problem the verifier finds in `joined`, a file that includes
    /// set.mm, `setmm` being the text this verifier was made of, each
    /// written out with the statement it is in.
    pub fn verified(&self, setmm: &str, joined: &str) -> Vec<String> {
        let mut db = self.base.clone();
        db.parse(JOINED.to_string(), files(setmm, joined));
        db.verify_pass();
        problems_of(&mut db)
    }
}

/// Every problem the verifier finds in `joined` over `setmm`, read and
/// verified for this run alone.
fn verified_afresh(setmm: &str, joined: &str) -> Vec<String> {
    // metamath-rs works segment by segment, and set.mm read whole is one
    // segment on one thread: split at its chapters, it is checked on every
    // core at once.
    let options = DbOptions {
        autosplit: true,
        jobs: std::thread::available_parallelism().map_or(1, |n| n.get()),
        ..DbOptions::default()
    };
    let mut db = Database::new(options);
    db.parse(JOINED.to_string(), files(setmm, joined));
    db.verify_pass();
    problems_of(&mut db)
}

/// What the verifier found, each problem written out plain.
fn problems_of(db: &mut Database) -> Vec<String> {
    let diags = db.diag_notations();
    // Plain, without colour: the gate's report is read as text.
    db.render_diags(diags, |message| {
        Renderer::plain().render(message).to_string()
    })
}
