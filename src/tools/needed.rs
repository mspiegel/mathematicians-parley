//! Every requires line is needed.
//!
//! A requires line does work when its step cannot be checked or built
//! without it. The checker and the elaborator each see part of what a line
//! is for: a hypothesis of an item that the kernel lemma does not use is the
//! checker's to ask for, and a membership the kernel builds from is the
//! elaborator's. Taken away, a line one of them needs makes that one
//! complain. A line neither needs is surplus, whatever route a proof took
//! through it while it was there: `requires 2 ∈ ℤ: arithmetic` on a step
//! that `exhibit`s 2 is used when it is written and worked out when it is
//! not (`ELABORATION.md`, R3).
//!
//! So each requires line of each proof is taken away in turn, and the
//! theorem it sits in is checked and elaborated without it. The lines are
//! shared out among workers that run side by side; each reads the corpus
//! once and loads set.mm once for every line it takes.

use std::path::Path;

use crate::check::{check_cuts, Cut};
use crate::corpus::proof_files;
use crate::elab::elaborate::Options;
use crate::regex;
use crate::said::Said;
use crate::source::{Memory, Overlay, Source};
use crate::tools::build::{elaborate_one, library};

regex!(STEP_HEAD, r"^\s*(\d+(?:\.\d+)*)\.\s");

/// One requires line taken away: where it was, the file lines it spans,
/// what it said, the step it sat in, and the file without it.
struct Taken {
    line: usize,
    span: (usize, usize),
    said: String,
    step: String,
    cut: Cut,
}

/// Every requires line of every proof, each as the file without it.
fn every_line(source: &dyn Source) -> Result<Vec<Taken>, String> {
    let mut out = Vec::new();
    for path in proof_files(source) {
        let text = source
            .read_text(&path)
            .map_err(|e| format!("{path}: {e}"))?;
        let lines: Vec<&str> = text.split('\n').collect();
        let mut theorem: Option<String> = None;
        let mut step = String::new();
        for (i, line) in lines.iter().enumerate() {
            if let Some(name) = line.strip_prefix("theorem ") {
                theorem = Some(str::trim(name).to_string());
                continue;
            }
            if let Some(m) = STEP_HEAD.captures(line) {
                step = m[1].to_string();
            }
            let Some(said) = line.trim_start().strip_prefix("requires ") else {
                continue;
            };
            let Some(theorem) = &theorem else { continue };
            // A requires line may go on in a deeper line that starts `from`.
            let indent = line.len() - line.trim_start().len();
            let mut end = i + 1;
            while end < lines.len()
                && lines[end].trim_start().starts_with("from ")
                && lines[end].len() - lines[end].trim_start().len() > indent
            {
                end += 1;
            }
            let mut without: Vec<&str> = lines[..i].to_vec();
            without.extend(&lines[end..]);
            out.push(Taken {
                line: i + 1,
                span: (i, end),
                said: str::trim(said).to_string(),
                step: step.clone(),
                cut: Cut {
                    path: path.clone(),
                    text: without.join("\n"),
                    theorem: theorem.clone(),
                },
            });
        }
    }
    Ok(out)
}

/// Whether each line in `share` is needed: the checker or the elaborator
/// complains of its theorem without it.
fn needed(tree: &Memory, setmm: &str, share: &[&Taken]) -> Result<Vec<bool>, String> {
    let lib = library(tree.root(), Some(setmm)).map_err(|p| p.to_string())?;
    let cuts: Vec<Cut> = share
        .iter()
        .map(|t| Cut {
            path: t.cut.path.clone(),
            text: t.cut.text.clone(),
            theorem: t.cut.theorem.clone(),
        })
        .collect();
    let checked = check_cuts(tree, &cuts).map_err(|out| out.complained)?;
    let mut out = Vec::new();
    for (taken, problems) in share.iter().zip(checked) {
        if !problems.is_empty() {
            out.push(true);
            continue;
        }
        let mut edited = Overlay::new(tree);
        edited.write(&taken.cut.path, taken.cut.text.clone().into_bytes());
        let name = format!(
            "{}/{}",
            taken.cut.path.trim_end_matches(".proof"),
            taken.cut.theorem
        );
        let options = Options::default();
        out.push(elaborate_one(&edited, &name, &lib, options).is_err());
    }
    Ok(out)
}

/// The surplus lines of one theorem that can all go at once.
///
/// Two lines that stand in for each other are each surplus taken away
/// alone, and not both: `requires A ∈ ℝ: membership, from D1` and `requires
/// Σ(k = 1 to n) a(k)² ∈ ℝ: membership` say one number is real. So where a
/// theorem has several, each is asked again in order, without the ones
/// already kept as surplus, and reported only if it can go with them. One
/// round asks the next line of every such theorem at once.
fn together<'t>(
    tree: &Memory,
    setmm: &str,
    surplus: Vec<&'t Taken>,
) -> Result<Vec<&'t Taken>, String> {
    let mut groups: Vec<Vec<&'t Taken>> = Vec::new();
    for t in surplus {
        match groups.last_mut() {
            Some(g)
                if g[0].cut.path == t.cut.path && g[0].cut.theorem == t.cut.theorem =>
            {
                g.push(t)
            }
            _ => groups.push(vec![t]),
        }
    }
    let mut kept: Vec<Vec<&'t Taken>> = groups.iter().map(|g| vec![g[0]]).collect();
    let rounds = groups.iter().map(Vec::len).max().unwrap_or(0);
    for round in 1..rounds {
        let mut asked: Vec<(usize, Taken)> = Vec::new();
        for (i, group) in groups.iter().enumerate() {
            let Some(next) = group.get(round) else {
                continue;
            };
            let text = tree.read_text(&next.cut.path).map_err(|e| e.to_string())?;
            let lines: Vec<&str> = text.split('\n').collect();
            let gone: Vec<(usize, usize)> =
                kept[i].iter().map(|t| t.span).chain([next.span]).collect();
            let without: Vec<&str> = lines
                .iter()
                .enumerate()
                .filter(|(n, _)| !gone.iter().any(|(a, b)| a <= n && n < b))
                .map(|(_, l)| *l)
                .collect();
            asked.push((
                i,
                Taken {
                    line: next.line,
                    span: next.span,
                    said: next.said.clone(),
                    step: next.step.clone(),
                    cut: Cut {
                        path: next.cut.path.clone(),
                        text: without.join("\n"),
                        theorem: next.cut.theorem.clone(),
                    },
                },
            ));
        }
        let share: Vec<&Taken> = asked.iter().map(|(_, t)| t).collect();
        let needs = needed(tree, setmm, &share)?;
        for ((i, _), need) in asked.iter().zip(needs) {
            if !need {
                kept[*i].push(groups[*i][round]);
            }
        }
    }
    Ok(kept.into_iter().flatten().collect())
}

pub fn run(source: &dyn Source, setmm: Option<&Path>) -> Said {
    let mut said = Said::default();
    let Some(setmm) = setmm.and_then(|p| p.to_str()) else {
        said.printed =
            "set.mm not found; say where it is with SET_MM, or leave a copy or a \
                        link at the root of the working tree\n"
                .to_string();
        said.status = 2;
        return said;
    };
    let tree = match Memory::copy(source, &["corpus", "proofs", "tests"]) {
        Ok(tree) => tree,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    let taken = match every_line(&tree) {
        Ok(taken) => taken,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    // Each worker holds a library and a corpus of its own.
    let workers = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .clamp(1, 8);
    let shares: Vec<Vec<&Taken>> = (0..workers)
        .map(|w| taken.iter().skip(w).step_by(workers).collect())
        .collect();
    let results: Vec<Result<Vec<bool>, String>> = std::thread::scope(|scope| {
        let running: Vec<_> = shares
            .iter()
            .map(|share| {
                let tree = &tree;
                scope.spawn(move || needed(tree, setmm, share))
            })
            .collect();
        running
            .into_iter()
            .map(|h| h.join().expect("a worker panicked"))
            .collect()
    });
    let mut surplus: Vec<&Taken> = Vec::new();
    for (share, result) in shares.iter().zip(results) {
        match result {
            Ok(needs) => {
                surplus.extend(
                    share.iter().zip(needs).filter(|(_, n)| !n).map(|(t, _)| *t),
                );
            }
            Err(e) => {
                said.complained = format!("{e}\n");
                said.status = 2;
                return said;
            }
        }
    }
    surplus.sort_by(|a, b| a.cut.path.cmp(&b.cut.path).then(a.line.cmp(&b.line)));
    let surplus = match together(&tree, setmm, surplus) {
        Ok(surplus) => surplus,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    for t in &surplus {
        said.printed.push_str(&format!(
            "{}:{}  the requires line of step {} says {}, and the step is checked and built without it\n",
            t.cut.path, t.line, t.step, t.said
        ));
    }
    if surplus.is_empty() {
        said.printed
            .push_str(&format!("all {} requires lines are needed\n", taken.len()));
    } else {
        said.status = 1;
    }
    said
}
