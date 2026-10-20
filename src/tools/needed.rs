//! Every requires line is needed.
//!
//! A requires line does work when its theorem cannot be checked without
//! it: what the page needs is the checker's to say, and a line the checker
//! does without and the build does not is a fault in the build. A line the
//! checker does not need is surplus, whatever route a proof took through it
//! while it was there: `requires 2 ∈ ℤ: arithmetic` on a step that
//! `exhibit`s 2 is used when it is written and worked out when it is not
//! (`ELABORATION.md`, R3).
//!
//! So each requires line of each proof is taken away in turn, and the
//! theorem it sits in is checked without it, over the whole theorem where
//! the checker's own rule asks of one step. The lines are shared out among
//! workers that run side by side.
//!
//! A pair naming a variable for itself, `n := n` in a citation, is asked the
//! same way (`SYNTAX.md`, no pair says what goes without saying): a
//! definition's subject with no pair is the proof's letter of that name, and
//! a theorem's variable is found by matching, so such a pair does work only
//! where matching would find something else.

use crate::checker::{check_cuts, Cut};
use crate::corpus::proof::cited_items;
use crate::corpus::skeleton::step_line;
use crate::corpus::{item_kind, proof_files};
use crate::said::Said;
use crate::source::{Memory, Source};
use crate::threads::threads;

/// Where the item a line cites ends, the first word that opens with an
/// item's prefix, `mun:abs`; None for a line that cites none.
fn item_end(line: &str) -> Option<usize> {
    line.split_whitespace().find_map(|word| {
        let item = word.split(',').next().unwrap_or(word);
        let at = word.as_ptr() as usize - line.as_ptr() as usize;
        item_kind(item).map(|_| at + item.len())
    })
}

/// What is taken away: a requires line, by the file lines it spans, or a
/// pair naming a variable for itself, by its file line and its variable.
#[derive(Clone)]
enum Removal {
    Lines {
        start: usize,
        end: usize,
        /// The import lines of the items only this line cites, which go
        /// with it: a file importing an item it cites nothing by is
        /// refused, and that would keep the line where nothing else does.
        imports: Vec<usize>,
    },
    Pair {
        line: usize,
        name: String,
    },
}

/// One thing taken away: where it was, what it was, what it said, the step
/// it sat in, and the file without it.
struct Taken {
    line: usize,
    removal: Removal,
    said: String,
    step: String,
    cut: Cut,
}

/// The text with each removal made: a requires line's lines dropped, and a
/// pair taken out of its citation with the comma that joined it.
fn without(text: &str, removals: &[&Removal]) -> String {
    let mut lines: Vec<Option<String>> =
        text.split('\n').map(|l| Some(l.to_string())).collect();
    for removal in removals {
        match removal {
            Removal::Lines {
                start,
                end,
                imports,
            } => {
                for line in &mut lines[*start..*end] {
                    *line = None;
                }
                for &at in imports {
                    if let Some(line) = lines.get_mut(at) {
                        *line = None;
                    }
                }
            }
            Removal::Pair { line, name } => {
                if let Some(Some(was)) = lines.get(*line) {
                    if let Some(now) = pair_taken_out(was, name) {
                        lines[*line] = Some(now);
                    }
                }
            }
        }
    }
    lines.into_iter().flatten().collect::<Vec<_>>().join("\n")
}

/// The pairs naming a variable for itself in the citation a line writes:
/// each `v := v` after the item, by its variable.
fn identity_pairs(line: &str) -> Vec<String> {
    let Some(end) = item_end(line) else {
        return Vec::new();
    };
    let rest = &line[end..];
    let mut out = Vec::new();
    for (at, _) in rest.match_indices(" := ") {
        let name = rest[..at].rsplit([' ', ',']).next().unwrap_or("");
        let value = rest[at + 4..].split(',').next().unwrap_or("").trim();
        if !name.is_empty() && name == value {
            out.push(name.to_string());
        }
    }
    out
}

/// The line with the pair `name := name` taken out of its citation, and the
/// comma that joined it to the next pair, or to `from`, with it.
fn pair_taken_out(line: &str, name: &str) -> Option<String> {
    let item = item_end(line)?;
    let pair = format!("{name} := {name}");
    let rest = &line[item..];
    let at = rest.match_indices(&pair).map(|(i, _)| i).find(|&i| {
        let after = &rest[i + pair.len()..];
        (rest[..i].ends_with(' ') || rest[..i].ends_with(','))
            && (after.is_empty() || after.starts_with(','))
    })?;
    let (start, end) = (item + at, item + at + pair.len());
    let (before, after) = (&line[..start], &line[end..]);
    if let Some(kept) = before.strip_suffix(", ") {
        return Some(format!("{kept}{after}"));
    }
    // The first pair: the next one moves up, or the item stands alone.
    let next_is_pair = after
        .strip_prefix(", ")
        .is_some_and(|a| a.split(',').next().is_some_and(|p| p.contains(" := ")));
    if next_is_pair {
        return Some(format!("{before}{}", &after[2..]));
    }
    Some(format!("{}{after}", before.trim_end()))
}

/// Every requires line of the proof files `files`, each as the file without
/// it.
fn every_line(source: &dyn Source, files: &[String]) -> Result<Vec<Taken>, String> {
    // A requires line is one the reader reads as one, by the file and line
    // it is on: a note's words "a requires line may …" are no such line.
    let read = crate::corpus::load::corpus(source).map_err(|p| p.to_string())?;
    let requires_at: std::collections::BTreeSet<(String, usize)> = read
        .theorems
        .iter()
        .flat_map(|t| {
            t.steps
                .iter()
                .flat_map(|s| s.requires.iter().map(|r| (t.path.clone(), r.line)))
        })
        .collect();
    let mut out = Vec::new();
    for path in files {
        // Each item the file cites, by the lines citing it, and the line
        // importing it, both counted from 1.
        let cites: Vec<(String, usize)> = read
            .theorems
            .iter()
            .filter(|t| &t.path == path)
            .flat_map(cited_items)
            .collect();
        let imported: Vec<(String, usize)> = read
            .scopes
            .iter()
            .filter(|s| &s.path == path)
            .flat_map(|s| s.items.iter().map(|i| (i.full(), i.line)))
            .collect();
        let text = source.read_text(path).map_err(|e| format!("{path}: {e}"))?;
        let lines: Vec<&str> = text.split('\n').collect();
        let mut theorem: Option<String> = None;
        let mut step = String::new();
        for (i, line) in lines.iter().enumerate() {
            if let Some(name) = line.strip_prefix("theorem ") {
                theorem = Some(str::trim(name).to_string());
                continue;
            }
            if let Some(said) = step_line(line.trim_start()) {
                step = said.number.to_string();
            }
            let Some(theorem) = &theorem else { continue };
            for name in identity_pairs(line) {
                let removal = Removal::Pair {
                    line: i,
                    name: name.clone(),
                };
                out.push(Taken {
                    line: i + 1,
                    said: format!("{name} := {name}"),
                    step: step.clone(),
                    cut: Cut {
                        path: path.clone(),
                        text: without(&text, &[&removal]),
                        theorem: theorem.clone(),
                    },
                    removal,
                });
            }
            let Some(said) = line.trim_start().strip_prefix("requires ") else {
                continue;
            };
            if !requires_at.contains(&(path.clone(), i + 1)) {
                continue;
            }
            // A requires line may go on in a deeper line that starts `from`.
            let indent = line.len() - line.trim_start().len();
            let mut end = i + 1;
            while end < lines.len()
                && lines[end].trim_start().starts_with("from ")
                && lines[end].len() - lines[end].trim_start().len() > indent
            {
                end += 1;
            }
            let spans = |line: usize| line > i && line <= end;
            let imports = imported
                .iter()
                .filter(|(item, _)| {
                    let mut at =
                        cites.iter().filter(|(c, _)| c == item).map(|(_, l)| *l);
                    let first = at.next();
                    first.is_some_and(spans) && at.all(spans)
                })
                .map(|(_, line)| line - 1)
                .collect();
            let removal = Removal::Lines {
                start: i,
                end,
                imports,
            };
            out.push(Taken {
                line: i + 1,
                said: str::trim(said).to_string(),
                step: step.clone(),
                cut: Cut {
                    path: path.clone(),
                    text: without(&text, &[&removal]),
                    theorem: theorem.clone(),
                },
                removal,
            });
        }
    }
    Ok(out)
}

/// Whether each line in `share` is needed: the checker complains of its
/// theorem without it. What the page needs is the checker's to say, and a
/// line the checker can do without that the build cannot is a fault in the
/// build.
fn needed(tree: &Memory, share: &[&Taken]) -> Result<Vec<bool>, String> {
    let cuts: Vec<Cut> = share
        .iter()
        .map(|t| Cut {
            path: t.cut.path.clone(),
            text: t.cut.text.clone(),
            theorem: t.cut.theorem.clone(),
        })
        .collect();
    let checked = check_cuts(tree, &cuts).map_err(|out| out.complained)?;
    Ok(checked
        .iter()
        .map(|problems| !problems.is_empty())
        .collect())
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
            let gone: Vec<&Removal> = kept[i]
                .iter()
                .map(|t| &t.removal)
                .chain([&next.removal])
                .collect();
            asked.push((
                i,
                Taken {
                    line: next.line,
                    removal: next.removal.clone(),
                    said: next.said.clone(),
                    step: next.step.clone(),
                    cut: Cut {
                        path: next.cut.path.clone(),
                        text: without(&text, &gone),
                        theorem: next.cut.theorem.clone(),
                    },
                },
            ));
        }
        let share: Vec<&Taken> = asked.iter().map(|(_, t)| t).collect();
        let needs = needed(tree, &share)?;
        for ((i, _), need) in asked.iter().zip(needs) {
            if !need {
                kept[*i].push(groups[*i][round]);
            }
        }
    }
    Ok(kept.into_iter().flatten().collect())
}

/// Every requires line of every proof file is needed.
pub fn run(source: &dyn Source) -> Said {
    run_over(source, &proof_files(source))
}

/// Every requires line of the proof files `files` is needed: each is taken
/// away in turn, and its theorem checked over the corpus without it. A
/// planted line is asked of its own file alone.
pub fn run_over(source: &dyn Source, files: &[String]) -> Said {
    let mut said = Said::default();
    let tree = match Memory::copy(source, &["corpus", "proofs", "tests"]) {
        Ok(tree) => tree,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    let taken = match every_line(&tree, files) {
        Ok(taken) => taken,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    let workers = threads().clamp(1, 8);
    let shares: Vec<Vec<&Taken>> = (0..workers)
        .map(|w| taken.iter().skip(w).step_by(workers).collect())
        .collect();
    let results: Vec<Result<Vec<bool>, String>> = std::thread::scope(|scope| {
        let running: Vec<_> = shares
            .iter()
            .map(|share| {
                let tree = &tree;
                scope.spawn(move || needed(tree, share))
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
    let surplus = match together(&tree, surplus) {
        Ok(surplus) => surplus,
        Err(e) => {
            said.complained = format!("{e}\n");
            said.status = 2;
            return said;
        }
    };
    for t in &surplus {
        let what = match t.removal {
            Removal::Lines { .. } => {
                format!("the requires line of step {} says", t.step)
            }
            Removal::Pair { .. } => format!("step {} cites with the pair", t.step),
        };
        said.printed.push_str(&format!(
            "{}:{}  {what} {}, and the step is checked and built without it\n",
            t.cut.path, t.line, t.said
        ));
    }
    if surplus.is_empty() {
        let pairs = taken
            .iter()
            .filter(|t| matches!(t.removal, Removal::Pair { .. }))
            .count();
        said.printed.push_str(&format!(
            "all {} requires lines and {pairs} pairs naming a variable for itself are needed\n",
            taken.len() - pairs
        ));
    } else {
        said.status = 1;
    }
    said
}
