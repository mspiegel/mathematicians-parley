//! The modules of Lean and Mathlib that what a Lean file writes comes from,
//! as Lean finds them (`lean/scripts/ModulesOf.lean`), kept in the tree
//! for the Mathlib revision the project builds against, so that a file
//! imports those modules and not the whole of Mathlib.
//!
//! The build asks Lean only for what the table lacks, and a Mathlib of
//! another revision starts the table again.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use super::doc::file::Lookup;
use crate::outcome::Problem;
use crate::source::Source;

/// The table, from the root of the tree.
pub const TABLE: &str = "lean/mathlib-modules.jsonl";

/// The Lean project's manifest, which pins the Mathlib revision.
const MANIFEST: &str = "lean/lake-manifest.json";

/// The script that asks Lean, from the Lean project.
const SCRIPT: &str = "scripts/ModulesOf.lean";

/// What Lean said of one lookup.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// The modules that declare it, Lean's own left out.
    Modules(Vec<String>),
    /// The sample did not parse, and why: a sample the writer made wrong.
    Unread(String),
}

/// Each lookup Lean has answered, for one Mathlib revision and one form of
/// the script that asks.
#[derive(Clone, Debug, Default)]
pub struct ModuleTable {
    /// What the answers hold for: the revision and the script's digest.
    pub made_for: MadeFor,
    pub answers: BTreeMap<Lookup, Answer>,
}

/// The Mathlib revision the manifest pins, and the SHA-256 of the script,
/// as the table's first line keeps them: answers made for others are
/// asked again.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MadeFor {
    pub mathlib: String,
    pub script: String,
}

impl MadeFor {
    /// The revision and script of the tree.
    fn of(source: &dyn Source) -> Result<MadeFor, Problem> {
        use sha2::{Digest, Sha256};
        let script = format!("lean/{SCRIPT}");
        let bytes = source
            .read(&script)
            .map_err(|e| Problem::new(script.clone(), 1, e.to_string()))?;
        let digest: String = Sha256::digest(&bytes)
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        Ok(MadeFor {
            mathlib: mathlib_revision(source)?,
            script: digest,
        })
    }

    /// The table's first line.
    fn line(&self) -> String {
        serde_json::json!({ "mathlib": self.mathlib, "script": self.script })
            .to_string()
    }

    /// What a table's first line says it was made for.
    fn read(line: &str) -> Option<MadeFor> {
        let v: serde_json::Value = serde_json::from_str(line).ok()?;
        Some(MadeFor {
            mathlib: v["mathlib"].as_str()?.to_string(),
            script: v["script"].as_str()?.to_string(),
        })
    }
}

/// One line of the table or of the script's answers.
fn read_line(line: &str) -> Result<(Lookup, Answer), String> {
    let v: serde_json::Value = serde_json::from_str(line).map_err(|e| e.to_string())?;
    let field = |name: &str| v.get(name).and_then(|f| f.as_str());
    let (Some(kind), Some(key)) = (field("kind"), field("key")) else {
        return Err("a line with no kind and key".to_string());
    };
    let Some(lookup) = Lookup::of(kind, key) else {
        return Err(format!("a lookup of the kind {kind}"));
    };
    let answer = match (v.get("modules").and_then(|m| m.as_array()), field("error")) {
        (Some(mods), _) => Answer::Modules(
            mods.iter()
                .filter_map(|m| m.as_str().map(str::to_string))
                .collect(),
        ),
        (None, Some(e)) => Answer::Unread(e.to_string()),
        (None, None) => return Err("a line with no modules and no error".to_string()),
    };
    Ok((lookup, answer))
}

/// A lookup as one line, for the table or for the script to read.
fn line_of(lookup: &Lookup, answer: Option<&Answer>) -> String {
    let mut v = serde_json::json!({ "kind": lookup.kind(), "key": lookup.key() });
    match answer {
        Some(Answer::Modules(m)) => v["modules"] = serde_json::json!(m),
        Some(Answer::Unread(e)) => v["error"] = serde_json::json!(e),
        None => {}
    }
    v.to_string()
}

/// The Mathlib revision the project's manifest pins.
fn mathlib_revision(source: &dyn Source) -> Result<String, Problem> {
    let unread = |why: String| Problem::new(MANIFEST, 1, why);
    let bytes = source.read(MANIFEST).map_err(|e| unread(e.to_string()))?;
    let v: serde_json::Value =
        serde_json::from_slice(&bytes).map_err(|e| unread(e.to_string()))?;
    v["packages"]
        .as_array()
        .and_then(|ps| ps.iter().find(|p| p["name"] == "mathlib"))
        .and_then(|p| p["rev"].as_str())
        .map(str::to_string)
        .ok_or_else(|| unread("no mathlib package with a revision".to_string()))
}

impl ModuleTable {
    /// The table in the tree, for the Mathlib the manifest pins and the
    /// script as it stands: empty where there is none yet or it was made
    /// for another revision or script.
    pub fn read(source: &dyn Source) -> Result<ModuleTable, Problem> {
        let mut table = ModuleTable {
            made_for: MadeFor::of(source)?,
            answers: BTreeMap::new(),
        };
        if !source.exists(TABLE) {
            return Ok(table);
        }
        let bytes = source
            .read(TABLE)
            .map_err(|e| Problem::new(TABLE, 1, e.to_string()))?;
        let text = String::from_utf8_lossy(&bytes);
        let mut lines = text.lines().enumerate();
        let made_for = lines.next().and_then(|(_, l)| MadeFor::read(l));
        if made_for.as_ref() != Some(&table.made_for) {
            return Ok(table);
        }
        for (i, line) in lines {
            let (lookup, answer) =
                read_line(line).map_err(|why| Problem::new(TABLE, i + 1, why))?;
            table.answers.insert(lookup, answer);
        }
        Ok(table)
    }

    /// The table as the file keeps it: the revision, then each answer.
    pub fn text(&self) -> String {
        let mut out = self.made_for.line();
        out.push('\n');
        for (lookup, answer) in &self.answers {
            out.push_str(&line_of(lookup, Some(answer)));
            out.push('\n');
        }
        out
    }

    /// Those of `wanted` the table has no answer for.
    pub fn missing<'a>(
        &self,
        wanted: impl IntoIterator<Item = &'a Lookup>,
    ) -> BTreeSet<Lookup> {
        wanted
            .into_iter()
            .filter(|l| !self.answers.contains_key(*l))
            .cloned()
            .collect()
    }

    /// Lean's answers for `asked`, from the Lean project under `root`,
    /// added to the table.
    pub fn ask(
        &mut self,
        root: &Path,
        asked: &BTreeSet<Lookup>,
    ) -> Result<(), Problem> {
        let failed = |why: String| Problem::new(SCRIPT, 1, why);
        let project = root.join("lean");
        // The files Lean reads and writes, from the project, where it runs.
        let (questions, answers) = (
            ".lake/modules-of/asked.jsonl",
            ".lake/modules-of/answers.jsonl",
        );
        std::fs::create_dir_all(project.join(".lake/modules-of"))
            .map_err(|e| failed(e.to_string()))?;
        let lines: Vec<String> = asked.iter().map(|l| line_of(l, None)).collect();
        std::fs::write(project.join(questions), lines.join("\n") + "\n")
            .map_err(|e| failed(e.to_string()))?;
        let run = Command::new("lake")
            .args(["env", "lean", "--run", SCRIPT, questions, answers])
            .current_dir(&project)
            .output()
            .map_err(|e| failed(format!("lake did not run: {e}")))?;
        if !run.status.success() {
            return Err(failed(format!(
                "Lean could not answer: {}{}",
                String::from_utf8_lossy(&run.stdout),
                String::from_utf8_lossy(&run.stderr)
            )));
        }
        let text = std::fs::read_to_string(project.join(answers))
            .map_err(|e| failed(e.to_string()))?;
        for (i, line) in text.lines().filter(|l| !l.is_empty()).enumerate() {
            let (lookup, answer) = read_line(line)
                .map_err(|why| failed(format!("answer {}: {why}", i + 1)))?;
            self.answers.insert(lookup, answer);
        }
        Ok(())
    }
}
