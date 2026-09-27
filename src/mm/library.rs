//! What a set.mm label expects on the proof stack.
//!
//! A Metamath proof is written in reverse Polish, and a step pushes the
//! label's mandatory floating hypotheses in order, then its essential
//! hypotheses in order. That order is not the order the variables appear in
//! the statement: it is the order their `$f` declarations appear in the
//! file. Nothing but the database knows it, so this module reads it.
//!
//! Only the shape is read, never the proofs, so a pass over set.mm costs a
//! second or two and no verification. A verifier does the same thing as part
//! of checking a proof; this is the part of it the elaborator needs.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use indexmap::{IndexMap, IndexSet};

/// What a label is: an axiom or definition, a theorem, or a floating
/// hypothesis, which proves its variable is of its type and is pushed by
/// label like anything else.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Axiom,
    Theorem,
    Float,
    /// A hypothesis a lemma being written states, registered so its proof
    /// may rest on it. The library's own are kept inside their assertions.
    Essential,
}

impl Kind {
    pub fn keyword(self) -> &'static str {
        match self {
            Kind::Axiom => "$a",
            Kind::Theorem => "$p",
            Kind::Float => "$f",
            Kind::Essential => "$e",
        }
    }
}

/// One label: what it concludes and what it wants pushed.
#[derive(Clone, Debug)]
pub struct Signature {
    pub label: String,
    pub kind: Kind,
    pub statement: Vec<String>,
    /// (typecode, variable) of each mandatory float, in push order.
    pub floats: Vec<(String, String)>,
    pub essentials: Vec<Vec<String>>,
    pub disjoint: BTreeSet<(String, String)>,
}

impl Signature {
    /// The variables to push, in order.
    pub fn push(&self) -> Vec<&str> {
        self.floats.iter().map(|(_, v)| v.as_str()).collect()
    }

    /// The variable a binder in this statement introduces, if one does.
    pub fn bound(&self) -> Option<&str> {
        self.floats
            .iter()
            .find(|(t, _)| t == "setvar")
            .map(|(_, v)| v.as_str())
    }
}

/// Every label of a database, by label, in the order the file declares
/// them.
pub type Signatures = IndexMap<String, Signature>;

/// The library, said on the command line, in the environment, or at the root
/// of the working tree.
pub fn where_set_mm(said: Option<&str>, root: &Path) -> Option<PathBuf> {
    let candidates = [
        said.map(PathBuf::from),
        std::env::var_os("SET_MM").map(PathBuf::from),
        Some(root.join("set.mm")),
    ];
    candidates.into_iter().flatten().find(|p| p.exists())
}

/// Every whitespace-separated token, with comments and includes removed.
///
/// Comments nest in Metamath, so the depth is counted rather than matched.
/// An include names a file rather than saying anything, and the caller
/// supplies the files it wants read, so the directive is dropped.
fn tokens(text: &str, out: &mut Vec<String>) {
    let mut depth = 0usize;
    let mut including = false;
    for tok in text.split_ascii_whitespace() {
        match tok {
            "$(" => depth += 1,
            "$)" => depth = depth.saturating_sub(1),
            _ if depth > 0 => {}
            "$[" => including = true,
            "$]" => including = false,
            _ if !including => out.push(tok.to_string()),
            _ => {}
        }
    }
}

#[derive(Default)]
struct Scope {
    variables: IndexSet<String>,
    floats: Vec<(String, String)>,
    essentials: Vec<Vec<String>>,
    disjoint: BTreeSet<(String, String)>,
}

/// Every label in the texts, as a signature.
///
/// Includes are not followed. A file that includes another is read by
/// passing both, in the order the includes would have reached them: the
/// tokens become one stream, which is what an include means.
pub fn read_texts(texts: &[&str]) -> Signatures {
    let mut toks = Vec::new();
    for text in texts {
        tokens(text, &mut toks);
    }
    let find = |from: usize, what: &str| -> usize {
        (from..toks.len())
            .find(|&j| toks[j] == what)
            .unwrap_or(toks.len())
    };
    let mut stack: Vec<Scope> = vec![Scope::default()];
    let mut out = Signatures::new();
    let mut label: Option<String> = None;
    let mut i = 0;
    while i < toks.len() {
        let tok = toks[i].as_str();
        match tok {
            "${" => {
                stack.push(Scope::default());
                i += 1;
            }
            "$}" => {
                stack.pop();
                i += 1;
            }
            "$v" | "$c" | "$d" | "$f" | "$e" | "$a" | "$p" => {
                let end = if tok == "$p" {
                    find(i, "$=")
                } else {
                    find(i, "$.")
                };
                let body: Vec<String> = toks[i + 1..end.min(toks.len())].to_vec();
                statement(&mut stack, &mut out, tok, label.take(), body);
                i = if tok == "$p" { find(end, "$.") } else { end } + 1;
            }
            _ => {
                label = Some(tok.to_string());
                i += 1;
            }
        }
    }
    out
}

/// Every label in the files, read as one stream in the order given.
pub fn read(paths: &[&Path]) -> std::io::Result<Signatures> {
    let texts: Vec<String> = paths
        .iter()
        .map(std::fs::read_to_string)
        .collect::<Result<_, _>>()?;
    let refs: Vec<&str> = texts.iter().map(String::as_str).collect();
    Ok(read_texts(&refs))
}

fn statement(
    stack: &mut [Scope],
    out: &mut Signatures,
    kind: &str,
    label: Option<String>,
    body: Vec<String>,
) {
    let top = stack.last_mut().unwrap();
    match kind {
        "$v" => top.variables.extend(body),
        "$c" => {}
        "$d" => {
            for a in &body {
                for b in &body {
                    if a != b {
                        let pair = if a < b {
                            (a.clone(), b.clone())
                        } else {
                            (b.clone(), a.clone())
                        };
                        top.disjoint.insert(pair);
                    }
                }
            }
        }
        "$f" => {
            top.floats.push((body[0].clone(), body[1].clone()));
            let label = label.unwrap_or_default();
            out.insert(
                label.clone(),
                Signature {
                    label,
                    kind: Kind::Float,
                    statement: body,
                    floats: Vec::new(),
                    essentials: Vec::new(),
                    disjoint: BTreeSet::new(),
                },
            );
        }
        "$e" => top.essentials.push(body),
        _ => {
            let kind = if kind == "$a" {
                Kind::Axiom
            } else {
                Kind::Theorem
            };
            let label = label.unwrap_or_default();
            let made = assertion(stack, kind, &label, body);
            out.insert(label, made);
        }
    }
}

/// The mandatory hypotheses of one assertion, in push order.
fn assertion(stack: &[Scope], kind: Kind, label: &str, body: Vec<String>) -> Signature {
    let active: IndexSet<&str> = stack
        .iter()
        .flat_map(|s| s.variables.iter().map(String::as_str))
        .collect();
    let essentials: Vec<Vec<String>> =
        stack.iter().flat_map(|s| s.essentials.clone()).collect();
    let mut wanted: IndexSet<&str> = essentials
        .iter()
        .chain(std::iter::once(&body))
        .flat_map(|h| h.iter().map(String::as_str))
        .filter(|t| active.contains(t))
        .collect();
    let names = wanted.clone();
    let mut floats = Vec::new();
    for s in stack {
        for (typecode, var) in &s.floats {
            if wanted.shift_remove(var.as_str()) {
                floats.push((typecode.clone(), var.clone()));
            }
        }
    }
    let disjoint = stack
        .iter()
        .flat_map(|s| s.disjoint.iter())
        .filter(|(a, b)| names.contains(a.as_str()) && names.contains(b.as_str()))
        .cloned()
        .collect();
    Signature {
        label: label.to_string(),
        kind,
        statement: body,
        floats,
        essentials,
        disjoint,
    }
}

/// A term written the way a Metamath file writes it.
///
/// A proof is reverse Polish because that is what the kernel reads, and a
/// `$a` states its claim in full, so anything written out has to come back
/// the other way.
pub fn render(rpn: &str, sigs: &Signatures) -> String {
    let mut stack: Vec<String> = Vec::new();
    for token in rpn.split_whitespace() {
        let sig = sigs
            .get(token)
            .unwrap_or_else(|| panic!("no label {token} to render"));
        let args = stack.split_off(stack.len() - sig.floats.len());
        let push = sig.push();
        let written: Vec<&str> = sig.statement[1..]
            .iter()
            .map(|t| match push.iter().position(|v| v == t) {
                Some(at) => args[at].as_str(),
                None => t.as_str(),
            })
            .collect();
        stack.push(written.join(" "));
    }
    stack.into_iter().next().unwrap_or_default()
}

/// A count written with a comma between each three digits, as a person
/// reads a library's size.
pub fn thousands(n: usize) -> String {
    let digits = n.to_string();
    let mut out = String::new();
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i) % 3 == 0 {
            out.push(',');
        }
        out.push(c);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floats_are_pushed_in_declaration_order() {
        let text = "$c wff |- ( -> ) $. $v ps ph $. wps $f wff ps $. wph $f wff ph $.
                    ${ $d ph ps $. ax $a |- ( ph -> ps ) $. $}";
        let sigs = read_texts(&[text]);
        let ax = &sigs["ax"];
        assert_eq!(ax.push(), vec!["ps", "ph"]);
        assert!(ax.disjoint.contains(&("ph".to_string(), "ps".to_string())));
        assert_eq!(sigs["wph"].kind, Kind::Float);
    }
}
