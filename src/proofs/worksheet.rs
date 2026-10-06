//! The text the proofs of `proved.mm` are written in.
//!
//! A group of lemmas is a file. Its lines before the first `lemma` are the
//! group's Metamath head, its comment and its `$d` lines, copied into
//! `proved.mm` as they stand; a line starting `#` is a note for a reader,
//! anywhere, and is not copied. Each lemma is written as a proof worksheet:
//!
//! ```text
//! lemma gcoprimesq
//!   |- ( ( ( A e. NN0 /\ B e. ZZ /\ C e. NN0 ) /\ ( A gcd B ) = 1 ) -> …
//!   1 simpr |- ( ( ( A e. NN0 /\ B e. ZZ /\ C e. NN0 ) /\ ( A gcd B ) = 1 ) -> …
//!   2 oveq1d 1 |- ( … -> ( ( A gcd B ) gcd C ) = ( 1 gcd C ) )
//! ```
//!
//! The first line under `lemma` is what it proves, after any `hypothesis`
//! lines naming what it assumes. Each numbered step names the lemma it
//! applies, the steps or hypotheses that lemma's hypotheses are taken from,
//! in its order, and what the step proves; the last step proves the lemma.
//! A line starting with more spaces than a step continues the one above.
//!
//! What a step substitutes is not written: the lemma's statement and its
//! hypotheses, matched against what the step and the steps it takes prove,
//! fix every variable, since set.mm's syntax reads each formula one way. The
//! terms are parsed, the step is built by `Builder::ap`, and the proof is
//! compressed when `proved.mm` is written.

use std::collections::BTreeSet;

use indexmap::IndexMap;

use super::Lemma;
use crate::mm::kernel::{match_term, same, Term};
use crate::mm::spell::{Binds, Builder, Proof};
use crate::outcome::{Checked, Problem};

/// One group read: its head, and its lemmas in order.
pub struct Group {
    pub head: String,
    pub lemmas: Vec<Lemma>,
}

/// One line of a lemma, joined with the lines continuing it.
struct Line {
    /// Where it starts in the file, counted from 1.
    at: usize,
    said: String,
}

/// A lemma as the file writes it, before it is built.
struct Written {
    /// Where its `lemma` line is.
    at: usize,
    label: String,
    lines: Vec<Line>,
}

/// What a step or hypothesis proves, and its proof.
#[derive(Clone)]
struct Shown {
    proof: Proof,
    term: Term,
}

/// A group's lemmas, read from its text and built, each registered in `b`
/// as it is read so that a later one may apply it.
pub fn read(path: &str, text: &str, b: &mut Builder) -> Checked<Group> {
    let defect = |line: usize, why: String| Problem::new(path, line, why);
    let mut head = String::new();
    let mut lines = text.lines().enumerate().peekable();
    while let Some((_, line)) = lines.peek() {
        if line.starts_with("lemma ") {
            break;
        }
        // Blank lines before the head begins part it from the notes.
        if !line.starts_with('#') && !(head.is_empty() && line.trim().is_empty()) {
            head.push_str(line);
            head.push('\n');
        }
        lines.next();
    }
    let mut written: Vec<Written> = Vec::new();
    for (n, line) in lines {
        let at = n + 1;
        if line.starts_with('#') || line.trim().is_empty() {
            continue;
        }
        if let Some(label) = line.strip_prefix("lemma ") {
            written.push(Written {
                at,
                label: label.trim().to_string(),
                lines: Vec::new(),
            });
            continue;
        }
        let Some(one) = written.last_mut() else {
            return Err(defect(at, format!("a line outside any lemma: {line}")));
        };
        let indent = line.len() - line.trim_start().len();
        if indent > 2 {
            let Some(above) = one.lines.last_mut() else {
                return Err(defect(at, "a continuation with nothing above".into()));
            };
            above.said.push(' ');
            above.said.push_str(line.trim());
        } else {
            one.lines.push(Line {
                at,
                said: line.trim().to_string(),
            });
        }
    }
    let mut out = Vec::new();
    for one in &written {
        out.push(lemma(path, one, b)?);
    }
    Ok(Group { head, lemmas: out })
}

/// One lemma, built from its lines.
fn lemma(path: &str, written: &Written, b: &mut Builder) -> Checked<Lemma> {
    let defect = |line: usize, why: String| Problem::new(path, line, why);
    let mut hyps: Vec<(String, String)> = Vec::new();
    let mut statement: Option<String> = None;
    let mut proved: IndexMap<String, Shown> = IndexMap::new();
    let mut last: Option<Shown> = None;
    for Line { at, said } in &written.lines {
        if let Some(rest) = said.strip_prefix("hypothesis ") {
            let (hyp, stated) = rest
                .split_once(' ')
                .ok_or_else(|| defect(*at, "a hypothesis with no statement".into()))?;
            b.hypothesis(hyp, stated);
            let term = formula(b, stated).map_err(|e| defect(*at, e))?;
            let proof = b.step(hyp);
            proved.insert(hyp.to_string(), Shown { proof, term });
            hyps.push((hyp.to_string(), stated.to_string()));
            continue;
        }
        if said.starts_with("|-") {
            statement = Some(said.clone());
            continue;
        }
        let (refs, stated) = said.split_once(" |- ").ok_or_else(|| {
            defect(*at, format!("a step that proves nothing: {said}"))
        })?;
        let stated = format!("|- {stated}");
        let mut words = refs.split_whitespace();
        let number = words.next().unwrap_or_default().to_string();
        let applied = words
            .next()
            .ok_or_else(|| defect(*at, "a step that applies nothing".into()))?
            .to_string();
        let mut taken: Vec<Shown> = Vec::new();
        for r in words {
            let got = proved.get(r).ok_or_else(|| {
                defect(*at, format!("{r} is no step or hypothesis above"))
            })?;
            taken.push(got.clone());
        }
        let term = formula(b, &stated).map_err(|e| defect(*at, e))?;
        let proof = step(b, &applied, &term, &taken).map_err(|e| defect(*at, e))?;
        let shown = Shown { proof, term };
        proved.insert(number, shown.clone());
        last = Some(shown);
    }
    let statement = statement
        .ok_or_else(|| defect(written.at, "a lemma that states nothing".into()))?;
    let last =
        last.ok_or_else(|| defect(written.at, "a lemma with no steps".into()))?;
    let claimed = formula(b, &statement).map_err(|e| defect(written.at, e))?;
    if !same(&claimed, &last.term) {
        return Err(defect(
            written.at,
            "the last step does not prove the lemma".into(),
        ));
    }
    let said: Vec<&str> = hyps.iter().map(|(_, s)| s.as_str()).collect();
    b.define_with_hyps(&written.label, &statement, &said);
    Ok(Lemma {
        label: written.label.clone(),
        statement,
        proof: last.proof,
        hyps,
    })
}

/// A `|- …` line as the term it states.
fn formula(b: &Builder, stated: &str) -> Result<Term, String> {
    let tokens: Vec<&str> = stated.split_whitespace().skip(1).collect();
    b.syntax().parse(&tokens, "wff").map_err(|p| p.to_string())
}

/// One step: `label` applied to what `taken` proves, matched to prove
/// `ground`.
fn step(
    b: &Builder,
    label: &str,
    ground: &Term,
    taken: &[Shown],
) -> Result<Proof, String> {
    let sig = b
        .sigs
        .get(label)
        .ok_or_else(|| format!("no label {label}"))?
        .clone();
    if sig.essentials.len() != taken.len() {
        return Err(format!(
            "{label} takes {} hypotheses and is given {}",
            sig.essentials.len(),
            taken.len()
        ));
    }
    let variables: BTreeSet<String> =
        sig.floats.iter().map(|(_, v)| v.clone()).collect();
    let pattern = b.syntax().statement(&sig).map_err(|p| p.to_string())?;
    let mut binding = match_term(&pattern, ground, &IndexMap::new(), &variables)
        .ok_or_else(|| format!("{label} does not prove what the step says"))?;
    for (n, (essential, shown)) in sig.essentials.iter().zip(taken).enumerate() {
        let tokens: Vec<&str> = essential[1..].iter().map(String::as_str).collect();
        let pattern = b
            .syntax()
            .parse(&tokens, "wff")
            .map_err(|p| p.to_string())?;
        binding = match_term(&pattern, &shown.term, &binding, &variables).ok_or_else(|| {
            format!("what the step takes for hypothesis {} of {label} is not what it asks", n + 1)
        })?;
    }
    let binds: Binds = binding
        .iter()
        .map(|(v, t)| (v.clone(), t.rpn(&b.flabel).to_string()))
        .collect();
    let proofs: Vec<&Proof> = taken.iter().map(|s| &s.proof).collect();
    Ok(b.ap(label, &binds, &proofs))
}
