//! One theorem of the corpus written as a Lean theorem, step by step.
//!
//! Each step is a `have` whose type is the step's claim and whose proof is
//! what its method is in Lean (`LEAN.md`, "What each method becomes"). A
//! step that owns a block proves its claim by the block's steps, opened by
//! what the block's lines introduce. Tactics see every line above them, as
//! Mathlib's proofs do. A comment above each step says where it stands on
//! the page, and each line written records the step it was written for, so
//! that a line Lean refuses is reported against the page.

use indexmap::IndexMap;

use super::expr::{LetterType, Printed, Writer};
use super::items::{Item, Sentence};
use super::names::{line_name, snake};
use super::statement::{binders, introduces, Asked, Binder};
use super::templates::Templates;
use crate::checker::record::Cited;
use crate::checker::{CheckedCorpus, CheckedTheorem};
use crate::citing::Way;
use crate::corpus::{Head, Intro, Justification, Method, Step, Theorem};
use crate::formula::page::Written;
use crate::formula::Node;
use crate::notations::{BICONDITIONAL, CONDITIONAL, EQUALITY, IMPLICATION, ORDER};
use crate::outcome::Route;

/// A Lean file, and for each of its lines the place on the page it was
/// written for.
#[derive(Clone, Debug, Default)]
pub struct LeanFile {
    pub text: String,
    pub origins: Vec<Origin>,
}

/// Where a line of a Lean file comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// The line of the Lean file, from 1.
    pub line: usize,
    /// The line of the proof file it was written for.
    pub page_line: usize,
    /// What it was written for.
    pub spot: Spot,
}

/// What a line of a Lean file was written for.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Spot {
    /// The theorem's statement, or a line of the file around it.
    Statement,
    /// A step, by its number as the page writes it.
    Step(String),
}

/// What writing a theorem reads: the corpus as checked, the notations and
/// items in Lean, and the theorems of the corpus as items in Lean.
pub struct Sources<'a> {
    pub checked: &'a CheckedCorpus,
    pub templates: &'a Templates,
    /// What each notation is to the methods' decisions, which `algebra`
    /// asks for its multipliers.
    pub targets: &'a crate::methods::terms::Targets,
    /// Every item a citation may name that has a Lean form, by full name:
    /// the library's records and the corpus's theorems.
    pub items: &'a IndexMap<String, Item>,
}

/// The theorem as an item of the library: its statement's binders, and its
/// `then` sentences joined into one Lean statement, each taken by its
/// projection.
pub fn as_item(sources: &Sources, thm: &Theorem, rec: &CheckedTheorem) -> Route<Item> {
    let mut writer = Writer {
        grammar: &sources.checked.grammar,
        templates: sources.templates,
        letters: IndexMap::new(),
    };
    let stated = match statement(&mut writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    let module = super::names::module_of(&thm.qualified());
    let decl = format!("{module}.{}", snake(&thm.name));
    let n = stated.conclusion.len();
    let mut written: Vec<Node> = hypothesis_sentences(thm, rec)
        .into_iter()
        .flat_map(|(_, s)| s.into_iter().map(|(node, _)| node))
        .collect();
    written.extend(stated.conclusion.iter().map(|c| c.says.clone()));
    let arithmetic = super::readback::page_arithmetic(&writer, &written);
    let sentences = stated
        .conclusion
        .into_iter()
        .enumerate()
        .map(|(i, c)| Sentence {
            decl: decl.clone(),
            binders: stated.binders.clone(),
            says: c.says,
            prop: c.prop.text,
            part: projection(i, n),
            arithmetic: arithmetic.clone(),
        })
        .collect();
    Route::Built(Item {
        module,
        sentences,
        proofs: Vec::new(),
    })
}

/// The projection that takes sentence `i` of `n` joined by `∧`, which
/// chains to the right: `.1`, `.2.1`, …, and the last `.2.2…`.
fn projection(i: usize, n: usize) -> String {
    if n == 1 {
        return String::new();
    }
    let mut out = ".2".repeat(i);
    if i + 1 < n {
        out.push_str(".1");
    }
    out
}

/// Each `let` and `assume` line of a theorem, by its label, with each of
/// its sentences and the Lean name of the hypothesis it is: the label, or
/// `H3a`, `H3b` for a line of several sentences.
fn hypothesis_sentences(
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Vec<(String, Vec<(Node, String)>)> {
    let mut out = Vec::new();
    for (i, h) in thm.hypotheses.iter().enumerate() {
        let label = h.label.clone().unwrap_or_else(|| format!("H{}", i + 1));
        let nodes: Vec<Node> = h
            .body(&thm.path)
            .sentences()
            .iter()
            .filter_map(|s| rec.page.get(s).cloned())
            .collect();
        let base = line_name(&label);
        let n = nodes.len();
        let said = nodes
            .into_iter()
            .enumerate()
            .map(|(k, node)| {
                let name = if n == 1 {
                    base.clone()
                } else {
                    format!("{base}{}", (b'a' + k as u8) as char)
                };
                (node, name)
            })
            .collect();
        out.push((label, said));
    }
    out
}

/// What a theorem states, in Lean.
struct Statement {
    /// Its binders, from its `let` and `assume` lines.
    binders: Vec<Binder>,
    /// Each sentence of its `then` line.
    conclusion: Vec<Concluded>,
}

/// One sentence a theorem concludes: its tree, and its Lean text.
struct Concluded {
    says: Node,
    prop: Printed,
}

/// A theorem's binders, from its `let` and `assume` lines, and each
/// sentence of its `then` line with its Lean text.
fn statement(
    writer: &mut Writer,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<Statement> {
    let said = hypothesis_sentences(thm, rec);
    let read: usize = said.iter().map(|(_, s)| s.len()).sum();
    let written: usize = thm
        .hypotheses
        .iter()
        .map(|h| h.body(&thm.path).sentences().len())
        .sum();
    if read != written {
        return Route::no("a hypothesis the checker did not read");
    }
    let asked: Vec<Asked> = said
        .iter()
        .flat_map(|(_, s)| s)
        .map(|(node, name)| Asked {
            node,
            name: name.clone(),
        })
        .collect();
    let binders = match binders(writer, &asked) {
        Route::Built(b) => b,
        Route::Declined(d) => return Route::Declined(d),
    };
    let mut conclusion = Vec::new();
    for s in thm.stated().sentences() {
        let Some(node) = rec.page.get(&s) else {
            return Route::no(format!("{}, which the checker did not read", s.text()));
        };
        let prop = match writer.formula(node) {
            Route::Built(p) => p,
            Route::Declined(d) => return Route::Declined(d),
        };
        conclusion.push(Concluded {
            says: node.clone(),
            prop,
        });
    }
    Route::Built(Statement {
        binders,
        conclusion,
    })
}

/// Writes one theorem's proof.
struct Proof<'a> {
    sources: &'a Sources<'a>,
    thm: &'a Theorem,
    rec: &'a CheckedTheorem,
    writer: Writer<'a>,
    lines: Vec<String>,
    origins: Vec<Origin>,
    /// The Lean names of each line the page can cite, by the reference
    /// that cites it: a step's number or a label.
    named: IndexMap<String, Vec<String>>,
    /// What each line the page can cite says, sentence by sentence, with
    /// the Lean name of each sentence's proof, by the reference that cites
    /// it.
    trees: IndexMap<String, Vec<(Node, String)>>,
    /// The defines written so far, by their index in the theorem's.
    defined: indexmap::IndexSet<usize>,
}

/// The theorem written as a Lean file's declaration: its statement and its
/// proof, with an origin for every line, counted from the first line of
/// the declaration.
pub fn theorem(
    sources: &Sources,
    thm: &Theorem,
    rec: &CheckedTheorem,
) -> Route<LeanFile> {
    let mut proof = Proof {
        sources,
        thm,
        rec,
        writer: Writer {
            grammar: &sources.checked.grammar,
            templates: sources.templates,
            letters: IndexMap::new(),
        },
        lines: Vec::new(),
        origins: Vec::new(),
        named: IndexMap::new(),
        trees: IndexMap::new(),
        defined: indexmap::IndexSet::new(),
    };
    let Statement {
        binders,
        conclusion,
    } = match statement(&mut proof.writer, thm, rec) {
        Route::Built(s) => s,
        Route::Declined(d) => return Route::Declined(d),
    };
    for (label, said) in hypothesis_sentences(thm, rec) {
        let names: Vec<String> = said.iter().map(|(_, n)| n.clone()).collect();
        proof.named.insert(label.clone(), names);
        proof.trees.insert(label, said);
    }
    let props: Vec<String> = conclusion.iter().map(|c| c.prop.at(36)).collect();
    let binders: Vec<String> = binders.iter().map(Binder::lean).collect();
    let space = if binders.is_empty() { "" } else { " " };
    proof.push(
        format!(
            "theorem {}{space}{} :\n    {} := by",
            snake(&thm.name),
            binders.join(" "),
            props.join(" ∧ ")
        ),
        thm.line,
        Spot::Statement,
    );
    let top: Vec<usize> = (0..thm.steps.len())
        .filter(|&i| rec.places[i].is_none())
        .collect();
    if let Route::Declined(d) = proof.steps(&top, 1) {
        return Route::Declined(d);
    }
    if conclusion.len() > 1 {
        proof.push(
            format!(
                "  exact ⟨{}⟩",
                vec!["by parley_side"; conclusion.len()].join(", ")
            ),
            thm.conclusion_line,
            Spot::Statement,
        );
    } else {
        proof.push(
            "  parley_side".to_string(),
            thm.conclusion_line,
            Spot::Statement,
        );
    }
    let mut text = String::new();
    let mut origins = Vec::new();
    let mut at = 1;
    for (line, origin) in proof.lines.iter().zip(proof.origins) {
        for _ in line.lines() {
            origins.push(Origin {
                line: at,
                ..origin.clone()
            });
            at += 1;
        }
        text.push_str(line);
        text.push('\n');
    }
    Route::Built(LeanFile { text, origins })
}

/// Indentation for a depth of nesting.
fn pad(depth: usize) -> String {
    "  ".repeat(depth)
}

/// What proves a claim: a justification, and what the checker read of the
/// item it cites. A step has one, and so does each of its requires lines
/// and each line of a calculation that gives a reason of its own.
#[derive(Clone, Copy)]
struct Reason<'r> {
    just: &'r Justification,
    cited: Option<&'r Cited>,
}

impl<'a> Proof<'a> {
    fn push(&mut self, line: String, page_line: usize, spot: Spot) {
        self.lines.push(line);
        self.origins.push(Origin {
            line: 0,
            page_line,
            spot,
        });
    }

    fn step_spot(step: &Step) -> Spot {
        Spot::Step(match step.number.number() {
            Some(n) => n.to_string(),
            None => "the theorem".to_string(),
        })
    }

    /// The steps, in order, each at the depth given.
    fn steps(&mut self, indices: &[usize], depth: usize) -> Route<()> {
        for &i in indices {
            if let Route::Declined(d) = self.step(i, depth) {
                return Route::Declined(d);
            }
        }
        Route::Built(())
    }

    /// A step's claim: each sentence, read, with its Lean text; a
    /// membership Lean's types already give is left out, since nothing
    /// needs saying.
    fn claim(&self, step: &Step) -> Route<Vec<(Node, Printed)>> {
        let mut out = Vec::new();
        for s in step.claim.sentences() {
            let Some(node) = self.rec.page.get(&s) else {
                return Route::no(format!(
                    "{}, which the checker did not read",
                    s.text()
                ));
            };
            let printed = match self.writer.formula(node) {
                Route::Built(p) => p,
                Route::Declined(d) => return Route::Declined(d),
            };
            if printed.text != "True" {
                out.push((node.clone(), printed));
            }
        }
        Route::Built(out)
    }

    /// The Lean names of a step's sentences: `s2` for one, `s2a`, `s2b` for
    /// several.
    fn names_of(step: &Step, count: usize) -> Vec<String> {
        let base = match step.number.number() {
            Some(n) => line_name(&n.to_string()),
            None => "sThm".to_string(),
        };
        if count == 1 {
            return vec![base];
        }
        (0..count)
            .map(|i| format!("{base}{}", (b'a' + i as u8) as char))
            .collect()
    }

    /// The letters a step's claim introduces, `k ∈ ℤ`, added to those in
    /// scope.
    fn introduce(&mut self, step: &Step) {
        for s in step.claim.sentences() {
            if let Some(node) = self.rec.page.get(&s) {
                if let Some((letter, system)) = introduces(node) {
                    self.writer.letters.insert(
                        letter,
                        LetterType::Number(super::expr::letter_type(system)),
                    );
                }
            }
        }
    }

    fn step(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        // The defines written above this step in its block, where the
        // checker opens them.
        let due: Vec<usize> = (0..self.thm.defines.len())
            .filter(|&d| {
                !self.defined.contains(&d)
                    && self.thm.defines[d].line < step.line
                    && self.thm.defines[d].line > self.thm.conclusion_line
                    && self.rec.defines.get(d).copied().flatten() == self.rec.places[i]
            })
            .collect();
        for d in due {
            if let Route::Declined(why) = self.define(d, depth) {
                return Route::Declined(why);
            }
        }
        let spot = Self::step_spot(step);
        let p = pad(depth);
        self.push(
            format!("{p}-- {}. {}", step.number, step.just.text.trim()),
            step.line,
            spot.clone(),
        );
        for (k, r) in step.requires.iter().enumerate() {
            let node = match self.tree(&r.fact) {
                Route::Built(n) => n,
                Route::Declined(d) => return Route::Declined(d),
            };
            let fact = match self.writer.formula(&node) {
                Route::Built(f) => f,
                Route::Declined(d) => return Route::Declined(d),
            };
            if fact.text == "True" {
                continue;
            }
            let Ok(just) = &r.by else {
                return Route::no("a requires line whose reason does not read");
            };
            let reason = Reason {
                just,
                cited: self.rec.cited_requires.get(&r.line),
            };
            let proof = match self.proof_of(reason, 0, &node) {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            let name = format!("r{}_{}", step.line, k + 1);
            self.push(
                indented(&format!("{p}have {name} : {} := {proof}", fact.text), &p),
                r.line,
                spot.clone(),
            );
        }
        if let Head::Method(Method::Obtain) = step.just.head {
            return self.obtain(i, depth);
        }
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        if let Head::Method(m) = step.just.head {
            // A calculation's lines are its proof, written as Lean's calc;
            // every other block's steps stand in it.
            if m.takes_block() && m != Method::Calculation {
                return self.block(i, m, &claim, &names, depth);
            }
        }
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        for (k, (node, prop)) in claim.iter().enumerate() {
            let proof = match self.proof_of(reason, k, node) {
                Route::Built(t) => t,
                Route::Declined(d) => return Route::Declined(d),
            };
            self.push(
                indented(
                    &format!("{p}have {} : {} := {proof}", names[k], prop.text),
                    &p,
                ),
                step.line,
                spot.clone(),
            );
        }
        if step.impossible {
            if let Some(last) = names.last() {
                self.push(
                    format!("{p}exact absurd {last} (by norm_num)"),
                    step.line,
                    spot,
                );
            }
        }
        Route::Built(())
    }

    /// A sentence of the page as the checker read it.
    fn tree(&self, written: &Written) -> Route<Node> {
        match written
            .sentences()
            .first()
            .and_then(|s| self.rec.page.get(s))
        {
            Some(node) => Route::Built(node.clone()),
            None => Route::no(format!(
                "{}, which the checker did not read",
                written.text()
            )),
        }
    }

    /// The proof of sentence `k` of a claim, by its reason.
    fn proof_of(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        match &reason.just.head {
            Head::Item { .. } => self.citation(reason, k, node),
            Head::Method(m) => {
                // A claim said of every member of a set is proved of one,
                // taken as the method's letter.
                let (intros, body, writer) = self.peel(node);
                let tactic = match self.method_proof(reason, *m, body, &writer) {
                    Route::Built(t) => t,
                    Route::Declined(d) => return Route::Declined(d),
                };
                if intros.is_empty() {
                    return Route::Built(tactic);
                }
                let inner = tactic.strip_prefix("by ").unwrap_or(&tactic);
                Route::Built(format!("by intro {}; {inner}", intros.join(" ")))
            }
            Head::Define => {
                Route::no("a step citing a define is not written in Lean yet")
            }
            // A requires line's lines, or one manipulation of one of them:
            // the fact is what they say, or follows from it by arithmetic.
            Head::Lines | Head::Manipulation(_) => {
                Route::Built("by parley_side".to_string())
            }
        }
    }

    /// A claim's leading "for all" taken off: the names its letters and
    /// their guards are introduced by, the body, and the letters in scope
    /// with the claim's own added.
    fn peel<'n>(&self, node: &'n Node) -> (Vec<String>, &'n Node, Writer<'a>) {
        let mut writer = Writer {
            grammar: self.writer.grammar,
            templates: self.writer.templates,
            letters: self.writer.letters.clone(),
        };
        let mut intros = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let name = super::names::letter(&letter.text);
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        s == super::expr::System::Positive,
                    ),
                    None => break,
                }
            };
            writer
                .letters
                .insert(letter.text.to_string(), LetterType::Number(ty));
            intros.push(name.clone());
            if guarded {
                intros.push(format!("h_{name}"));
            }
            body = inner;
        }
        (intros, body, writer)
    }

    /// The proof of a claim by a method that closes it, with the letters
    /// `writer` holds.
    fn method_proof(
        &self,
        reason: Reason,
        m: Method,
        node: &Node,
        writer: &Writer,
    ) -> Route<String> {
        let just = reason.just;
        Route::Built(match m {
            Method::Algebra => {
                let cited = self.cited_parts(&just.refs);
                return super::algebra::algebra(
                    writer,
                    self.sources.targets,
                    node,
                    &cited,
                );
            }
            Method::Arithmetic | Method::RealArithmetic => "by norm_num".to_string(),
            // Rows are linear moves on the line the first row cites, so the
            // claim follows from that line by linear arithmetic, as a step
            // with no rows does from the lines it cites.
            Method::Inequalities | Method::Transitivity | Method::Antisymmetry => {
                "by parley_side".to_string()
            }
            Method::Inspection => "by parley_side".to_string(),
            Method::Substitute => return self.substitute(just),
            Method::Calculation => return self.calculation(just, writer),
            Method::Exhibit => return self.exhibit(just, node),
            Method::Instantiate => return self.instantiate(just, node),
            Method::Membership | Method::Restate | Method::Join => {
                "by parley_side".to_string()
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        })
    }

    /// A define in a proof, `let t = 1/j, a real number`: Lean's `set`, of
    /// the type the line names, or else of the least that holds its value,
    /// whose hypothesis is the define's equation, named by its label.
    fn define(&mut self, d: usize, depth: usize) -> Route<()> {
        self.defined.insert(d);
        let line = &self.thm.defines[d];
        let crate::outcome::Route::Built(crate::corpus::DefineParts::One(def)) =
            crate::corpus::define_parts(&line.text)
        else {
            return Route::no("a define of a function or a phrase");
        };
        if !def.params.is_empty() {
            return Route::no("a define of a function");
        }
        let bodies: Vec<&Node> = self
            .rec
            .page
            .entries()
            .filter(|(key, _)| key.line == line.line)
            .map(|(_, node)| node)
            .collect();
        let [body] = bodies.as_slice() else {
            return Route::no(
                "a define whose value the checker did not read as one term",
            );
        };
        let body = (*body).clone();
        use super::templates::Num;
        let ty = match def.kind.as_deref() {
            Some("a real number") => Num::Real,
            Some("a rational number") => Num::Rat,
            Some("an integer") => Num::Int,
            Some("a complex number") => Num::Complex,
            Some(other) => return Route::no(format!("a define of {other}")),
            None => match self.writer.carrier(&body) {
                Route::Built(n) => n,
                Route::Declined(why) => return Route::Declined(why),
            },
        };
        let value = match self.writer.number_fixed(&body, ty) {
            Route::Built(v) => v,
            Route::Declined(why) => return Route::Declined(why),
        };
        let name = super::names::letter(&def.name);
        let label = line_name(&line.label);
        self.push(
            format!(
                "{}set {name} : {} := {} with {label}",
                pad(depth),
                ty.lean(),
                value.text
            ),
            line.line,
            Spot::Statement,
        );
        self.writer
            .letters
            .insert(def.name.clone(), LetterType::Number(ty));
        let letter = Node::name(body.sort.clone(), &def.name);
        let equation = Node::of(
            crate::notations::EQUALS,
            crate::formula::node::Sort::of("formula"),
            vec![letter, body],
        );
        self.named.insert(line.label.clone(), vec![label.clone()]);
        self.trees
            .insert(line.label.clone(), vec![(equation, label)]);
        Route::Built(())
    }

    /// `exhibit`: the claim's "there is", with the values the checker read
    /// for its letters, and what it says of them left to `parley_side`.
    fn exhibit(&self, just: &Justification, node: &Node) -> Route<String> {
        let Some(step) = self.thm.steps.iter().find(|s| s.just.line == just.line)
        else {
            return Route::no("an exhibit that is no step's");
        };
        let Some(binding) = self
            .rec
            .exhibited
            .get(&step.line)
            .and_then(|all| all.iter().flatten().next())
        else {
            return Route::no("an exhibit the checker read no values for");
        };
        let mut parts = Vec::new();
        let mut body = node;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = binding.get(&letter.text) else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        s == super::expr::System::Positive,
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match self.writer.number_fixed(value, ty) {
                Route::Built(p) => parts.push(p.text),
                Route::Declined(d) => return Route::Declined(d),
            }
            if guarded {
                parts.push("by parley_side".to_string());
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::no("an exhibit of no \"there is\"");
        }
        parts.push("by parley_side".to_string());
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// `instantiate`: the "for all" line at the values given, each guard
    /// left to `parley_side`, and an "if" in it applied where the claim is
    /// what it gives.
    fn instantiate(&self, just: &Justification, node: &Node) -> Route<String> {
        let Some(target) = just
            .target
            .as_deref()
            .or(just.refs.first().map(String::as_str))
        else {
            return Route::no("an instantiate of no line");
        };
        let Some((line, name)) = self.trees.get(target).and_then(|t| t.first()) else {
            return Route::no(format!(
                "instantiate in {target}, which has no Lean name"
            ));
        };
        let mut args = vec![name.clone()];
        let mut body = line;
        while body.notation() == crate::notations::FOR_ALL {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some((_, given)) =
                just.values.pairs().find(|(n, _)| *n == &*letter.text)
            else {
                return Route::no(format!("no value for {}", letter.text));
            };
            let value = match self.tree(given) {
                Route::Built(v) => v,
                Route::Declined(d) => return Route::Declined(d),
            };
            let (ty, guarded) = if set.notation() == crate::notations::INTEGER_RANGE {
                (super::templates::Num::Int, true)
            } else {
                match super::expr::system_of(set) {
                    Some(s) => (
                        super::expr::letter_type(s),
                        s == super::expr::System::Positive,
                    ),
                    None => {
                        return Route::no("a value of a letter of no number system")
                    }
                }
            };
            match self.writer.number_fixed(&value, ty) {
                Route::Built(p) => args.push(p.at(super::expr::MAX)),
                Route::Declined(d) => return Route::Declined(d),
            }
            if guarded {
                args.push("(by parley_side)".to_string());
            }
            body = inner;
        }
        let gives = matches!(body.notation(), CONDITIONAL | IMPLICATION)
            && !matches!(node.notation(), CONDITIONAL | IMPLICATION);
        if gives {
            args.push("(by parley_side)".to_string());
        }
        Route::Built(close(node, &format!("({})", args.join(" "))))
    }

    /// `substitute`: the claim is a line, or the left side of a calculation's
    /// link, with a term put for another by an equation, which a line says
    /// or arithmetic works out.
    fn substitute(&self, just: &Justification) -> Route<String> {
        if !just.rows.is_empty() {
            return Route::no("a substitute step written in rows");
        }
        let equation = match (&just.source, &just.equation) {
            (Some(crate::corpus::skeleton::Source::At(place)), _) => {
                match self.named.get(place.named()).and_then(|n| n.first()) {
                    Some(name) => name.clone(),
                    None => {
                        return Route::no(format!(
                            "substitute from {}, which has no Lean name",
                            place.named()
                        ))
                    }
                }
            }
            (_, Some(written)) => {
                let node = match self.tree(written) {
                    Route::Built(n) => n,
                    Route::Declined(d) => return Route::Declined(d),
                };
                match self.writer.formula(&node) {
                    Route::Built(p) => format!("(show {} by parley_side)", p.text),
                    Route::Declined(d) => return Route::Declined(d),
                }
            }
            _ => return Route::Built("by parley_side".to_string()),
        };
        let into = just
            .into
            .as_ref()
            .and_then(|place| self.named.get(place.named()))
            .and_then(|n| n.first());
        Route::Built(match into {
            Some(line) => format!("by parley_subst_at {equation} {line}"),
            None => format!("by parley_subst {equation}"),
        })
    }

    /// `calculation`: the chain as Lean's `calc`, every term in one type,
    /// each link proved by its reason.
    fn calculation(&self, just: &Justification, writer: &Writer) -> Route<String> {
        let Some(Ok(chain)) = crate::corpus::proof::chain(just, &self.thm.path) else {
            return Route::no("a calculation whose lines do not cut");
        };
        let mut terms = vec![match self.tree(&chain.start) {
            Route::Built(n) => n,
            Route::Declined(d) => return Route::Declined(d),
        }];
        for line in &chain.lines {
            match self.tree(&line.term) {
                Route::Built(n) => terms.push(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let mut at = super::templates::Num::Int;
        for t in &terms {
            match writer.carrier(t) {
                Route::Built(n) => at = at.max(n),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        let mut printed = Vec::new();
        for t in &terms {
            match writer.number(t, at) {
                Route::Built(p) => printed.push(p.at(51)),
                Route::Declined(d) => return Route::Declined(d),
            }
        }
        // A chain of numerals alone is told its type once, on its first term.
        if !terms.iter().any(|t| !t.names().is_empty()) {
            printed[0] = format!("({} : {})", printed[0], at.lean());
        }
        let mut out = String::from("by\n  calc ");
        out.push_str(&printed[0]);
        for (k, line) in chain.lines.iter().enumerate() {
            let relation = match line.relation.as_str() {
                r @ ("=" | "<" | ">" | "≤" | "≥") => r,
                other => return Route::no(format!("a calculation joined by {other}")),
            };
            let proof = match &line.reason {
                Some(r) => {
                    let Ok(by) = &r.by else {
                        return Route::no(
                            "a calculation line whose reason does not read",
                        );
                    };
                    let fact = match self.tree(&r.fact) {
                        Route::Built(n) => n,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    let reason = Reason {
                        just: by,
                        cited: self.rec.cited_requires.get(&r.line),
                    };
                    match self.proof_of(reason, 0, &fact) {
                        Route::Built(p) => p,
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                None if line.cited().is_some() => "by parley_side".to_string(),
                None => "by norm_num".to_string(),
            };
            let term = &printed[k + 1];
            if k == 0 {
                out.push_str(&format!(" {relation} {term} := {proof}"));
            } else {
                out.push_str(&format!("\n    _ {relation} {term} := {proof}"));
            }
        }
        Route::Built(out)
    }

    /// Each sentence of the lines `refs` names, each conjunction taken apart
    /// into its parts, with the Lean term that proves each part.
    fn cited_parts(&self, refs: &[String]) -> Vec<super::algebra::Cited> {
        let mut out = Vec::new();
        for r in refs {
            for (node, name) in self.trees.get(r).into_iter().flatten() {
                conjuncts(node, name.clone(), &mut out);
            }
        }
        out
    }

    /// The Lean term an item's sentence is at a citation: the theorem with
    /// each letter given its value, and each hypothesis left to
    /// `parley_side`.
    fn instance(
        &self,
        sentence: &Sentence,
        binding: &crate::matching::Binding,
    ) -> Route<String> {
        let mut args = Vec::new();
        for b in &sentence.binders {
            match b {
                Binder::Letter { name, page, ty } => {
                    let Some(value) =
                        binding.get(&crate::formula::symbol::Symbol::of(page))
                    else {
                        args.push(format!("({name} := _)"));
                        continue;
                    };
                    let printed = match ty {
                        LetterType::Number(n) => self.writer.number_fixed(value, *n),
                        LetterType::Function { .. } => {
                            Route::no("a function given as a citation's value")
                        }
                    };
                    match printed {
                        Route::Built(p) => args.push(format!("({name} := {})", p.text)),
                        Route::Declined(d) => return Route::Declined(d),
                    }
                }
                Binder::Fact { .. } => args.push("(by parley_side)".to_string()),
            }
        }
        let head = if args.is_empty() {
            sentence.decl.clone()
        } else {
            format!("({} {})", sentence.decl, args.join(" "))
        };
        Route::Built(format!("{head}{}", sentence.part))
    }

    /// The item a reason cites, in Lean.
    fn cited_item<'r>(&self, reason: Reason<'r>) -> Route<(&Item, &'r Cited)>
    where
        'a: 'r,
    {
        let Some(cited) = reason.cited else {
            return Route::no("a citation the checker did not read");
        };
        match self.sources.items.get(&cited.item) {
            Some(item) => Route::Built((item, cited)),
            None => Route::no(format!("{} has no Lean form", cited.item)),
        }
    }

    /// Sentence `k` of a claim, by the item its reason cites.
    fn citation(&self, reason: Reason, k: usize, node: &Node) -> Route<String> {
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let Some(concluded) = cited.concluded.get(k) else {
            return Route::no("a claim sentence no conclusion of the item gives");
        };
        let Some(sentence) = item.sentences.get(concluded.sentence) else {
            return Route::no("a conclusion the item does not have in Lean");
        };
        let inst = match self.instance(sentence, &cited.binding) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        let iff = sentence.says.notation() == BICONDITIONAL;
        let implication = matches!(sentence.says.notation(), CONDITIONAL | IMPLICATION);
        let term = match concluded.way {
            Way::AsWritten => inst,
            Way::Forward if iff => format!("({inst}).mp (by parley_side)"),
            Way::Forward if implication => format!("{inst} (by parley_side)"),
            Way::Forward => {
                return Route::no("a forward reading of a sentence that is no ↔ or if")
            }
            Way::Backward => {
                let witness = match self.witnesses(sentence, cited) {
                    Route::Built(w) => w,
                    Route::Declined(d) => return Route::Declined(d),
                };
                return Route::Built(format!("({inst}).mpr {witness}"));
            }
        };
        Route::Built(close(node, &term))
    }

    /// The proof of the right side of a definition a step folds: its
    /// witnesses, where it is a "there is", and its body left to
    /// `parley_side`.
    fn witnesses(
        &self,
        sentence: &Sentence,
        cited: &crate::checker::record::Cited,
    ) -> Route<String> {
        let [_, right] = sentence.says.children.as_slice() else {
            return Route::no("a definition of other than two sides");
        };
        let mut parts = Vec::new();
        let mut body = right;
        while body.notation() == crate::notations::THERE_IS {
            let [letter, set, inner] = body.children.as_slice() else {
                break;
            };
            let Some(value) = cited.bound.get(&letter.text) else {
                return Route::no(format!("no witness for {}", letter.text));
            };
            let system = super::expr::system_of(set);
            let ty = match system {
                Some(s) => super::expr::letter_type(s),
                None => return Route::no("a witness ranging over no number system"),
            };
            match self.writer.number_fixed(value, ty) {
                Route::Built(p) => parts.push(p.text),
                Route::Declined(d) => return Route::Declined(d),
            }
            if system == Some(super::expr::System::Positive) {
                parts.push("by parley_side".to_string());
            }
            body = inner;
        }
        if parts.is_empty() {
            return Route::Built("(by parley_side)".to_string());
        }
        parts.push("by parley_side".to_string());
        Route::Built(format!("⟨{}⟩", parts.join(", ")))
    }

    /// `obtain`: the witnesses of a "there is" an item gives, named as the
    /// claim names them.
    fn obtain(&mut self, i: usize, depth: usize) -> Route<()> {
        let step = &self.thm.steps[i];
        let reason = Reason {
            just: &step.just,
            cited: self.rec.cited[i].as_ref(),
        };
        let (item, cited) = match self.cited_item(reason) {
            Route::Built(x) => x,
            Route::Declined(d) => return Route::Declined(d),
        };
        let item = item.clone();
        let cited = cited.clone();
        let Some(at) = cited.obtained else {
            return Route::no("an obtain that takes no sentence of its item");
        };
        let before: usize = match self.sources.checked.library.groups.get(&cited.item) {
            Some(Some(groups)) => {
                groups[..cited.group].iter().map(|g| g.gives.len()).sum()
            }
            _ => 0,
        };
        let Some(sentence) = item.sentences.get(before + at) else {
            return Route::no("an obtain of a sentence the item does not have in Lean");
        };
        let mut binding = cited.binding.clone();
        for (k, v) in &cited.written {
            binding.entry(*k).or_insert_with(|| v.clone());
        }
        let inst = match self.instance(sentence, &binding) {
            Route::Built(t) => t,
            Route::Declined(d) => return Route::Declined(d),
        };
        let source = if sentence.says.notation() == BICONDITIONAL {
            format!("({inst}).mp (by parley_side)")
        } else {
            inst
        };
        self.introduce(step);
        let claim = match self.claim(step) {
            Route::Built(c) => c,
            Route::Declined(d) => return Route::Declined(d),
        };
        let names = Self::names_of(step, claim.len());
        if let Some(n) = step.number.number() {
            self.named.insert(n.to_string(), names.clone());
            let said = claim
                .iter()
                .zip(&names)
                .map(|((node, _), name)| (node.clone(), name.clone()))
                .collect();
            self.trees.insert(n.to_string(), said);
        }
        let mut pattern: Vec<String> = step
            .just
            .obtained
            .iter()
            .map(|l| super::names::letter(l))
            .collect();
        pattern.extend(names.iter().cloned());
        let p = pad(depth);
        self.push(
            format!("{p}obtain ⟨{}⟩ := {source}", pattern.join(", ")),
            step.line,
            Self::step_spot(step),
        );
        Route::Built(())
    }

    /// A step that owns a block: its claim proved by the block's steps,
    /// opened by its lines.
    fn block(
        &mut self,
        i: usize,
        method: Method,
        claim: &[(Node, Printed)],
        names: &[String],
        depth: usize,
    ) -> Route<()> {
        let step = &self.thm.steps[i];
        let spot = Self::step_spot(step);
        let [(_, prop)] = claim else {
            return Route::no("a block whose claim is other than one sentence");
        };
        let Some(block_at) = self.rec.blocks.iter().position(|b| b.owner == i) else {
            return Route::no("a block the checker did not record");
        };
        let block = self.rec.blocks[block_at].clone();
        let p = pad(depth);
        let inner = pad(depth + 1);
        self.push(
            format!("{p}have {} : {} := by", names[0], prop.text),
            step.line,
            spot.clone(),
        );
        let kept = self.writer.letters.clone();
        let parts: Vec<Option<usize>> = if step.parts.is_empty() {
            vec![None]
        } else {
            (0..step.parts.len()).map(Some).collect()
        };
        match method {
            Method::Proof | Method::Contradiction => {
                if let Route::Declined(d) = self.open(step, None, depth + 1) {
                    return Route::Declined(d);
                }
                let children: Vec<usize> = block.children.clone();
                if let Route::Declined(d) = self.steps(&children, depth + 1) {
                    return Route::Declined(d);
                }
                self.push(format!("{inner}parley_side"), step.line, spot.clone());
            }
            Method::Cases => {
                let Some(from) = step.just.from.first() else {
                    return Route::no("cases from no line");
                };
                let Some(source) =
                    self.named.get(from).and_then(|n| n.first()).cloned()
                else {
                    return Route::no(format!(
                        "cases from {from}, which has no Lean name"
                    ));
                };
                let labels: Vec<String> = parts
                    .iter()
                    .map(|part| {
                        step.openers
                            .iter()
                            .find(|o| o.part == *part)
                            .map(|o| line_name(&o.label))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                self.push(
                    format!("{inner}rcases {source} with {}", labels.join(" | ")),
                    step.line,
                    spot.clone(),
                );
                for (part, label) in parts.iter().zip(&labels) {
                    self.named.insert(label.clone(), vec![label.clone()]);
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    self.push(format!("{inner}· skip"), step.line, spot.clone());
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push(format!("{inner}  parley_side"), step.line, spot.clone());
                }
            }
            Method::BothDirections => {
                self.push(format!("{inner}constructor"), step.line, spot.clone());
                for part in &parts {
                    self.push(format!("{inner}· skip"), step.line, spot.clone());
                    if let Route::Declined(d) = self.open(step, *part, depth + 2) {
                        return Route::Declined(d);
                    }
                    let children: Vec<usize> = block
                        .children
                        .iter()
                        .copied()
                        .filter(|&c| self.rec.places[c].and_then(|pl| pl.part) == *part)
                        .collect();
                    if let Route::Declined(d) = self.steps(&children, depth + 2) {
                        return Route::Declined(d);
                    }
                    self.push(format!("{inner}  parley_side"), step.line, spot.clone());
                }
            }
            other => {
                return Route::no(format!(
                    "the method {} is not written in Lean yet",
                    other.as_str()
                ))
            }
        }
        self.writer.letters = kept;
        Route::Built(())
    }

    /// The lines that open a `proof` or `contradiction` block: each `let`
    /// introduces its letter, each `assume` its fact, and a `suppose` the
    /// opposite of the claim.
    fn open(&mut self, step: &Step, part: Option<usize>, depth: usize) -> Route<()> {
        let p = pad(depth);
        let spot = Self::step_spot(step);
        for o in step.openers.iter().filter(|o| o.part == part) {
            let label = line_name(&o.label);
            self.named.insert(o.label.clone(), vec![label.clone()]);
            let body = o.body(&self.thm.path);
            let nodes: Vec<Node> = body
                .sentences()
                .iter()
                .filter_map(|s| self.rec.page.get(s).cloned())
                .collect();
            match o.kind {
                Intro::Let => {
                    for node in &nodes {
                        let Some((letter, system)) = introduces(node) else {
                            return Route::no(
                                "a let that introduces no letter of a number system",
                            );
                        };
                        self.writer.letters.insert(
                            letter.clone(),
                            LetterType::Number(super::expr::letter_type(system)),
                        );
                        let letter = super::names::letter(&letter);
                        if system == super::expr::System::Positive {
                            self.push(
                                format!("{p}intro {letter} {label}"),
                                o.line,
                                spot.clone(),
                            );
                        } else {
                            self.push(
                                format!("{p}intro {letter}"),
                                o.line,
                                spot.clone(),
                            );
                        }
                    }
                }
                Intro::Assume => {
                    if let [node] = nodes.as_slice() {
                        self.trees.insert(
                            o.label.clone(),
                            vec![(node.clone(), label.clone())],
                        );
                    }
                    self.push(format!("{p}intro {label}"), o.line, spot.clone());
                }
                Intro::Suppose => {
                    let Some(node) = nodes.first() else {
                        return Route::no("a suppose the checker did not read");
                    };
                    let says = match self.writer.formula(node) {
                        Route::Built(s) => s,
                        Route::Declined(d) => return Route::Declined(d),
                    };
                    self.trees
                        .insert(o.label.clone(), vec![(node.clone(), label.clone())]);
                    // The block's claim denied, and the suppose line proved
                    // from that denial in the words the page chose for it.
                    self.push(format!("{p}by_contra hc_{label}"), o.line, spot.clone());
                    self.push(
                        format!(
                            "{p}have {label} : {} := by parley_suppose hc_{label}",
                            says.text
                        ),
                        o.line,
                        spot.clone(),
                    );
                }
            }
        }
        Route::Built(())
    }
}

/// A line whose proof runs over several lines, each line after the first
/// indented by `pad` as the first is.
fn indented(text: &str, pad: &str) -> String {
    text.replace('\n', &format!("\n{pad}"))
}

/// A sentence's parts, a conjunction taken apart by Lean's projections,
/// `H3.1` and `H3.2`, as the tree joins them.
fn conjuncts(node: &Node, proof: String, out: &mut Vec<super::algebra::Cited>) {
    let joined = matches!(
        node.notation(),
        crate::notations::CONJUNCTION | crate::notations::COMMA_CONJUNCTION
    );
    if let ([left, right], true) = (node.children.as_slice(), joined) {
        conjuncts(left, format!("{proof}.1"), out);
        conjuncts(right, format!("{proof}.2"), out);
        return;
    }
    out.push(super::algebra::Cited {
        node: node.clone(),
        proof,
    });
}

/// A claim proved from a term that gives it, as the claim's shape asks:
/// an equation by the ring identity between the two, an order by linear
/// arithmetic, anything else as it stands.
fn close(claim: &Node, term: &str) -> String {
    match claim.notation() {
        EQUALITY => format!("by linear_combination {term}"),
        ORDER => format!("by linarith [{term}]"),
        _ => format!("by simpa using {term}"),
    }
}
