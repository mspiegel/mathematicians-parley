//! A theorem and what it cites: scopes, references and items.

use std::borrow::Cow;

use super::*;

/// Which file's scope a theorem is read in.
pub type ScopeId = usize;

/// What a proof file holds outside its theorems: the definitions it writes
/// between them, and what it imports from other files, one item to a line.
///
/// A theorem sees the definitions written above it and every one its file
/// imports (`visible`). An imported one is read in the file that wrote it,
/// which is why each carries the scope it comes from.
#[derive(Clone, Debug)]
pub struct FileScope {
    pub path: String,
    pub defines: Vec<DefineLine>,
    /// Its defines of phrases (`define <name>: <phrase> means <meaning>`),
    /// which give no name a formula writes and are kept apart from those
    /// that do.
    pub phrases: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    /// The defines it imports from proof files.
    pub imports: Vec<Import>,
    /// The items it imports that a step cites by prefix and name.
    pub items: Vec<ItemImport>,
    /// The items it forbids itself to import.
    pub forbids: Vec<Forbid>,
    /// Each definition import, by its alias, and the define it names in the
    /// scope that wrote it (`link_definitions`).
    pub linked: IndexMap<String, (ScopeId, DefineLine)>,
    /// The library functions it imports, which are in scope in it and in no
    /// file that does not import them.
    pub functions: Vec<FunctionImport>,
    /// The line each of its theorems is written on, by the theorem's name:
    /// what a theorem of the file is stated over (`sorts::stated_over`).
    pub theorems: IndexMap<String, usize>,
    /// Every define a line of the file may use, each read once after the
    /// imports are linked (`read_visible`): those it imports, by alias, and
    /// those it writes, each below its own line (`visible`).
    pub visible: Vec<Visible>,
}

/// A define a line of a file may use: one the file writes, or one it
/// imports (`FileScope::visible`).
#[derive(Clone, Debug)]
pub struct Visible {
    /// The name a line uses: the define's own, or the alias an import gives
    /// it.
    pub name: String,
    pub define: DefineLine,
    /// The define read into its parts, once.
    pub parts: DefineParts,
    /// The scope whose file writes it, where it is read.
    pub scope: ScopeId,
    /// Whether the file imports it: then every line of the file may use it,
    /// and otherwise only the lines below it.
    pub imported: bool,
}

impl FileScope {
    pub fn new(path: &str) -> Self {
        FileScope {
            path: path.to_string(),
            defines: Vec::new(),
            phrases: Vec::new(),
            readings: IndexMap::new(),
            imports: Vec::new(),
            items: Vec::new(),
            forbids: Vec::new(),
            linked: IndexMap::new(),
            functions: Vec::new(),
            theorems: IndexMap::new(),
            visible: Vec::new(),
        }
    }

    /// The names of the library functions it imports.
    pub fn function_names(&self) -> IndexSet<String> {
        self.functions.iter().map(|f| f.name.clone()).collect()
    }

    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// What each name its citations write stands for: the items it imports
    /// and the library functions, which a line unfolding one cites.
    pub fn names(&self) -> Names {
        let mut imported: IndexMap<String, String> = IndexMap::new();
        for i in &self.items {
            imported.entry(i.alias.clone()).or_insert_with(|| i.full());
        }
        for f in &self.functions {
            imported
                .entry(f.name.clone())
                .or_insert_with(|| format!("{}/{}", f.module, f.name));
        }
        Names {
            module: self.module().to_string(),
            imported,
        }
    }

    /// The label the import writing a definition as `alias` carries, where it
    /// gives one.
    pub fn import_label(&self, alias: &str) -> Option<&str> {
        self.imports
            .iter()
            .find(|i| i.alias == alias)
            .and_then(|i| i.label.as_deref())
    }

    /// The define this file writes at file level under `name`.
    pub fn written(&self, name: &str) -> Option<&DefineLine> {
        self.defines.iter().find(|d| match define_parts(&d.text) {
            Built(said) => said.name() == Some(name),
            _ => false,
        })
    }
}

/// Every definition a line of the file of scope `id` at `line` may use: each
/// it imports, and each it writes above the line (`FileScope::visible`).
pub fn visible(scopes: &[FileScope], id: ScopeId, line: usize) -> Vec<&Visible> {
    scopes[id]
        .visible
        .iter()
        .filter(|v| v.imported || v.define.line < line)
        .collect()
}

/// A define a theorem may use, as the theorem uses it (`in_scope`).
#[derive(Clone, Debug)]
pub struct InScope<'s> {
    /// The name it gives: its own, or the alias an import gives it.
    pub name: String,
    /// The label a line of the theorem cites it by: its own, or the label on
    /// the import; None for an import that gives none, which no line cites.
    pub label: Option<String>,
    pub define: &'s DefineLine,
    /// The define read into its parts: once, for the file's and the
    /// imported (`FileScope::visible`), and here for the theorem's own.
    pub parts: Cow<'s, DefineParts>,
    /// Imported from another file, where it is read.
    pub imported: bool,
}

/// Every define the theorem `thm` may use: its own, each that reads, then
/// those its file writes above it and those it imports (`visible`). A
/// recursion of its own is listed once, under its first name.
pub fn in_scope<'s>(thm: &'s Theorem, scopes: &'s [FileScope]) -> Vec<InScope<'s>> {
    let own = thm
        .defines
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(parts) => {
                let name = parts.names().into_iter().next()?;
                Some(InScope {
                    name,
                    label: Some(d.label.clone()),
                    define: d,
                    parts: Cow::Owned(parts),
                    imported: false,
                })
            }
            Route::Declined(_) => None,
        });
    let scope = &scopes[thm.scope];
    let outside = visible(scopes, thm.scope, thm.line)
        .into_iter()
        .map(|v| InScope {
            name: v.name.clone(),
            label: match v.imported {
                true => scope.import_label(&v.name).map(String::from),
                false => Some(v.define.label.clone()),
            },
            define: &v.define,
            parts: Cow::Borrowed(&v.parts),
            imported: v.imported,
        });
    own.chain(outside).collect()
}

/// Reads each file's defines and the defines it imports once, into
/// `FileScope::visible`, after `link_definitions` has linked the imports:
/// the imports first, by alias, then the file's own in order. A define that
/// does not read is left out, as is a file-level recursion, which gives no
/// one name to be found by; the checker reports either.
pub fn read_visible(scopes: &mut [FileScope]) {
    for (id, scope) in scopes.iter_mut().enumerate() {
        let imported = scope.linked.iter().filter_map(|(alias, (src, d))| {
            match define_parts(&d.text) {
                Built(parts) => Some(Visible {
                    name: alias.clone(),
                    define: d.clone(),
                    parts,
                    scope: *src,
                    imported: true,
                }),
                Route::Declined(_) => None,
            }
        });
        let written =
            scope
                .defines
                .iter()
                .filter_map(|d| match define_parts(&d.text) {
                    Built(parts) => {
                        let name = parts.name()?.to_string();
                        Some(Visible {
                            name,
                            define: d.clone(),
                            parts,
                            scope: id,
                            imported: false,
                        })
                    }
                    Route::Declined(_) => None,
                });
        let visible: Vec<Visible> = imported.chain(written).collect();
        scope.visible = visible;
    }
}

/// One theorem of a proof file.
#[derive(Clone, Debug)]
pub struct Theorem {
    pub name: String,
    /// Whether its header says `mundane theorem`: a fact a proof takes for
    /// granted and cites `mun:`, as a mundane record is. Only a theorem of
    /// the standard library is marked so, since only the library holds
    /// what proofs reach for as known.
    pub mundane: bool,
    pub hypotheses: Vec<Hypothesis>,
    pub ranges: Vec<Range>,
    pub conclusion: String,
    /// The line of the `then`: a define above it is the statement's, and
    /// the statement is read with it.
    pub conclusion_line: usize,
    pub defines: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    pub steps: Vec<Step>,
    pub line: usize,
    pub path: String,
    /// Its `note`, where it says one.
    pub fields: IndexMap<String, String>,
    pub scope: ScopeId,
    /// What the names its file cites stand for.
    pub names: Arc<Names>,
}

impl Theorem {
    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// The `then` line's formula as written, with where.
    pub fn stated(&self) -> Written {
        Written::new(&self.conclusion, &self.path, self.conclusion_line)
    }

    pub fn qualified(&self) -> String {
        format!("{}/{}", self.module(), self.name)
    }

    /// Whether `line` of the theorem's file is one of its own: from its
    /// header to the last line anything in it is written on. A file's
    /// theorems never interleave, so no other theorem's line is among them.
    pub fn owns_line(&self, line: usize) -> bool {
        (self.line..=self.last_line()).contains(&line)
    }

    /// The last line anything in the theorem is written on.
    pub(super) fn last_line(&self) -> usize {
        let steps = self.steps.iter().flat_map(|s| {
            let just = &s.just;
            [s.line, just.line]
                .into_iter()
                .chain(s.requires.iter().map(|r| r.line))
                .chain(s.openers.iter().map(|o| o.line))
                .chain(s.parts.iter().map(|(_, l)| *l))
                .chain(just.chain.iter().map(|(_, l)| *l))
                .chain(just.rows.iter().map(|(_, l)| *l))
        });
        let heads = self
            .hypotheses
            .iter()
            .map(|h| h.line)
            .chain(self.defines.iter().map(|d| d.line));
        steps
            .chain(heads)
            .chain([self.line, self.conclusion_line])
            .max()
            .unwrap_or(self.line)
    }

    /// Each define by recursion above the `then`, which the statement is
    /// read with, and its line. One that does not read is left out, and is
    /// `check_recursions`'s to report.
    pub fn stated_recursions(&self) -> Vec<(usize, super::super::define::Recursion)> {
        self.defines
            .iter()
            .filter(|d| d.line < self.conclusion_line)
            .filter_map(|d| match define_parts(&d.text) {
                Built(DefineParts::Recursion(r)) => Some((d.line, r)),
                _ => None,
            })
            .collect()
    }

    /// Each let that says what kind of number its name is, read
    /// (`DefineLine::kinded`).
    pub fn kinded(&self, members: &IndexMap<String, String>) -> Checked<Vec<Kinded>> {
        let mut out = Vec::new();
        for d in &self.defines {
            if let Some(k) = d.kinded(&self.path, members)? {
                out.push(k);
            }
        }
        Ok(out)
    }

    /// The step a let's reason is read under, as a requires line is read
    /// under its step (`requires_as_step`): the first step below the let,
    /// whose scope the let stands in. None for a let below every step.
    pub fn step_after(&self, line: usize) -> Option<&Step> {
        self.steps.iter().find(|s| s.line > line)
    }

    /// The requires lines written under the lets' reasons (`Reason::requires`).
    pub fn let_requires(&self) -> impl Iterator<Item = &Requires> {
        self.defines
            .iter()
            .filter_map(|d| d.reason.as_ref())
            .flat_map(|r| &r.requires)
    }
}

/// A step number or label a theorem's text writes, and where: `cite`'s
/// place is in the logical line that starts on `line` (`lines::read_lines`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reference {
    pub cite: Cite,
    pub line: usize,
}

/// Every step number and label a theorem's text writes as one, each where
/// the reader read it: a step's own number where its claim opens, every
/// line and label a justification, a requires line, a let's reason, a
/// chain line or a row cites, and the step an induction hypothesis names.
/// A number anywhere else, in a formula or a value, is none of these.
pub fn references(thm: &Theorem) -> Vec<Reference> {
    let mut out = Vec::new();
    for r in thm.let_requires() {
        cited_by(&mut out, &r.by, r.line);
    }
    for d in &thm.defines {
        if let Some(reason) = &d.reason {
            cited_by(&mut out, &reason.by, reason.line);
        }
    }
    for step in &thm.steps {
        // The theorem's own step has no number written on the page.
        if let Some(number) = step.number.number() {
            out.push(Reference {
                cite: Cite {
                    cited: Cited::Line(number.clone()),
                    at: 0,
                    len: fmt(number).len(),
                },
                line: step.line,
            });
        }
        out.extend(step.just.cited.iter().map(|c| Reference {
            cite: c.clone(),
            line: step.just.line,
        }));
        for r in &step.requires {
            cited_by(&mut out, &r.by, r.line);
        }
        for opener in step.openers.iter().filter(|o| o.is_hypothesis) {
            // `the theorem is true for k` names no step.
            if let Some(step) =
                skeleton::induction_hypothesis(&opener.text).and_then(|s| s.step)
            {
                let at = skeleton::offset(&opener.text, step);
                out.push(Reference {
                    cite: skeleton::cite_at(step, at),
                    line: opener.line,
                });
            }
        }
        if let Some(Ok(chain)) = chain(&step.just, &thm.path) {
            for link in &chain.lines {
                if let Some(cited) = link.cited() {
                    out.push(Reference {
                        cite: skeleton::cite_at(cited, link.cite_at),
                        line: link.line,
                    });
                }
                if let Some(r) = &link.reason {
                    cited_by(&mut out, &r.by, link.line);
                }
            }
        }
        if let Some(Ok(rows)) = substitute_rows(&step.just, &thm.path) {
            for row in &rows {
                if skeleton::is_ref(&row.cite) {
                    out.push(Reference {
                        cite: skeleton::cite_at(&row.cite, row.cite_at),
                        line: row.line,
                    });
                }
                if let Some(r) = &row.reason {
                    cited_by(&mut out, &r.by, row.line);
                }
            }
        }
        if let Some(Ok(rows)) = rows(&step.just, &thm.path) {
            for row in &rows {
                if let (RowReason::Cited(cited), Some(at)) = (&row.reason, row.cited_at)
                {
                    out.push(Reference {
                        cite: skeleton::cite_at(cited, at),
                        line: row.line,
                    });
                }
            }
        }
    }
    out
}

/// What a reason read on the logical line starting on `line` cites, put in
/// `out`; nothing for a reason that did not read.
pub(super) fn cited_by(
    out: &mut Vec<Reference>,
    by: &Checked<Justification>,
    line: usize,
) {
    if let Ok(just) = by {
        out.extend(just.cited.iter().map(|c| Reference {
            cite: c.clone(),
            line,
        }));
    }
}

/// Everything a theorem's lines say, as one run of text: the statement, its
/// defines, and every step's claim, openers, requires lines and
/// justification.
pub fn written_text(thm: &Theorem) -> String {
    let mut parts: Vec<&str> = thm.hypotheses.iter().map(|h| h.text.as_str()).collect();
    parts.push(&thm.conclusion);
    parts.extend(thm.defines.iter().map(|d| d.text.as_str()));
    parts.extend(
        thm.defines
            .iter()
            .filter_map(|d| d.reason.as_ref().map(|r| r.how.as_str())),
    );
    parts.extend(thm.let_requires().map(|r| r.fact.text()));
    for step in &thm.steps {
        parts.push(step.claim.text());
        parts.extend(step.openers.iter().map(|o| o.text.as_str()));
        parts.extend(step.requires.iter().map(|r| r.fact.text()));
        parts.push(&step.just.text);
        parts.extend(step.just.chain.iter().map(|(t, _)| t.as_str()));
    }
    parts.join(" ")
}

/// Where a chain's first line puts its relation: the first time the symbol
/// stands outside every bracket; None where it stands only inside.
///
/// A sum binds its index with the same `=` a chain relates by, so
/// `x·(Σ(k = 0 to m) t(k)) = …` has an `=` inside the sum before the one the
/// chain means.
pub fn outermost(words: &[&str], relation: &str) -> Option<usize> {
    let mut depth: i64 = 0;
    for (at, word) in words.iter().enumerate() {
        if depth == 0 && *word == relation {
            return Some(at);
        }
        let opens = word.chars().filter(|c| "({[".contains(*c)).count() as i64;
        let closes = word.chars().filter(|c| ")}]".contains(*c)).count() as i64;
        depth += opens - closes;
    }
    None
}

pub(super) fn parse_justification(
    path: &str,
    line: &Line,
    labels: &skeleton::Labels,
    names: &Arc<Names>,
) -> Checked<Justification> {
    // A malformed justification is reported by the checker, not raised here
    // (`Justification::unproduced`): one bad line must not cost the reader
    // every later line in the file.
    let slots = skeleton::cut(&line.text, path, line.no, labels)?;
    Ok(Justification::of(slots, line.no, names))
}

/// The labels a justification line of `thm` may cite a define by: the
/// file's defines, the theorem's, and the labels the file's imports give,
/// each once.
pub(super) fn justification_labels(
    scope: &FileScope,
    thm: &Theorem,
) -> skeleton::Labels {
    let mut defines: Vec<String> = Vec::new();
    for d in scope.defines.iter().chain(thm.defines.iter()) {
        if !defines.contains(&d.label) {
            defines.push(d.label.clone());
        }
    }
    for label in scope.imports.iter().filter_map(|i| i.label.as_ref()) {
        if !defines.contains(label) {
            defines.push(label.clone());
        }
    }
    skeleton::Labels {
        defines,
        phrases: phrase_labels(scope),
    }
}

/// The label of each define of a phrase the file has written so far, with
/// the item a line citing it cites: `def:` and its name.
pub(super) fn phrase_labels(scope: &FileScope) -> Vec<skeleton::PhraseLabel> {
    scope
        .phrases
        .iter()
        .filter_map(|d| match define_parts(&d.text) {
            Built(DefineParts::Phrase(p)) => Some(skeleton::PhraseLabel {
                label: d.label.clone(),
                kind: ItemKind::Definition,
                name: p.name,
            }),
            _ => None,
        })
        .collect()
}

/// Every item a theorem's steps cite, by full name, with its line.
pub fn cited_items(thm: &Theorem) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let just = &step.just;
        if let Some(item) = just.cited_item() {
            out.push((just.item(&item), just.line));
        }
        if let Some(target) = &just.target {
            if item_kind(target).is_some() {
                out.push((just.item(target), just.line));
            }
        }
        for req in step.requires.iter().chain(&chain_reasons(just, &thm.path)) {
            if let Some((cited, _)) = req.cited_item() {
                out.push((just.item(&cited), req.line));
            }
        }
    }
    // A let's reason is written as a requires line's is.
    for reason in thm.defines.iter().filter_map(|d| d.reason.as_ref()) {
        if let Some((cited, _)) = reason.cited_item() {
            out.push((thm.names.full(&cited), reason.line));
        }
    }
    for req in thm.let_requires() {
        if let Some((cited, _)) = req.cited_item() {
            out.push((thm.names.full(&cited), req.line));
        }
    }
    out
}
