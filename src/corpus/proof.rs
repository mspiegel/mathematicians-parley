//! Proof skeletons: the `.proof` files.

use std::fmt;

use indexmap::{IndexMap, IndexSet};

use super::define::{define_parts, DefineParts};
use super::lines::{read_lines, Line};
use super::{cited_name, full, module_of, resolve};
use crate::outcome::{Built, Checked, Problem};
use crate::regex;
use crate::text::{prefix, repr};

/// How a line introduces what it introduces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Intro {
    Let,
    Assume,
    Suppose,
}

impl Intro {
    pub fn parse(word: &str) -> Option<Intro> {
        Some(match word {
            "let" => Intro::Let,
            "assume" => Intro::Assume,
            "suppose" => Intro::Suppose,
            _ => return None,
        })
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Intro::Let => "let",
            Intro::Assume => "assume",
            Intro::Suppose => "suppose",
        }
    }
}

impl fmt::Display for Intro {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A `let` or `assume` line of a statement.
///
/// In a record the text is what follows the keyword; in a proof file it is
/// the whole line, keyword and label included, as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    pub kind: Intro,
    pub text: String,
    pub label: Option<String>,
    pub line: usize,
}

/// A statement's `ε, δ range over ℝ`: the set each of those letters belongs
/// to wherever a quantifier in the theorem writes a bound in place of the
/// set, "for all ε > 0". It introduces nothing and is not a hypothesis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Range {
    pub names: Vec<String>,
    pub set: String,
    /// The line as written, for a restatement to copy.
    pub text: String,
    pub line: usize,
}

regex!(
    RANGE_LINE,
    r"^([A-Za-zα-ω][₀-₉′]*(?:\s*,\s*[A-Za-zα-ω][₀-₉′]*)*)\s+ranges?\s+over\s+(\S.*?)\s*$"
);

impl Range {
    /// The line read as a range, or None where it is some other line.
    pub fn read(text: &str, line: usize) -> Option<Range> {
        let m = RANGE_LINE.captures(text)?;
        Some(Range {
            names: m[1].split(',').map(|n| str::trim(n).to_string()).collect(),
            set: m[2].to_string(),
            text: text.to_string(),
            line,
        })
    }
}

/// A line opening a block: `suppose`, `let` or `assume`, with its label and
/// the part of the block it opens, where the block has parts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Opener {
    pub kind: Intro,
    pub text: String,
    pub label: String,
    pub line: usize,
    pub part: Option<usize>,
}

/// A `define` line as written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DefineLine {
    pub text: String,
    pub label: String,
    pub line: usize,
}

/// An `import definition` line.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub alias: String,
    pub line: usize,
    pub label: String,
}

/// An `import definition stdlib/<file>/<name>` line: a library function the
/// file applies, by its name, from the library file that declares it. It
/// carries no label, since nothing cites a function, and no `as`, since the
/// library's name for it is the one every file writes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionImport {
    pub module: String,
    pub name: String,
    pub line: usize,
}

/// A `requires` line: the fact, and how it is justified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Requires {
    pub fact: String,
    pub how: String,
    pub line: usize,
}

/// A step's number, as the text writes it: 3.1.2.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StepNo(pub Vec<u32>);

impl StepNo {
    pub fn parent(&self) -> StepNo {
        StepNo(self.0[..self.0.len() - 1].to_vec())
    }

    pub fn prefix(&self, k: usize) -> StepNo {
        StepNo(self.0[..k.min(self.0.len())].to_vec())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn last(&self) -> u32 {
        self.0[self.0.len() - 1]
    }

    /// Parsed from a reference such as `3.1`.
    pub fn parse(text: &str) -> StepNo {
        StepNo(text.split('.').map(|x| x.parse().unwrap_or(0)).collect())
    }
}

impl fmt::Display for StepNo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, n) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str(".")?;
            }
            write!(f, "{n}")?;
        }
        Ok(())
    }
}

/// A step number written as the text writes it.
pub fn fmt(number: &StepNo) -> String {
    number.to_string()
}

/// Whether a citation names a definition or a theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ItemKind {
    Def,
    Thm,
}

impl ItemKind {
    pub fn prefix(self) -> &'static str {
        match self {
            ItemKind::Def => "def",
            ItemKind::Thm => "thm",
        }
    }

    /// The kind of record a citation of this kind names.
    pub fn record_kind(self) -> &'static str {
        match self {
            ItemKind::Def => "definition",
            ItemKind::Thm => "theorem",
        }
    }
}

/// The methods a justification may open with, in the order a line is tried
/// against them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Method {
    Obtain,
    Exhibit,
    Substitute,
    Instantiate,
    Algebra,
    Arithmetic,
    Inequalities,
    Membership,
    Join,
    Contradiction,
    Fix,
    Induction,
    Cases,
    Calculation,
}

pub const METHODS: [Method; 14] = [
    Method::Obtain,
    Method::Exhibit,
    Method::Substitute,
    Method::Instantiate,
    Method::Algebra,
    Method::Arithmetic,
    Method::Inequalities,
    Method::Membership,
    Method::Join,
    Method::Contradiction,
    Method::Fix,
    Method::Induction,
    Method::Cases,
    Method::Calculation,
];

impl Method {
    pub fn as_str(self) -> &'static str {
        match self {
            Method::Obtain => "obtain",
            Method::Exhibit => "exhibit",
            Method::Substitute => "substitute",
            Method::Instantiate => "instantiate",
            Method::Algebra => "algebra",
            Method::Arithmetic => "arithmetic",
            Method::Inequalities => "inequalities",
            Method::Membership => "membership",
            Method::Join => "join",
            Method::Contradiction => "contradiction",
            Method::Fix => "fix",
            Method::Induction => "induction",
            Method::Cases => "cases",
            Method::Calculation => "calculation",
        }
    }

    /// Whether this method opens a block of steps.
    pub fn takes_block(self) -> bool {
        matches!(
            self,
            Method::Contradiction
                | Method::Fix
                | Method::Induction
                | Method::Cases
                | Method::Calculation
        )
    }
}

/// Whether a line opens a justification: one of the heads `GRAMMAR.md`
/// lists, `def:`, `thm:` and the methods, by the text it starts with.
pub fn starts_with_head(text: &str) -> bool {
    text.starts_with("def:")
        || text.starts_with("thm:")
        || METHODS.iter().any(|m| text.starts_with(m.as_str()))
}

/// What a justification opens with.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    /// A definition or theorem, with the name as the citation spells it.
    Item {
        kind: ItemKind,
        cited: String,
    },
    Method(Method),
    /// A define, cited by its label.
    Define,
}

impl Head {
    pub fn is_item(&self) -> bool {
        matches!(self, Head::Item { .. })
    }

    pub fn is(&self, method: Method) -> bool {
        *self == Head::Method(method)
    }

    pub fn method(&self) -> Option<Method> {
        match self {
            Head::Method(m) => Some(*m),
            _ => None,
        }
    }

    /// Whether this head opens a block of steps.
    pub fn takes_block(&self) -> bool {
        self.method().is_some_and(Method::takes_block)
    }
}

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Head::Item { kind, cited } => write!(f, "{}:{cited}", kind.prefix()),
            Head::Method(m) => f.write_str(m.as_str()),
            Head::Define => f.write_str("define"),
        }
    }
}

/// A step's justification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Justification {
    pub head: Head,
    pub text: String,
    pub line: usize,
    /// Everything cited, in order.
    pub refs: Vec<String>,
    /// An instantiate's `in …`.
    pub target: Option<String>,
    pub instantiations: Vec<String>,
    /// Each line of a calculation's chain, with the line it is on.
    pub chain: Vec<(String, usize)>,
    /// A `from` entry that is neither a line nor a label.
    pub bad_ref: Option<String>,
    /// The module of the file it is written in, which a bare name means.
    pub module: String,
    /// The define's label, where the head is a define.
    pub defined: Option<String>,
}

impl Justification {
    /// The full name a citation written in this justification's file means.
    pub fn item(&self, cited: &str) -> String {
        resolve(cited_name(cited), &self.module)
    }
}

/// One numbered step of a proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    pub number: StepNo,
    pub claim: Vec<String>,
    pub just: Justification,
    pub requires: Vec<Requires>,
    /// The part markers of the block it owns, with their lines.
    pub parts: Vec<(String, usize)>,
    pub openers: Vec<Opener>,
    pub line: usize,
    /// Which part of its parent's block this step sits in.
    pub part: Option<usize>,
    /// What the block it opens does, with the line it is said on.
    pub note: Option<(String, usize)>,
    /// What each part of its block does, by the part's index.
    pub part_notes: IndexMap<usize, (String, usize)>,
}

impl Step {
    pub fn claim_text(&self) -> String {
        self.claim.join(" ")
    }
}

/// Which file's scope a theorem is read in.
pub type ScopeId = usize;

/// What a proof file holds outside its theorems: the definitions it writes
/// between them, the definitions it imports from other files, and the proof
/// files it imports.
///
/// A theorem sees the definitions written above it and every one its file
/// imports (`visible`). An imported one is read in the file that wrote it,
/// which is why each carries the scope it comes from.
#[derive(Clone, Debug)]
pub struct FileScope {
    pub path: String,
    pub defines: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    pub imports: Vec<Import>,
    /// The proof files it imports, with their lines.
    pub proof_imports: Vec<(String, usize)>,
    /// Each definition import, by its alias, and the define it names in the
    /// scope that wrote it (`link_definitions`).
    pub linked: IndexMap<String, (ScopeId, DefineLine)>,
    /// The library functions it imports, which are in scope in it and in no
    /// file that does not import them.
    pub functions: Vec<FunctionImport>,
}

impl FileScope {
    pub fn new(path: &str) -> Self {
        FileScope {
            path: path.to_string(),
            defines: Vec::new(),
            readings: IndexMap::new(),
            imports: Vec::new(),
            proof_imports: Vec::new(),
            linked: IndexMap::new(),
            functions: Vec::new(),
        }
    }

    /// The names of the library functions it imports.
    pub fn function_names(&self) -> IndexSet<String> {
        self.functions.iter().map(|f| f.name.clone()).collect()
    }

    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    /// The label the import writing a definition as `alias` carries.
    pub fn import_label(&self, alias: &str) -> Option<&str> {
        self.imports
            .iter()
            .find(|i| i.alias == alias)
            .map(|i| i.label.as_str())
    }

    /// The define this file writes at file level under `name`.
    pub fn written(&self, name: &str) -> Option<&DefineLine> {
        self.defines.iter().find(|d| match define_parts(&d.text) {
            Built(said) => said.name() == Some(name),
            _ => false,
        })
    }
}

/// (name, define, the scope it is read in) for every definition a line of
/// the file of scope `id` at `line` may use.
pub fn visible(
    scopes: &[FileScope],
    id: ScopeId,
    line: usize,
) -> Vec<(String, DefineLine, ScopeId)> {
    let scope = &scopes[id];
    let mut out: Vec<(String, DefineLine, ScopeId)> = scope
        .linked
        .iter()
        .map(|(alias, (src, d))| (alias.clone(), d.clone(), *src))
        .collect();
    for d in &scope.defines {
        if d.line < line {
            if let Built(said) = define_parts(&d.text) {
                // A recursion is never written at file level, and has no
                // one name to be found by.
                if let Some(name) = said.name() {
                    out.push((name.to_string(), d.clone(), id));
                }
            }
        }
    }
    out
}

/// One theorem of a proof file.
#[derive(Clone, Debug)]
pub struct Theorem {
    pub name: String,
    pub hypotheses: Vec<Hypothesis>,
    pub ranges: Vec<Range>,
    pub conclusion: String,
    pub defines: Vec<DefineLine>,
    /// A define's label, and what its `reads` line says.
    pub readings: IndexMap<String, (String, usize)>,
    pub steps: Vec<Step>,
    pub line: usize,
    pub path: String,
    /// `metamath` and `note`, where it says them.
    pub fields: IndexMap<String, String>,
    pub scope: ScopeId,
}

impl Theorem {
    pub fn module(&self) -> &str {
        module_of(&self.path)
    }

    pub fn qualified(&self) -> String {
        format!("{}/{}", self.module(), self.name)
    }
}

/// Everything a theorem's lines say, as one run of text: the statement, its
/// defines, and every step's claim, openers, requires lines and
/// justification.
pub fn written_text(thm: &Theorem) -> String {
    let mut parts: Vec<&str> = thm.hypotheses.iter().map(|h| h.text.as_str()).collect();
    parts.push(&thm.conclusion);
    parts.extend(thm.defines.iter().map(|d| d.text.as_str()));
    for step in &thm.steps {
        parts.extend(step.claim.iter().map(String::as_str));
        parts.extend(step.openers.iter().map(|o| o.text.as_str()));
        parts.extend(step.requires.iter().map(|r| r.fact.as_str()));
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

// A justification that cites a define: its label, and what says which case.
regex!(DEFINE_CITED, r"^([A-Z]+[0-9]*)(?:\s*,\s*from\s+\S.*)?$");
regex!(FROM_LINE, format!(r"\bfrom\s+line\s+({})\b", super::NUMBER));
regex!(FROM_ANY, r"\bfrom\s+(.*)$");
regex!(REF_RE, super::REF);

/// References named by a justification, read from their syntactic position
/// and never by scanning for digits, and the first `from` entry that is no
/// reference. A step's justification and a requires line's are the same
/// production, and both are read here.
pub fn references(text: &str) -> (Vec<String>, Option<String>) {
    let mut out = Vec::new();
    if let Some(m) = FROM_LINE.captures(text) {
        out.push(m[1].to_string());
    } else if let Some(m) = FROM_ANY.captures(text) {
        for tok in m[1].split(',') {
            let tok = str::trim(tok);
            if full(&REF_RE, tok) {
                out.push(tok.to_string());
            } else if !tok.is_empty() {
                return (out, Some(tok.to_string()));
            }
        }
    }
    (out, None)
}

/// The define label a justification line cites as its head.
///
/// A define is cited by its label, alone or with `from`: `D2, from 4.1`.
/// Only a whole line of that shape, and only a label a define in scope
/// carries, since a claim may begin with a capital as a label does.
pub fn cites_define(text: &str, defines: &[String]) -> Option<String> {
    let m = DEFINE_CITED.captures(text)?;
    let label = &m[1];
    defines
        .iter()
        .any(|d| d == label)
        .then(|| label.to_string())
}

regex!(ITEM_HEAD, format!(r"^(def|thm):({})", super::CITED));
regex!(
    SUBSTITUTE_SOURCE,
    format!(
        r"^substitute\s.*\((?:line\s+({})|({}))\)(?:\s+into\s+\S.*?)?\s*$",
        super::NUMBER,
        super::LABEL
    )
);
regex!(
    INTO,
    format!(
        r"\binto\s+(?:line\s+({})|({}))\b",
        super::NUMBER,
        super::LABEL
    )
);
regex!(
    IN_TARGET,
    format!(
        r"\bin\s+(?:line\s+({})|(def:{})|({}))\b",
        super::NUMBER,
        super::CITED,
        super::LABEL
    )
);
regex!(INSTANTIATED, r"([^\s,]+)\s*:=");

fn parse_justification(
    path: &str,
    line: &Line,
    defines: &[String],
) -> Checked<Justification> {
    let text = &line.text;
    let module = module_of(path).to_string();
    let has_head = starts_with_head(text);
    let label = if has_head {
        None
    } else {
        cites_define(text, defines)
    };
    if let Some(label) = label {
        let (mut refs, bad_ref) = references(text);
        refs.insert(0, label.clone());
        return Ok(Justification {
            head: Head::Define,
            text: text.clone(),
            line: line.no,
            refs,
            target: None,
            instantiations: Vec::new(),
            chain: Vec::new(),
            bad_ref,
            module,
            defined: Some(label),
        });
    }
    if !has_head {
        return Err(Problem::new(
            path,
            line.no,
            format!("no justification head in {}", repr(prefix(text, 40))),
        ));
    }
    let head = if text.starts_with("def:") || text.starts_with("thm:") {
        match ITEM_HEAD.captures(text) {
            Some(m) => Head::Item {
                kind: if &m[1] == "def" {
                    ItemKind::Def
                } else {
                    ItemKind::Thm
                },
                cited: m[2].to_string(),
            },
            // `def:` with no name after it cites nothing, which is a defect
            // in the line.
            None => {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("no justification head in {}", repr(prefix(text, 40))),
                ))
            }
        }
    } else {
        let method = METHODS
            .iter()
            .find(|m| text.starts_with(m.as_str()))
            .copied()
            .unwrap();
        Head::Method(method)
    };
    // A malformed justification is reported by the checker, not raised here:
    // one bad line must not cost the reader every later line in the file.
    let (mut refs, bad_ref) = references(text);
    // A substitute names its equation's source in brackets after it. Only
    // there: M(C) on any other line is a function applied to C, not a
    // citation of a label C.
    if let Some(src) = SUBSTITUTE_SOURCE.captures(text) {
        let got = src.get(1).or(src.get(2)).map(|m| m.as_str().to_string());
        if let Some(got) = got {
            refs.push(got);
        }
    }
    for dest in INTO.captures_iter(text) {
        let got = dest.get(1).or(dest.get(2)).unwrap();
        refs.push(got.as_str().to_string());
    }
    let mut target = None;
    if let Some(m) = IN_TARGET.captures(text) {
        let got = m
            .get(1)
            .or(m.get(2))
            .or(m.get(3))
            .map(|g| g.as_str().to_string());
        if let Some(t) = &got {
            if !t.starts_with("def:") {
                refs.push(t.clone());
            }
        }
        target = got;
    }
    if head.is(Method::Join) {
        for tok in text["join".len()..].split(',') {
            let tok = str::trim(tok);
            if full(&REF_RE, tok) {
                refs.push(tok.to_string());
            }
        }
    }
    let instantiations = INSTANTIATED
        .captures_iter(text)
        .map(|c| c[1].to_string())
        .collect();
    Ok(Justification {
        head,
        text: text.clone(),
        line: line.no,
        refs,
        target,
        instantiations,
        chain: Vec::new(),
        bad_ref,
        module,
        defined: None,
    })
}

regex!(STEP_RE, format!(r"^({})\.\s+(.*)$", super::NUMBER));
// The item an obtain takes its object from.
regex!(
    OBTAINED_FROM,
    format!(r"^obtain\s+[^:]+:\s*((?:def|thm):{})", super::CITED)
);
// A requires line's justification, where it cites an item.
regex!(REQUIRES_ITEM_RE, format!(r"^(def|thm):({})", super::CITED));

/// A requires line's citation of an item: the whole `def:x` or `thm:x`, and
/// its prefix.
pub fn requires_item(how: &str) -> Option<(String, ItemKind)> {
    let m = REQUIRES_ITEM_RE.captures(how)?;
    let kind = if &m[1] == "def" {
        ItemKind::Def
    } else {
        ItemKind::Thm
    };
    Some((m[0].to_string(), kind))
}

/// The item a step's justification cites, as `def:x` or `thm:x`.
///
/// Either the head is the item, or the step obtains from one: `obtain c:
/// thm:stdlib/calculus/completeness S := S, from 5, 2, 7` owes the item's
/// hypotheses as surely as a step headed by it does.
pub fn cited_item(just: &Justification) -> Option<String> {
    if just.head.is_item() {
        return Some(just.head.to_string());
    }
    if just.head.is(Method::Obtain) {
        return OBTAINED_FROM.captures(&just.text).map(|m| m[1].to_string());
    }
    None
}

/// Every item a theorem's steps cite, by full name, with its line.
pub fn cited_items(thm: &Theorem) -> Vec<(String, usize)> {
    let mut out = Vec::new();
    for step in &thm.steps {
        let just = &step.just;
        if let Some(item) = cited_item(just) {
            out.push((just.item(&item), just.line));
        }
        if let Some(target) = &just.target {
            if target.starts_with("def:") {
                out.push((just.item(target), just.line));
            }
        }
        for req in &step.requires {
            if let Some((cited, _)) = requires_item(&req.how) {
                out.push((just.item(&cited), req.line));
            }
        }
    }
    out
}

// A definition is imported by the name a formula writes, which is not an
// item's name: a proof's define is one letter, perhaps with a subscript or a
// prime, and a library function's name may be a Greek letter, as σ. So the
// last part of the path takes those, where a module's parts are item names.
const DEFINED_NAME: &str = r"[A-Za-zα-ω][A-Za-zα-ω0-9₀-₉′-]*";

regex!(
    IMPORTED,
    format!(
        r"^import\s+(?:(?P<proof>proof)\s+(?P<module>{c})|(?P<definition>definition)\s+(?P<full>(?:{n}/)*{d})(?:\s+as\s+(?P<alias>[^\s()]+))?(?:\s+\((?P<label>{l})\))?)\s*$",
        c = super::CITED,
        n = super::NAME,
        d = DEFINED_NAME,
        l = super::LABEL
    )
);

enum Imported {
    Proof(String, usize),
    Definition(Import),
    Function(FunctionImport),
}

/// One `import` line.
///
/// Every import says what it brings in: `import proof` a proof file, whose
/// theorems the file may then cite by their full names, and `import
/// definition` one definition, which the file then writes by its name, or by
/// the name after `as`. Said on the line, a file and a definition never have
/// to be told apart by what happens to exist.
fn importing(path: &str, no: usize, text: &str) -> Checked<Imported> {
    let Some(m) = IMPORTED.captures(str::trim(text)) else {
        return Err(Problem::new(
            path,
            no,
            "an import says `import proof <file>` or `import definition <file>/<name>`",
        ));
    };
    if m.name("proof").is_some() {
        return Ok(Imported::Proof(m["module"].to_string(), no));
    }
    let whole = &m["full"];
    let (module, name) = match whole.rfind('/') {
        Some(at) => (&whole[..at], &whole[at + 1..]),
        None => ("", whole),
    };
    if module.is_empty() {
        return Err(Problem::new(
            path,
            no,
            format!("import definition {whole} names no file"),
        ));
    }
    // A library function is imported by the name the library gives it, and
    // nothing cites it by a label.
    if super::in_stdlib(whole) {
        if m.name("label").is_some() || m.name("alias").is_some() {
            return Err(Problem::new(
                path,
                no,
                format!(
                    "import definition {whole}: a library function is imported by its name alone, with no `as` and no label"
                ),
            ));
        }
        return Ok(Imported::Function(FunctionImport {
            module: module.to_string(),
            name: name.to_string(),
            line: no,
        }));
    }
    // A definition a file imports is cited by its label, as one it defines
    // is: a calculation link writing S(k + 1) out cites the equation.
    let Some(label) = m.name("label") else {
        return Err(Problem::new(
            path,
            no,
            format!("import definition {whole} carries no label"),
        ));
    };
    let alias = m.name("alias").map_or(name, |a| a.as_str());
    if !super::define::is_one_name(alias) {
        return Err(Problem::new(
            path,
            no,
            format!(
                "a definition is imported under one letter, perhaps with a subscript or a prime, and {} is not one",
                repr(alias)
            ),
        ));
    }
    Ok(Imported::Definition(Import {
        module: module.to_string(),
        name: name.to_string(),
        alias: alias.to_string(),
        line: no,
        label: label.as_str().to_string(),
    }))
}

regex!(CHAIN_TAIL, format!(r"(\barithmetic|{})$", super::REF));

/// A chain line's citation, read from the right end of the line rather than
/// from the whitespace that happens to separate it.
///
/// A link relating numerals alone may name `arithmetic` in place of a line,
/// and then it cites nothing: the fact is worked out where it stands.
fn chain_citation(path: &str, line: &Line) -> Checked<Vec<String>> {
    let Some(m) = CHAIN_TAIL.captures(&line.text) else {
        return Err(Problem::new(
            path,
            line.no,
            "chain line names no line or label; a chain only joins, so every line must cite a numbered step, a label, or `arithmetic` for a link of numerals alone",
        ));
    };
    if &m[1] == "arithmetic" {
        Ok(Vec::new())
    } else {
        Ok(vec![m[1].to_string()])
    }
}

/// A step being read, whose justification may not have arrived yet.
struct DraftStep {
    step: Step,
    has_just: bool,
}

struct DraftTheorem {
    thm: Theorem,
    steps: Vec<DraftStep>,
}

const THEOREM_FIELDS: [&str; 2] = ["metamath", "note"];

regex!(THEOREM_NAME, super::NAME);
regex!(LABEL_END, r"\(([A-Z]+[0-9]*)\)$");

fn label_at_end(text: &str) -> Option<String> {
    LABEL_END.captures(text).map(|c| c[1].to_string())
}

fn placeholder_justification() -> Justification {
    Justification {
        head: Head::Define,
        text: String::new(),
        line: 0,
        refs: Vec::new(),
        target: None,
        instantiations: Vec::new(),
        chain: Vec::new(),
        bad_ref: None,
        module: String::new(),
        defined: None,
    }
}

/// The theorems of a proof file, and what the file holds outside them.
/// Structure comes from the step number; indentation is presentation and is
/// not consulted.
pub fn parse_proof(
    path: &str,
    text: &str,
    scope_id: ScopeId,
) -> Checked<(FileScope, Vec<Theorem>)> {
    let mut theorems: Vec<Theorem> = Vec::new();
    let mut scope = FileScope::new(path);
    let mut thm: Option<DraftTheorem> = None;
    // Whether the step being read still waits for its justification: the
    // index of the draft step in the theorem being read.
    let mut step: Option<usize> = None;
    let mut just_defined: Option<DefineLine> = None;
    // Between a theorem line and its statement a theorem may carry fields,
    // and a line there that opens no field continues the one above it.
    let mut header = false;
    let mut last_field: Option<(String, usize)> = None;
    // A part marker or a block opener appears before the sub-steps it governs,
    // so it is held until the next step arrives and is then attached to that
    // step's parent, which is the step that owns the block.
    // Each held marker, its line, and the note said under it.
    type Said = (String, usize);
    let mut pending_markers: Vec<(String, usize, Option<Said>)> = Vec::new();
    let mut pending_openers: Vec<(Intro, String, String, usize)> = Vec::new();
    let mut part_no: IndexMap<StepNo, usize> = IndexMap::new();
    let mut by_number: IndexMap<StepNo, usize> = IndexMap::new();

    fn close_step(
        path: &str,
        thm: &Option<DraftTheorem>,
        step: &mut Option<usize>,
    ) -> Checked<()> {
        if let (Some(at), Some(t)) = (*step, thm.as_ref()) {
            let draft = &t.steps[at];
            if !draft.has_just {
                return Err(Problem::new(
                    path,
                    draft.step.line,
                    format!("step {} has no justification", draft.step.number),
                ));
            }
        }
        *step = None;
        Ok(())
    }

    /// A define after a theorem's last step is the file's, for the theorems
    /// below it: that theorem could never use it.
    fn settle(
        thm: Option<DraftTheorem>,
        scope: &mut FileScope,
        theorems: &mut Vec<Theorem>,
    ) {
        let Some(mut draft) = thm else { return };
        let last = draft
            .steps
            .iter()
            .map(|s| s.step.line)
            .max()
            .unwrap_or(draft.thm.line);
        let moved: Vec<DefineLine> = draft
            .thm
            .defines
            .iter()
            .filter(|d| d.line > last)
            .cloned()
            .collect();
        for d in moved {
            draft.thm.defines.retain(|x| x != &d);
            if let Some(reading) = draft.thm.readings.shift_remove(&d.label) {
                scope.readings.insert(d.label.clone(), reading);
            }
            scope.defines.push(d);
        }
        draft.thm.steps = draft.steps.into_iter().map(|s| s.step).collect();
        theorems.push(draft.thm);
    }

    for line in read_lines(text) {
        let t = line.text.clone();
        // A `reads` line belongs to the define immediately above it, so what
        // a define leaves behind survives exactly one line.
        let previous = just_defined.take();
        if t.starts_with("theorem ") && line.indent == 0 {
            close_step(path, &thm, &mut step)?;
            settle(thm.take(), &mut scope, &mut theorems);
            let name = str::trim(&t["theorem ".len()..]).to_string();
            if !full(&THEOREM_NAME, &name) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem name {} is malformed", repr(&name)),
                ));
            }
            thm = Some(DraftTheorem {
                thm: Theorem {
                    name,
                    hypotheses: Vec::new(),
                    ranges: Vec::new(),
                    conclusion: String::new(),
                    defines: Vec::new(),
                    readings: IndexMap::new(),
                    steps: Vec::new(),
                    line: line.no,
                    path: path.to_string(),
                    fields: IndexMap::new(),
                    scope: scope_id,
                },
                steps: Vec::new(),
            });
            pending_markers.clear();
            pending_openers.clear();
            part_no.clear();
            by_number.clear();
            header = true;
            last_field = None;
            continue;
        }
        let Some(draft) = thm.as_mut() else {
            if t.starts_with("import ") {
                if !scope.defines.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "an import below a define; imports come first",
                    ));
                }
                match importing(path, line.no, &t)? {
                    Imported::Proof(module, no) => {
                        scope.proof_imports.push((module, no))
                    }
                    Imported::Definition(import) => scope.imports.push(import),
                    Imported::Function(import) => scope.functions.push(import),
                }
                continue;
            }
            // A define before any theorem is the file's, for every theorem.
            if t.starts_with("define ") {
                let Some(label) = label_at_end(&t) else {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "define line carries no label",
                    ));
                };
                match define_parts(&t) {
                    crate::outcome::Declined(d) => {
                        return Err(d.into_problem(path, line.no));
                    }
                    Built(DefineParts::Recursion(_)) => {
                        return Err(Problem::new(
                            path,
                            line.no,
                            "a define by recursion is written in the theorem that uses it, in its statement or its proof",
                        ));
                    }
                    Built(DefineParts::One(_)) => {}
                }
                let d = DefineLine {
                    text: t.clone(),
                    label,
                    line: line.no,
                };
                scope.defines.push(d.clone());
                just_defined = Some(d);
                continue;
            }
            if let (Some(rest), Some(d)) = (t.strip_prefix("reads"), &previous) {
                scope
                    .readings
                    .insert(d.label.clone(), (str::trim(rest).to_string(), line.no));
                continue;
            }
            return Err(Problem::new(
                path,
                line.no,
                "text before any theorem header that is neither an import nor a define",
            ));
        };

        let head = t.split_whitespace().next().unwrap_or_default().to_string();
        if header && THEOREM_FIELDS.contains(&head.as_str()) {
            if draft.thm.fields.contains_key(&head) {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("theorem {} says {head} twice", draft.thm.name),
                ));
            }
            draft
                .thm
                .fields
                .insert(head.clone(), str::trim(&t[head.len()..]).to_string());
            last_field = Some((head, line.indent));
            continue;
        }
        if header {
            if let Some((field, indent)) = &last_field {
                if line.indent > *indent {
                    let value = draft.thm.fields.get_mut(field).unwrap();
                    value.push(' ');
                    value.push_str(&t);
                    continue;
                }
            }
        }
        header = false;

        if let Some(m) = STEP_RE.captures(&t) {
            close_step(path, &thm, &mut step)?;
            let draft = thm.as_mut().unwrap();
            let number = StepNo::parse(&m[1]);
            // Resolve held markers and openers against the owner of the block
            // that this step sits in, and say which part it sits in.
            let parent = number.parent();
            let owner = by_number.get(&parent).copied();
            for (marker, no, note) in pending_markers.drain(..) {
                let Some(owner) = owner else {
                    return Err(Problem::new(
                        path,
                        no,
                        format!("part marker {} outside any block", repr(&marker)),
                    ));
                };
                draft.steps[owner].step.parts.push((marker, no));
                let index = part_no.get(&parent).map_or(0, |n| n + 1);
                part_no.insert(parent.clone(), index);
                if let Some(note) = note {
                    draft.steps[owner].step.part_notes.insert(index, note);
                }
            }
            let current = part_no.get(&parent).copied();
            for (kind, text, label, no) in pending_openers.drain(..) {
                let Some(owner) = owner else {
                    return Err(Problem::new(
                        path,
                        no,
                        format!("{kind} line outside any block"),
                    ));
                };
                draft.steps[owner].step.openers.push(Opener {
                    kind,
                    text,
                    label,
                    line: no,
                    part: current,
                });
            }
            draft.steps.push(DraftStep {
                step: Step {
                    number: number.clone(),
                    claim: vec![m[2].to_string()],
                    just: placeholder_justification(),
                    requires: Vec::new(),
                    parts: Vec::new(),
                    openers: Vec::new(),
                    line: line.no,
                    part: current,
                    note: None,
                    part_notes: IndexMap::new(),
                },
                has_just: false,
            });
            let at = draft.steps.len() - 1;
            by_number.insert(number, at);
            step = Some(at);
            continue;
        }

        if step.is_none() {
            if let Some(range) = Range::read(&t, line.no) {
                draft.thm.ranges.push(range);
                continue;
            }
        }
        let intro = Intro::parse(&head);
        if matches!(intro, Some(Intro::Let | Intro::Assume)) && step.is_none() {
            draft.thm.hypotheses.push(Hypothesis {
                kind: intro.unwrap(),
                text: t.clone(),
                label: label_at_end(&t),
                line: line.no,
            });
            continue;
        }
        if head == "then" && step.is_none() {
            draft.thm.conclusion = str::trim(&t["then".len()..]).to_string();
            continue;
        }
        if head == "define" {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "define line carries no label",
                ));
            };
            if let crate::outcome::Declined(d) = define_parts(&t) {
                return Err(d.into_problem(path, line.no));
            }
            // A define names an object and is in scope from where it stands on.
            let d = DefineLine {
                text: t.clone(),
                label,
                line: line.no,
            };
            draft.thm.defines.push(d.clone());
            just_defined = Some(d);
            continue;
        }
        if head == "reads" {
            let Some(d) = &previous else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "reads line that does not follow a define",
                ));
            };
            draft.thm.readings.insert(
                d.label.clone(),
                (str::trim(&t["reads".len()..]).to_string(), line.no),
            );
            continue;
        }
        if head == "note" {
            let said = (str::trim(&t["note".len()..]).to_string(), line.no);
            // Under a part marker, the note says what that part does; the
            // marker is still held, because the step owning it is found only
            // when the part's first step arrives.
            if let Some((marker, _no, held)) = pending_markers.last_mut() {
                if held.is_some() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!("the {} part already carries a note", repr(marker)),
                    ));
                }
                if !pending_openers.is_empty() {
                    return Err(Problem::new(
                        path,
                        line.no,
                        format!(
                            "a note on the {} part goes directly under its marker, before its openers",
                            repr(marker)
                        ),
                    ));
                }
                *held = Some(said);
                continue;
            }
            match step {
                Some(at) if draft.steps[at].has_just => {
                    draft.steps[at].step.note = Some(said);
                }
                _ => {
                    return Err(Problem::new(
                        path,
                        line.no,
                        "note line outside a block",
                    ));
                }
            }
            continue;
        }
        if super::PART_MARKERS.contains(&t.as_str()) {
            pending_markers.push((t.clone(), line.no, None));
            continue;
        }
        if let Some(kind) = intro {
            let Some(label) = label_at_end(&t) else {
                return Err(Problem::new(
                    path,
                    line.no,
                    format!("{head} line carries no label"),
                ));
            };
            pending_openers.push((kind, t.clone(), label, line.no));
            continue;
        }
        if head == "requires" {
            let Some(at) = step else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "requires line outside a step",
                ));
            };
            let body = str::trim(&t["requires".len()..]);
            let Some((fact, how)) = body.split_once(':') else {
                return Err(Problem::new(
                    path,
                    line.no,
                    "requires line has no justification",
                ));
            };
            draft.steps[at].step.requires.push(Requires {
                fact: str::trim(fact).to_string(),
                how: str::trim(how).to_string(),
                line: line.no,
            });
            continue;
        }
        if let Some(at) = step {
            if !draft.steps[at].has_just {
                let mut defines: Vec<String> = Vec::new();
                for d in scope.defines.iter().chain(draft.thm.defines.iter()) {
                    if !defines.contains(&d.label) {
                        defines.push(d.label.clone());
                    }
                }
                for i in &scope.imports {
                    if !defines.contains(&i.label) {
                        defines.push(i.label.clone());
                    }
                }
                if starts_with_head(&t) || cites_define(&t, &defines).is_some() {
                    draft.steps[at].step.just =
                        parse_justification(path, &line, &defines)?;
                    draft.steps[at].has_just = true;
                } else {
                    draft.steps[at].step.claim.push(t.clone());
                }
                continue;
            }
            if draft.steps[at].step.just.head.is(Method::Calculation) {
                let cited = chain_citation(path, &line)?;
                let just = &mut draft.steps[at].step.just;
                just.refs.extend(cited);
                just.chain.push((line.text.clone(), line.no));
                continue;
            }
            return Err(Problem::new(
                path,
                line.no,
                format!(
                    "unexpected line after a justification: {}",
                    repr(prefix(&t, 48))
                ),
            ));
        }
        return Err(Problem::new(
            path,
            line.no,
            format!("unexpected line {}", repr(prefix(&t, 48))),
        ));
    }
    close_step(path, &thm, &mut step)?;
    settle(thm.take(), &mut scope, &mut theorems);
    Ok((scope, theorems))
}
