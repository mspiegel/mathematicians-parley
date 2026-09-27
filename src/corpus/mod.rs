//! Reading the database files and the proof skeletons that `GRAMMAR.md`
//! describes.
//!
//! A claim is an opaque run of text here. Nothing in this module looks
//! inside a formula; `formula` does that.

pub mod define;
pub mod lines;
pub mod load;
pub mod proof;
pub mod records;

pub use define::{define_parts, Define, DefineParts, Recursion};
pub use lines::{read_lines, Line};
pub use load::{
    corpus, index, link_definitions, proof_files, record_files, Corpus, Item,
};
pub use proof::{
    cited_item, cited_items, cites_define, fmt, outermost, parse_proof, references,
    written_text, DefineLine, FileScope, Head, Hypothesis, Import, Intro, ItemKind,
    Justification, Method, Opener, Requires, ScopeId, Step, StepNo, Theorem,
};
pub use records::{parse_database, Record, RecordKind, FIELDS};

/// Build a regular expression once, the first time it is used.
#[macro_export]
macro_rules! regex {
    ($name:ident, $pattern:expr) => {
        static $name: std::sync::LazyLock<regex::Regex> =
            std::sync::LazyLock::new(|| regex::Regex::new(&$pattern).unwrap());
    };
}

/// Build a regular expression that needs lookaround once.
#[macro_export]
macro_rules! fancy {
    ($name:ident, $pattern:expr) => {
        static $name: std::sync::LazyLock<fancy_regex::Regex> =
            std::sync::LazyLock::new(|| fancy_regex::Regex::new(&$pattern).unwrap());
    };
}

/// An item's name, or a theorem's.
pub const NAME: &str = r"[A-Za-z][A-Za-z0-9-]*";
/// What follows `def:` or `thm:`: an item's name, spelt with the path of the
/// file that holds it, or bare for a theorem of the file citing it.
pub const CITED: &str = r"(?:[A-Za-z][A-Za-z0-9-]*/)*[A-Za-z][A-Za-z0-9-]*";
/// The standard library, the one module root that is not a proof file: it is
/// never imported, and every proof may cite it.
pub const STDLIB: &str = "stdlib";
pub const LABEL: &str = r"[A-Z]+[0-9]*";
pub const NUMBER: &str = r"\d+(?:\.\d+)*";
pub const REF: &str = r"(?:\d+(?:\.\d+)*|[A-Z]+[0-9]*)";

pub const PART_MARKERS: [&str; 3] = ["base", "step", "case"];

/// The module a file is: its path from the root without the extension.
pub fn module_of(path: &str) -> &str {
    match path.rfind('.') {
        Some(at) => &path[..at],
        None => path,
    }
}

/// The full name a citation means, cited from a file of `module`.
///
/// A spelt name is taken as written; a bare one is a theorem of the citing
/// file. Whether anything has that name is the caller's to ask.
pub fn resolve(cited: &str, module: &str) -> String {
    if cited.contains('/') {
        cited.to_string()
    } else {
        format!("{module}/{cited}")
    }
}

/// The name a `def:` or `thm:` head cites, without its prefix.
pub fn cited_name(head: &str) -> &str {
    match head.split_once(':') {
        Some((_, name)) => name,
        None => head,
    }
}

pub fn in_stdlib(name: &str) -> bool {
    name.starts_with("stdlib/")
}

/// Whether `text` is wholly one match of `re`, as Python's `fullmatch`.
pub fn full(re: &regex::Regex, text: &str) -> bool {
    re.find(text)
        .is_some_and(|m| m.start() == 0 && m.end() == text.len())
}
