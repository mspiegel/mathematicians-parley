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
    corpus, index, link_definitions, link_functions, proof_files, record_files, Corpus,
    Item,
};
pub use proof::{
    cited_item, cited_items, cites_define, fmt, item_prefix, outermost, parse_proof,
    references, written_text, DefineLine, FileScope, Head, Hypothesis, Import, Intro,
    ItemImport, ItemKind, Justification, Method, Names, Opener, Range, Requires,
    ScopeId, Step, StepNo, Theorem,
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

/// An item's name, or a theorem's. It may open with a Greek letter, since a
/// library function is named by its record and a formula writes it, as σ.
pub const NAME: &str = r"[A-Za-zα-ω][A-Za-z0-9-]*";
/// What follows an item's prefix: the name its import gives it, or a theorem
/// of the file citing it. A path is read here too, so that a citation
/// written by its path is said to be one rather than left unread.
pub const CITED: &str = r"(?:[A-Za-zα-ω][A-Za-z0-9-]*/)*[A-Za-zα-ω][A-Za-z0-9-]*";
/// The prefix of a citation of any item, `thm:` and the rest.
pub const ITEM_PREFIX: &str = r"(?:thm|axi|mun|def):";
/// The standard library, the one module root that is not a proof file: its
/// files are records.
pub const STDLIB: &str = "stdlib";
/// Where the database, the library and what is built from them are kept,
/// under the working tree. Names are read from inside it, so the directory's
/// own name is in no name: `corpus/stdlib/numbers.records` is the module
/// `stdlib/numbers`.
pub const CORPUS: &str = "corpus";
pub const LABEL: &str = r"[A-Z]+[0-9]*";
pub const NUMBER: &str = r"\d+(?:\.\d+)*";
pub const REF: &str = r"(?:\d+(?:\.\d+)*|[A-Z]+[0-9]*)";

pub const PART_MARKERS: [&str; 3] = ["base", "step", "case"];

/// The module a file is: its path from the root without the extension, and
/// without `corpus/` for a file kept there.
pub fn module_of(path: &str) -> &str {
    let path = path
        .strip_prefix(CORPUS)
        .and_then(|rest| rest.strip_prefix('/'))
        .unwrap_or(path);
    match path.rfind('.') {
        Some(at) => &path[..at],
        None => path,
    }
}

/// The name a citation such as `thm:x` cites, without its prefix.
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
