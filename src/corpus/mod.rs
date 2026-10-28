//! Reading the database files and the proof skeletons that `GRAMMAR.md`
//! describes.
//!
//! A claim is an opaque run of text here. Nothing in this module looks
//! inside a formula; `formula` does that.

pub mod define;
pub(crate) mod lines;
pub(crate) mod load;
pub mod phrases;
pub mod proof;
pub(crate) mod records;
pub mod skeleton;
pub(crate) mod values;

pub use define::{
    define_parts, for_pieces, step_index, Define, DefineParts, Param, Recursion,
    RuleText, Within,
};
pub use lines::{read_lines, Line};
pub use load::{
    corpus, index, link_definitions, link_functions, proof_files, record_files, Corpus,
    Item,
};
pub use proof::{
    cited_items, fmt, outermost, parse_proof, written_text, DefineLine, FileScope,
    Head, Hypothesis, Import, Intro, ItemImport, ItemKind, Justification, Kinded,
    Method, Names, Opener, Range, Reason, Requires, ScopeId, Step, StepNo, Theorem,
};
pub use records::{parse_database, Record, RecordKind, FIELDS};
pub use skeleton::{
    is_label, is_number, is_ref, item_kind, naming_pieces, starts_with_head, Place,
    Source,
};
pub use values::{Value, Values};

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

/// The standard library, the one module root that is not a proof file: its
/// files are records.
pub const STDLIB: &str = "stdlib";
/// Where the database, the library and what is built from them are kept,
/// under the working tree. Names are read from inside it, so the directory's
/// own name is in no name: `corpus/stdlib/numbers.records` is the module
/// `stdlib/numbers`.
pub const CORPUS: &str = "corpus";

pub const PART_MARKERS: [&str; 4] = ["base", "step", "case", "direction"];

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
