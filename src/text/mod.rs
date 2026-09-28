//! Text as the corpus is written and as the tools quote it.

pub mod encoding;
pub mod pyrepr;

pub use encoding::check_encoding;
pub use pyrepr::repr;

use unicode_segmentation::UnicodeSegmentation;

/// The first `n` characters of `s`, as a reader counts them: by grapheme
/// cluster, so a quoted excerpt never keeps a letter and drops the accent
/// written after it, as `x̄` in the library's notes would lose its bar.
pub fn prefix(s: &str, n: usize) -> &str {
    match s.grapheme_indices(true).nth(n) {
        Some((at, _)) => &s[..at],
        None => s,
    }
}

/// Runs of whitespace closed up to one space, and none at either end, so two
/// spellings of a formula that differ only in spacing compare equal.
pub fn squash(s: &str) -> String {
    s.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_prefix_counts_what_a_reader_sees() {
        assert_eq!(prefix("𝒫A ∈ B", 2), "𝒫A");
        assert_eq!(prefix("ab", 5), "ab");
        assert_eq!(prefix("√(x·x\u{304})", 5), "√(x·x\u{304}");
    }
}
