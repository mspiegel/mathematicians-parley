//! Whitespace as Python's `str.isspace` understands it.
//!
//! The corpus is read by stripping and splitting on this set, the one the
//! checker's messages and every committed file were produced with. Rust's
//! `char::is_whitespace` agrees on every character but four: the ASCII
//! information separators U+001C to U+001F, which this set counts as
//! whitespace. A line holding one would be read differently, so the tools
//! use this set and not Rust's.

/// Whether `c` is whitespace to Python's `str.isspace`.
pub fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}

/// `s.strip()`.
pub fn strip(s: &str) -> &str {
    s.trim_matches(is_space)
}

/// `s.lstrip()`.
pub fn lstrip(s: &str) -> &str {
    s.trim_start_matches(is_space)
}

/// `s.rstrip()`.
pub fn rstrip(s: &str) -> &str {
    s.trim_end_matches(is_space)
}

/// `s.split()`: the runs of text between runs of whitespace.
pub fn split(s: &str) -> Vec<&str> {
    s.split(is_space).filter(|w| !w.is_empty()).collect()
}

/// `s.split(None, 1)`: the first word, and the rest after the whitespace
/// that follows it, with trailing whitespace kept on the rest as Python
/// keeps it.
pub fn split_once_space(s: &str) -> Vec<&str> {
    let s = lstrip(s);
    if s.is_empty() {
        return Vec::new();
    }
    match s.find(is_space) {
        None => vec![s],
        Some(at) => {
            let rest = lstrip(&s[at..]);
            if rest.is_empty() {
                vec![&s[..at]]
            } else {
                vec![&s[..at], rest]
            }
        }
    }
}

/// `' '.join(s.split())`: runs of whitespace closed up to one space.
pub fn squash(s: &str) -> String {
    split(s).join(" ")
}

/// The first `n` characters of `s`, as `s[:n]` counts them: by scalar
/// value, never by byte.
pub fn prefix(s: &str, n: usize) -> &str {
    match s.char_indices().nth(n) {
        Some((at, _)) => &s[..at],
        None => s,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn information_separators_are_space() {
        assert_eq!(strip("\u{1c} a \u{1f}"), "a");
        assert_eq!(split("a\u{1d}b"), vec!["a", "b"]);
    }

    #[test]
    fn split_once_keeps_the_rest_whole() {
        assert_eq!(split_once_space("  let x ∈ A  "), vec!["let", "x ∈ A  "]);
        assert_eq!(split_once_space("then"), vec!["then"]);
        assert_eq!(split_once_space("then   "), vec!["then"]);
        assert!(split_once_space("   ").is_empty());
    }

    #[test]
    fn a_prefix_counts_scalar_values() {
        assert_eq!(prefix("𝒫A ∈ B", 2), "𝒫A");
        assert_eq!(prefix("ab", 5), "ab");
    }
}
