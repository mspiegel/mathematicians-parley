//! Text as the corpus is written and as the tools quote it.

pub mod encoding;
pub mod pyrepr;

pub use encoding::check_encoding;
pub use pyrepr::repr;

use unicode_segmentation::UnicodeSegmentation;

/// A name with each Greek letter written as its English name, for what
/// Metamath reads, which is ASCII: a label, and the name of a file it
/// includes. A theorem named σ is labelled from `sigma` and written to
/// `sigma.mm`.
pub fn spelt_in_ascii(name: &str) -> String {
    const GREEK: [(char, &str); 24] = [
        ('α', "alpha"),
        ('β', "beta"),
        ('γ', "gamma"),
        ('δ', "delta"),
        ('ε', "epsilon"),
        ('ζ', "zeta"),
        ('η', "eta"),
        ('θ', "theta"),
        ('ι', "iota"),
        ('κ', "kappa"),
        ('λ', "lambda"),
        ('μ', "mu"),
        ('ν', "nu"),
        ('ξ', "xi"),
        ('ο', "omicron"),
        ('π', "pi"),
        ('ρ', "rho"),
        ('σ', "sigma"),
        ('τ', "tau"),
        ('υ', "upsilon"),
        ('φ', "phi"),
        ('χ', "chi"),
        ('ψ', "psi"),
        ('ω', "omega"),
    ];
    name.chars()
        .map(|c| match GREEK.iter().find(|(g, _)| *g == c) {
            Some((_, spelt)) => spelt.to_string(),
            None => c.to_string(),
        })
        .collect()
}

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
