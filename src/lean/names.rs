//! How the corpus's names are spelt in Lean.
//!
//! A module is a path of UpperCamelCase segments under `Parley`, one for
//! each segment of the name, so the theorem
//! `proofs/hammack/seven-divides-four-times/seven-divides-four-times` is
//! the module `Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes`
//! in `lean/Parley/Proofs/Hammack/SevenDividesFourTimes/SevenDividesFourTimes.lean`.
//! A declaration is the name in snake_case. An item is declared under its
//! citation prefix, `def_divides` for `def:divides`, so that no item's name
//! is ever one Mathlib's notation reaches for, `abs` or `exp`.

/// One segment, `seven-divides-four-times`, in UpperCamelCase.
fn camel(segment: &str) -> String {
    let mut out = String::new();
    for word in segment.split(['-', '_']) {
        let mut chars = word.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    // A Lean name does not start with a digit.
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, 'N');
    }
    out
}

/// The Lean module of a name of the corpus, `Parley.Proofs.Hammack.…`.
pub fn module_of(name: &str) -> String {
    let parts: Vec<String> = name.split('/').map(camel).collect();
    format!("Parley.{}", parts.join("."))
}

/// Where a Lean bridge's full name begins.
pub const LEAN_BRIDGES: &str = "lean-bridges/";

/// The Lean declaration a bridge's full name names: `lean-bridges/counting/
/// choose-outside` is `LeanBridges.Counting.choose_outside`, declared in
/// `corpus/lean-bridges/Counting.lean`. Declines a name that is not a
/// subject and a lemma under `lean-bridges/`.
pub fn bridge_of(full: &str) -> crate::outcome::Route<String> {
    let parts: Option<Vec<&str>> = full
        .strip_prefix(LEAN_BRIDGES)
        .map(|rest| rest.split('/').collect());
    match parts.as_deref() {
        Some([subject, lemma]) if !subject.is_empty() && !lemma.is_empty() => {
            crate::outcome::Route::Built(format!(
                "LeanBridges.{}.{}",
                camel(subject),
                snake(lemma)
            ))
        }
        _ => crate::outcome::Route::no(format!(
            "{full} is not a Lean bridge's full name, lean-bridges/<subject>/<lemma>"
        )),
    }
}

/// The file under `lean/` that holds a module.
pub fn path_of_module(module: &str) -> String {
    format!("lean/{}.lean", module.replace('.', "/"))
}

/// A declaration's name in snake_case, kept a Lean identifier: ASCII
/// letters, digits and underscores, never starting with a digit. A Greek
/// letter is spelt by its English name, as a Metamath label is: φ is
/// `phi`.
pub fn snake(name: &str) -> String {
    let mut out: String = crate::text::spelt_in_ascii(name)
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, 'n');
    }
    out
}

/// A letter of the page as a Lean identifier: a prime is Lean's `'`, and λ,
/// which Lean reserves, is spelt out.
pub fn letter(text: &str) -> String {
    let out: String = text
        .chars()
        .map(|c| match c {
            '′' => '\'',
            other => other,
        })
        .collect();
    match out.as_str() {
        "λ" => "lam".to_string(),
        "fun" | "end" | "at" | "by" | "do" | "if" | "then" | "else" | "let"
        | "have" | "show" | "from" | "in" | "match" | "with" | "open" => {
            format!("«{out}»")
        }
        _ => out,
    }
}

/// The name of a step's line, `s2` for step 2 and `s4_1` for step 4.1, or
/// a label as written, `H2`.
pub fn line_name(reference: &str) -> String {
    if reference.starts_with(|c: char| c.is_ascii_digit()) {
        format!("s{}", reference.replace('.', "_"))
    } else {
        // A label is written after an `h`, so that a label spelt as a
        // letter of the page, K, never hides the letter.
        format!("h{}", snake(reference))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_theorem_is_a_module_of_camel_segments() {
        assert_eq!(
            module_of(
                "proofs/hammack/seven-divides-four-times/seven-divides-four-times"
            ),
            "Parley.Proofs.Hammack.SevenDividesFourTimes.SevenDividesFourTimes"
        );
        assert_eq!(
            path_of_module("Parley.Items.Stdlib.Divisibility"),
            "lean/Parley/Items/Stdlib/Divisibility.lean"
        );
    }

    #[test]
    fn lines_and_declarations_are_identifiers() {
        assert_eq!(line_name("4.1"), "s4_1");
        assert_eq!(line_name("H2"), "hH2");
        assert_eq!(
            snake("seven-divides-four-times"),
            "seven_divides_four_times"
        );
        assert_eq!(snake("2-adic"), "n2_adic");
    }
}
