//! The checker catches things.
//!
//! Each case takes the corpus, makes one edit that should be a defect, and
//! requires that the checker report it. A checker that passes a clean corpus
//! proves nothing on its own; this is the half that matters.
//!
//! The corpus is read once into memory and each case edits it through an
//! overlay of its own, so no case copies a directory and none can see
//! another's edit. The clean corpus is checked whole; a case checks the
//! theorems its edits can reach (`checker::run_edited`), against the clean
//! corpus as read once (`checker::Clean`). The cases run side by side
//! (`threads::in_order_slots`), and are reported in the order they are written.
//!
//! Every message the checker writes out where it reports it is said by some
//! case, so that a check no case reaches is found: one that had stopped
//! running said nothing, and nothing here noticed. A message put together
//! elsewhere and handed to the report is not read this way.

mod calculations;
mod citations;
mod defines;
mod geometry;
mod imports;
mod library;
mod methods;
mod numbers;
mod reading;
mod structure;

use std::fs;
use std::path::{Path, PathBuf};

use parley::checker;
use parley::checker::Clean;
use parley::corpus::proof::METHODS;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::in_order_slots;

/// The threads the cases are shared among: the slots nextest gives this
/// binary's tests (`threads-required` in `.config/nextest.toml`).
const SLOTS: usize = 8;

/// A file that defines a function outside its theorems, for the cases below
/// that import it, use it, or define its name again.
const TRI: &str = "define T(k) := k(k + 1)/2, for k ∈ ℕ                                  (D1)\n       reads the k-th triangular number\n\ntheorem tri-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    calculation\n      T(1) = 1(1 + 1)/2        D1\n           = 1                 arithmetic\n";

/// A file that squares a quotient whose divisor is a letter. x/y is real by
/// what the page says once of x and y only where a line says y ≠ 0, so H3
/// is cited for it.
const QUOTIENT: &str = "import mundane theorem    stdlib/numbers/square-nonneg\n\ntheorem quotient-square\n  let x ∈ ℝ                                                           (H1)\n  let y ∈ ℝ                                                           (H2)\n  assume y ≠ 0                                                        (H3)\n  then (x/y)² ≥ 0\n\n1.  (x/y)² ≥ 0\n    mun:square-nonneg x := x/y, from H3\n";

/// One edit: the file, the text replaced (its first occurrence), and what
/// replaces it. No text replaced writes a file that was not there.
struct Edit {
    file: &'static str,
    old: Option<String>,
    new: String,
}

struct Case {
    name: &'static str,
    edits: Vec<Edit>,
    expect: &'static str,
}

fn case(name: &'static str, edits: Vec<Edit>, expect: &'static str) -> Case {
    Case {
        name,
        edits,
        expect,
    }
}

fn edit(file: &'static str, old: Option<String>, new: String) -> Edit {
    Edit { file, old, new }
}

/// Where the cases that plant defects in the law of sines write it.
const SINES_FILE: &str = "proofs/wiedijk/similar-by-sines.proof";

/// Similar triangles by the angle sum and the law of sines, a proof whose
/// algebra combines angles and sines. The corpus
/// proves similarity from the postulates instead (`angle-angle-similar`),
/// so the cases that plant defects in such lines write this one first.
const SINES: &str = r#"import theorem            proofs/wiedijk/angle-sum/angle-sum
import theorem            stdlib/geometry/law-of-sines
import theorem            stdlib/geometry/altitude-foot
import mundane theorem    stdlib/geometry/segment-addition
import mundane theorem    stdlib/geometry/angle-along-segment
import mundane theorem    stdlib/geometry/angle-symmetric
import mundane theorem    stdlib/geometry/between-symmetric
import mundane theorem    stdlib/geometry/sine-positive
import definition         stdlib/geometry/triangle
import mundane theorem    stdlib/numbers/multiply-cancel
import definition         stdlib/trigonometry/sin

theorem similar-triangles
  note        Two triangles with two angles equal have the third equal too
              (angle-sum), and the law of sines then gives their sides in
              proportion.
  let P be a point                                                   (H1)
  let Q be a point                                                    (H2)
  let R be a point                                                    (H3)
  let P′ be a point                                                   (H4)
  let Q′ be a point                                                   (H5)
  let R′ be a point                                                   (H6)
  assume P, Q, R form a triangle                                      (H7)
  assume P′, Q′, R′ form a triangle                                   (H8)
  assume ∠QPR = ∠Q′P′R′                                               (H9)
  assume ∠PQR = ∠P′Q′R′                                               (H10)
  then |PQ|·|P′R′| = |P′Q′|·|PR|

1.  ∠QPR + ∠PQR + ∠QRP = 180°
    thm:angle-sum A := P, B := Q, C := R, from H7

2.  ∠Q′P′R′ + ∠P′Q′R′ + ∠Q′R′P′ = 180°
    thm:angle-sum A := P′, B := Q′, C := R′, from H8

3.  ∠QPR + ∠PQR + ∠QRP = ∠Q′P′R′ + ∠P′Q′R′ + ∠Q′R′P′
    calculation
      ∠QPR + ∠PQR + ∠QRP = 180°                               1
                         = ∠Q′P′R′ + ∠P′Q′R′ + ∠Q′R′P′         2

4.  ∠QRP = ∠Q′R′P′
    algebra, from H9, H10, 3

5.  |PQ|·sin(∠PQR) = |PR|·sin(∠QRP)
    thm:law-of-sines, from H7

6.  |P′Q′|·sin(∠P′Q′R′) = |P′R′|·sin(∠Q′R′P′)
    thm:law-of-sines P := P′, Q := Q′, R := R′, from H8

7.  |P′Q′|·sin(∠PQR) = |P′R′|·sin(∠Q′R′P′)
    substitute ∠PQR = ∠P′Q′R′ (H10) into line 6

8.  |P′Q′|·sin(∠PQR) = |P′R′|·sin(∠QRP)
    substitute ∠QRP = ∠Q′R′P′ (line 4) into line 7

9.  |PQ|·|P′R′|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)
    algebra, from 5

10. |P′Q′|·|PR|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)
    algebra, from 8

11. |PQ|·|P′R′|·sin(∠PQR) = |P′Q′|·|PR|·sin(∠PQR)
    calculation
      |PQ|·|P′R′|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)       9
                            = |P′Q′|·|PR|·sin(∠PQR)       10

12. sin(∠PQR) > 0
    mun:sine-positive, from H7

13. sin(∠PQR) ≠ 0
    inequalities
      sin(∠PQR) > 0      12
      sin(∠PQR) ≠ 0      weakening

14. |PQ|·|P′R′| = |P′Q′|·|PR|
    mun:multiply-cancel a := |PQ|·|P′R′|, b := |P′Q′|·|PR|, c := sin(∠PQR),
      from 11
    requires sin(∠PQR) ≠ 0: from 13
"#;

/// The edits that write `SINES` and plant `new` in place of `old` there.
fn in_sines(old: &str, new: &str) -> Vec<Edit> {
    vec![
        edit(SINES_FILE, None, SINES.to_string()),
        edit(SINES_FILE, Some(old.to_string()), new.to_string()),
    ]
}

/// The corpus as it stands: the database, the library, and every proof.
fn clean() -> Memory {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap()
}

/// The clean corpus read once, which each case's edits are read against.
/// What it holds cannot be shared between threads, so each thread reads its
/// own.
fn clean_read(clean: &Memory) -> Clean {
    Clean::read(clean)
        .unwrap_or_else(|out| panic!("the corpus reads: {}", out.complained))
}

/// Plant one case's edits, or say why they could not be planted.
fn plant<'a>(case: &Case, clean: &'a Memory) -> Result<Overlay<'a>, String> {
    let mut tree = Overlay::new(clean);
    for e in &case.edits {
        let Some(old) = &e.old else {
            tree.write(e.file, e.new.clone().into_bytes());
            continue;
        };
        let text = tree
            .read_text(e.file)
            .map_err(|err| format!("  SETUP FAILED  {}\n      {err}", case.name))?;
        if !text.contains(old.as_str()) {
            return Err(format!(
                "  SETUP FAILED  {}\n      anchor not found in {}",
                case.name, e.file
            ));
        }
        tree.write(e.file, text.replacen(old.as_str(), &e.new, 1).into_bytes());
    }
    Ok(tree)
}

/// What the checker prints of `tree`, the case's edits planted in it, with
/// the theorems the edits reach checked (`checker::run_edited`).
fn checked_planted(case: &Case, tree: &dyn Source) -> String {
    let edited: Vec<String> = case.edits.iter().map(|e| e.file.to_string()).collect();
    checker::run_edited(tree, &edited).printed
}

/// What one case says, whether it missed, and everything the checker
/// printed: a case misses where its edit could not be planted, or the
/// checker did not report it.
fn outcome(case: &Case, clean: &Memory, read: &Clean) -> (String, bool, String) {
    let tree = match plant(case, clean) {
        Ok(tree) => tree,
        Err(why) => return (why, true, String::new()),
    };
    // Only what the edits reach is checked: a case passes only where its
    // problem is reported, and a theorem left unchecked can only leave a
    // problem out.
    let edited: Vec<String> = case.edits.iter().map(|e| e.file.to_string()).collect();
    let out = read.run_edited(&tree, &edited).printed;
    if out.contains(case.expect) {
        return (format!("  caught        {}", case.name), false, out);
    }
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with(|c: char| c.is_ascii_digit()))
        .collect();
    let got: String = lines.join(" | ").chars().take(200).collect();
    (
        format!(
            "  NOT CAUGHT    {}\n      expected a report containing {:?}\n      got: {got}",
            case.name, case.expect
        ),
        true,
        out,
    )
}

/// Every `.rs` file under `dir`, in the directories the checker's modules
/// are cut into as well as beside them.
fn rust_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    for entry in fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("{} reads: {e}", dir.display()))
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if path.is_dir() {
            found.extend(rust_files(&path));
        } else if path.extension().is_some_and(|x| x == "rs") {
            found.push(path);
        }
    }
    found
}

/// A message the checker can give: the words its format string writes
/// between the values it fills in.
struct Message {
    words: Vec<String>,
}

impl Message {
    /// Whether a line of `out` is this message: its words in it, in order.
    fn said_in(&self, out: &str) -> bool {
        out.lines().any(|line| {
            let mut rest = line;
            self.words.iter().all(|w| match rest.find(w.as_str()) {
                Some(at) => {
                    rest = &rest[at + w.len()..];
                    true
                }
                None => false,
            })
        })
    }
}

/// The first string literal of the call that opens at `text`, up to the
/// bracket that closes it, as the string it writes: an escaped quote a
/// quote, and a backslash ending a line the end of the line and the spaces
/// after it.
fn first_literal(text: &str) -> Option<String> {
    let mut depth = 0;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return None;
                }
            }
            '"' => {
                let mut out = String::new();
                while let Some(c) = chars.next() {
                    match c {
                        '"' => return Some(out),
                        '\\' => match chars.next() {
                            Some('\n') => {
                                while chars.next_if(|c| c.is_whitespace()).is_some() {}
                            }
                            Some('n') => out.push('\n'),
                            Some(other) => out.push(other),
                            None => return None,
                        },
                        _ => out.push(c),
                    }
                }
                return None;
            }
            _ => {}
        }
    }
    None
}

/// Every message the checker writes out where it reports it: each `.say(`
/// under `src/checker/` whose message is a string written there. The words
/// are the pieces of the string between its `{…}`, each with a word of
/// three letters in it, so that a piece of punctuation between two values
/// matches anything.
fn messages() -> Vec<Message> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/checker");
    let mut files = rust_files(&root);
    files.sort();
    let mut out = Vec::new();
    for file in files {
        let text = fs::read_to_string(&file).expect("a source file reads");
        for (at, _) in text.match_indices(".say(") {
            let Some(said) = first_literal(&text[at + ".say".len()..]) else {
                continue;
            };
            let words: Vec<String> = said
                .split('{')
                .enumerate()
                .map(|(i, piece)| {
                    if i == 0 {
                        piece
                    } else {
                        piece.split_once('}').map_or("", |(_, rest)| rest)
                    }
                })
                .filter(|piece| {
                    piece
                        .split(|c: char| !c.is_alphabetic())
                        .any(|w| w.chars().count() >= 3)
                })
                .map(String::from)
                .collect();
            if words.is_empty() {
                continue;
            }
            out.push(Message { words });
        }
    }
    out
}

/// A file that does not import the library's C may give the letter to a
/// function of its own: the library function is in scope only where it is
/// imported.
#[test]
fn a_file_that_does_not_import_a_library_function_may_use_its_name() {
    let clean = clean();
    let case = case(
        "import a function as C where the library's C is not imported",
        vec![
            edit("proofs/wiedijk/tri.proof", None, TRI.to_string()),
            edit(
                "proofs/wiedijk/tri-use.proof",
                None,
                "import theorem proofs/wiedijk/tri/tri-one\nimport definition proofs/wiedijk/tri/T as C (D1)\n\ntheorem use-one\n  then C(1) = 1\n\n1.  C(1) = 1\n    thm:tri-one, from D1\n".to_string(),
            ),
        ],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

/// A quotient's divisor not being zero is what a line cited for it says, and
/// that line does work: the case below that takes it away is a defect only
/// if the file with it is clean.
#[test]
fn a_line_saying_a_divisor_is_not_zero_does_work() {
    let clean = clean();
    let case = case(
        "cite y ≠ 0 for a quotient by y",
        vec![edit(
            "proofs/wiedijk/quotient.proof",
            None,
            QUOTIENT.to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

/// An item's function letter that the page names alike is found by
/// matching where the citation gives it no value. The map a match may bind
/// it to names the page's letter of the same name, E ↦ (s ↦ E(s)) or
/// t ↦ (y ↦ t(g(y))); what it gives is the page's own term, compared as
/// written, and not filled in again without end.
#[test]
fn a_function_letter_named_alike_is_found_without_a_pair() {
    let clean = clean();
    let cases = [
        case(
            "cite set-image with no values, the page's letters named as the item's",
            vec![edit(
                "proofs/wiedijk/image-back.proof",
                None,
                "import definition         stdlib/functions/set-image\n\ntheorem image-back\n  let Y be a set                                                      (H1)\n  let Z be a set                                                      (H2)\n  let E : Y → Z                                                       (H3)\n  let u be an element                                                 (H4)\n  assume there is s ∈ Y with u = E(s)                                 (H5)\n  then u ∈ {E(s) : s ∈ Y}\n\n1.  s ∈ Y. u = E(s).\n    obtain s from H5\n\n2.  u ∈ {E(s) : s ∈ Y}\n    def:set-image, from 1\n".to_string(),
            )],
            "",
        ),
        case(
            "cite product-reindex with no values, the page's letters named as the item's",
            vec![edit(
                "proofs/wiedijk/reindex-plain.proof",
                None,
                "import mundane theorem stdlib/sums/product-reindex\n\ntheorem reindex-plain\n  let Y be a set                                                      (H1)\n  assume Y is finite                                                  (H2)\n  let Z be a set                                                      (H5)\n  let g : Y → Z be one-to-one and onto                                (H3)\n  let t : Z → ℝ                                                       (H4)\n  then ∏(z ∈ Z) t(z) = ∏(y ∈ Y) t(g(y))\n\n1.  ∏(z ∈ Z) t(z) = ∏(y ∈ Y) t(g(y))\n    mun:product-reindex, from H2, H3\n".to_string(),
            )],
            "",
        ),
    ];
    for case in &cases {
        let tree = plant(case, &clean).unwrap();
        let out = checked_planted(case, &tree);
        assert!(out.contains("\n0 problem(s)\n"), "{}: {out}", case.name);
    }
}

/// A substitute justification that matches no production has no reading,
/// so it is told that alone: what a substitution makes is not asked of the
/// parts the reader cut from it (`Justification::unproduced`).
#[test]
fn an_unread_substitute_is_told_only_that_it_does_not_read() {
    let clean = clean();
    let case = case(
        "end a substitute justification with a marker it cannot carry",
        vec![edit(
            "proofs/wiedijk/unread-substitute.proof",
            None,
            "theorem unread-substitute\n  let x ∈ ℝ                                                           (H1)\n  assume x > 1                                                        (H2)\n  then x ≠ 0\n\n1.  x ≠ 0\n    contradiction\n    suppose x = 0                                                     (S)\n\n    1.1.  0 > 1\n          substitute x = 0 (S) into H2, which is impossible\n".to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    assert!(out.contains("justification matches no production"), "{out}");
    assert!(!out.contains("which putting one side of"), "{out}");
}

/// One reason line of the corpus headed by each method, and one citing an
/// item: the method as `Method::as_str` spells it, the file, and the line
/// as written.
const READ_REASONS: &[(&str, &str, &str)] = &[
    (
        "obtain",
        "proofs/setmm/halves-series.proof",
        "          obtain N: thm:archimedean x := ε, from A1",
    ),
    (
        "exhibit",
        "proofs/setmm/limit-constant-multiple.proof",
        "          exhibit, from 4.6",
    ),
    (
        "substitute",
        "proofs/setmm/halves-series.proof",
        "          substitute Σ(k = 1 to m) 1/2^k = 1 − 1/2^m (IH) into line 2.2",
    ),
    (
        "instantiate",
        "proofs/setmm/limit-constant-multiple.proof",
        "          instantiate ε := ε/(2·(|C| + 1)) in line 4.3, from 4.1, 4.2",
    ),
    ("algebra", "proofs/setmm/minus-one-mod.proof", "    algebra"),
    (
        "arithmetic",
        "proofs/setmm/halves-series.proof",
        "          arithmetic",
    ),
    (
        "real arithmetic",
        "proofs/identities/ln-above-one-is-positive.proof",
        "    real arithmetic",
    ),
    (
        "inequalities",
        "proofs/setmm/floor-below-non-integer.proof",
        "    inequalities, from 1, 3",
    ),
    (
        "transitivity",
        "proofs/setmm/halves-series.proof",
        "                  transitivity, from A2, 3.2.2",
    ),
    (
        "antisymmetry",
        "proofs/setmm/limit-unique.proof",
        "    antisymmetry, from 1, 2",
    ),
    (
        "membership",
        "proofs/setmm/limit-constant-multiple.proof",
        "          membership",
    ),
    (
        "inspection",
        "proofs/setmm/image-empty.proof",
        "          inspection, contradicting 1.2",
    ),
    (
        "join",
        "proofs/setmm/halves-series.proof",
        "                  join 3.2.7, 3.2.10",
    ),
    (
        "restate",
        "proofs/setmm/divisor-of-power.proof",
        "          restate H4",
    ),
    (
        "contradiction",
        "proofs/setmm/floor-below-non-integer.proof",
        "    contradiction",
    ),
    ("proof", "proofs/setmm/halves-series.proof", "    proof"),
    (
        "induction",
        "proofs/setmm/halves-series.proof",
        "    induction on k starting at 1",
    ),
    (
        "cases",
        "proofs/setmm/joined-functions.proof",
        "          cases, from 1.1",
    ),
    (
        "both directions",
        "proofs/setmm/square-roots-equal.proof",
        "    both directions",
    ),
    (
        "calculation",
        "proofs/setmm/halves-series.proof",
        "          calculation",
    ),
    (
        "an item",
        "proofs/wiedijk/pythagoras.proof",
        "    mun:segment-addition P := A, Q := B, S := D, from 1",
    ),
];

/// A reason that matches no production has no reading, and is told that
/// alone: no other check asks anything of the parts the reader cut from it,
/// or of the lines it may cite (`Justification::unproduced`). Each reason
/// line of `READ_REASONS` is broken by a marker it cannot carry, the
/// mistake trial 13 met, and its file must report that one problem. Every
/// method has a line, so a check keyed on a method added later is asked too.
#[test]
fn a_reason_that_does_not_read_is_told_only_that() {
    for method in METHODS {
        assert!(
            READ_REASONS.iter().any(|(m, _, _)| *m == method.as_str()),
            "no reason line of {} in READ_REASONS",
            method.as_str()
        );
    }
    let clean = clean();
    for &(method, file, line) in READ_REASONS {
        let case = case(
            "end a reason line with a marker it cannot carry",
            vec![edit(
                file,
                Some(format!("\n{line}\n")),
                format!("\n{line}, which is impossible\n"),
            )],
            "",
        );
        let tree = plant(&case, &clean).unwrap();
        let out = checked_planted(&case, &tree);
        let problems: Vec<&str> = out
            .lines()
            .filter(|l| l.starts_with(&format!("{file}:")))
            .collect();
        assert!(
            problems.len() == 1
                && problems[0].contains("justification matches no production"),
            "{method}: {problems:#?}"
        );
    }
}

/// A forbid the file keeps is no defect: a file that does not import
/// side-side-side may forbid it, and an item it imports, the converse of
/// Pythagoras, may rest on it.
#[test]
fn a_forbid_kept_says_nothing() {
    let clean = clean();
    let file = "proofs/euclid/three-four-five.proof";
    let case = case(
        "forbid an item the file does not import",
        vec![edit(
            file,
            Some("forbid theorem            stdlib/geometry/law-of-sines\n".to_string()),
            "forbid theorem            stdlib/geometry/law-of-sines\nforbid theorem            stdlib/geometry/side-side-side\n"
                .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    let problems: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with(&format!("{file}:")))
        .collect();
    assert!(problems.is_empty(), "{problems:#?}");
}

/// A citation whose claim is what the item concludes, with one hypothesis
/// not supplied, is reported once, naming that hypothesis: here
/// divides-difference without line 5.2, which says p divides n!. The other
/// hypotheses are supplied, and the claim is the item's conclusion. Line
/// 5.2 is then cited by nothing, which is said of it too.
#[test]
fn a_hypothesis_not_supplied_is_named_alone() {
    let clean = clean();
    let case = case(
        "drop the line that supplies one hypothesis",
        vec![edit(
            "proofs/wiedijk/infinitely-many-primes.proof",
            Some(
                "mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2"
                    .to_string(),
            ),
            "mun:divides-difference d := p, a := n! + 1, b := n!, from 3".to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    assert!(
        out.contains(
            "which asks for p divides n!, and what it cites does not supply it"
        ),
        "{out}"
    );
    assert!(!out.contains("does not conclude"), "{out}");
    assert!(out.contains("step 5.2 is cited by nothing"), "{out}");
    assert!(out.contains("\n2 problem(s)\n"), "{out}");
}

/// A step number written twice, once in each direction of a biconditional,
/// is reported once as numbered twice. Each step keeps the block it is
/// written in, and a citation of the number reads the one written above it:
/// the first 1.2 cites D1, which is in scope there, and the calculation's
/// link cites that 1.2, which says what the link does.
#[test]
fn a_number_written_twice_is_reported_alone() {
    let clean = clean();
    let case = case(
        "write one step number in each direction",
        vec![edit(
            "proofs/wiedijk/twice.proof",
            None,
            "\
theorem twice
  let a ∈ ℝ                                                           (H1)
  let b ∈ ℝ                                                           (H2)
  then a + 1 = b + 1 ↔ a = b

1.  a + 1 = b + 1 ↔ a = b
    both directions

    direction
    assume a + 1 = b + 1                                              (D1)

    1.1.  a = (a + 1) − 1
          algebra

    1.2.  a = (b + 1) − 1
          substitute a + 1 = b + 1 (D1) into line 1.1

    1.3.  (b + 1) − 1 = b
          algebra

    1.4.  a = b
          calculation
          a = (b + 1) − 1       1.2
            = b                 1.3

    direction
    assume a = b                                                      (D2)

    1.2.  a + 1 = b + 1
          substitute a = b (D2)
"
            .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out =
        checker::run_edited(&tree, &["proofs/wiedijk/twice.proof".to_string()]).printed;
    assert!(out.contains("step 1.2 is numbered twice"), "{out}");
    assert!(out.contains("\n1 problem(s)\n"), "{out}");
}

/// A hypothesis two lines supply, a cited H2 and a requires line saying the
/// same, is reported as said twice, and neither line as asked for nothing:
/// the item does ask for it, and one of the two is enough.
#[test]
fn a_hypothesis_supplied_twice_is_said_once() {
    let clean = clean();
    let case = case(
        "supply one hypothesis by a cited line and a requires line",
        vec![edit(
            "proofs/wiedijk/twice.proof",
            None,
            "\
import mundane theorem    stdlib/numbers/quotient-positive

theorem twice
  let M ∈ ℝ                                                           (H1)
  assume M > 0                                                        (H2)
  then 1/M > 0

1.  1/M > 0
    mun:quotient-positive x := 1, y := M, from H2
    requires 0 < 1: arithmetic
    requires 0 < M: inequalities, from H2
"
            .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out =
        checker::run_edited(&tree, &["proofs/wiedijk/twice.proof".to_string()]).printed;
    assert!(
        out.contains(
            "step 1 supplies one hypothesis of mun:quotient-positive twice, by H2 and the requires line 0 < M; one of them is enough"
        ),
        "{out}"
    );
    assert!(!out.contains("asks for nothing it says"), "{out}");
    assert!(
        !out.contains("nor the step's other lines ask for it"),
        "{out}"
    );
}

/// An operation `arithmetic` does not work out is named once for the
/// sentence, however often the sentence writes it.
#[test]
fn an_operation_arithmetic_does_not_work_out_is_named_once() {
    let clean = clean();
    let case = case(
        "write a floor twice in an arithmetic step",
        vec![edit(
            "proofs/wiedijk/twice.proof",
            None,
            "theorem twice\n  then ⌊1/2⌋ = ⌊1/2⌋\n\n1.  ⌊1/2⌋ = ⌊1/2⌋\n    arithmetic\n"
                .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out =
        checker::run_edited(&tree, &["proofs/wiedijk/twice.proof".to_string()]).printed;
    assert_eq!(out.matches("works out floor").count(), 1, "{out}");
}

/// A requires line whose fact the step's own citation gives is not repeated
/// where a line below needs it: the line below sees only its reason and the
/// lines above it (R2). Here reals-uncountable's step 3.5 cites line 3.1,
/// which says N(k + 1) = 10·N(k) + d(k + 1), and `N(k + 1) ∈ ℝ: membership`
/// below asks that of the line above it.
#[test]
fn a_line_the_step_cites_may_be_restated_for_a_line_below() {
    let clean = clean();
    let case = case(
        "restate a fact the step cites, for a requires line below",
        vec![edit(
            "proofs/wiedijk/reals-uncountable.proof",
            Some(
                "\
          transitivity, from 3.4, 3.1
          requires N(k) ∈ ℝ: membership, from 2
          requires d(k + 1) ∈ ℝ: membership, from H1, 3.2
"
                .to_string(),
            ),
            "\
          transitivity, from 3.4, 3.1
          requires N(k) ∈ ℝ: membership, from 2
          requires d(k + 1) ∈ ℝ: membership, from H1, 3.2
          requires N(k + 1) = 10·N(k) + d(k + 1): from 3.1
          requires N(k + 1) ∈ ℝ: membership, from H1, 2, 3.2
"
            .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = checked_planted(&case, &tree);
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

#[test]
fn the_checker_catches_every_planted_defect() {
    let clean = clean();
    let base = checker::run(&clean);
    assert!(
        base.printed.contains("\n0 problem(s)\n"),
        "the corpus is not clean, so a planted defect proves nothing:\n{}",
        base.printed
    );
    let cases = cases();
    let results = in_order_slots(
        SLOTS,
        &cases,
        || clean_read(&clean),
        |read, case| outcome(case, &clean, read),
    );
    let missed = results.iter().filter(|(_, missed, _)| *missed).count();
    let said: Vec<&str> = results.iter().map(|(line, _, _)| line.as_str()).collect();
    println!("{}", said.join("\n"));
    println!(
        "\n{} caught, {missed} missed, of {} planted defects",
        cases.len() - missed,
        cases.len()
    );
    assert_eq!(missed, 0, "{}", said.join("\n"));
    // Every message the checker writes is said by some case, or none can be
    // planted, and the list below says why.
    let every = messages();
    let unsaid: Vec<String> = every
        .iter()
        .filter(|m| !results.iter().any(|(_, _, out)| m.said_in(out)))
        .map(|m| m.words.join(" … "))
        .collect();
    let known: Vec<String> = UNPLANTED.iter().map(|(w, _)| w.to_string()).collect();
    let new: Vec<&String> = unsaid.iter().filter(|u| !known.contains(u)).collect();
    let gone: Vec<&String> = known.iter().filter(|k| !unsaid.contains(k)).collect();
    println!(
        "\n{} messages, {} said by no case, of which {} cannot be planted",
        every.len(),
        unsaid.len(),
        known.len()
    );
    assert!(
        new.is_empty() && gone.is_empty(),
        "messages no case says:\n{}\n\nmessages listed as unplanted that a case says, or no longer written:\n{}",
        new.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n"),
        gone.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
}

/// A case's edits checked against the clean corpus read once report what
/// they report read afresh, word for word.
#[test]
fn a_clean_reading_kept_reports_what_a_fresh_one_does() {
    let clean = clean();
    let cases = cases();
    let differ = in_order_slots(
        SLOTS,
        &cases,
        || clean_read(&clean),
        |read, case| kept_unlike_fresh(case, &clean, read),
    );
    let differ: Vec<String> = differ.into_iter().flatten().collect();
    assert!(differ.is_empty(), "{}", differ.join("\n\n"));
}

/// What a case's edits report against the clean corpus read once and read
/// afresh, where the two differ.
fn kept_unlike_fresh(case: &Case, clean: &Memory, read: &Clean) -> Option<String> {
    let tree = plant(case, clean).ok()?;
    let edited: Vec<String> = case.edits.iter().map(|e| e.file.to_string()).collect();
    let kept = read.run_edited(&tree, &edited).printed;
    let fresh = checker::run_edited(&tree, &edited).printed;
    (kept != fresh)
        .then(|| format!("{}\n  kept:\n{kept}\n  fresh:\n{fresh}", case.name))
}

/// The checker's messages no planted edit can make it say, by their words
/// as `messages` reads them, each with why.
const UNPLANTED: &[(&str, &str)] = &[
    (
        "cannot be read: ",
        "a file the source cannot read at all; an edit writes text, which reads",
    ),
    (
        "let  …  stands below every step, where no step uses it",
        "the parser refuses a let below a theorem's last step first",
    ),
    (
        ", which no define in scope carries",
        "only a define by recursion has no one name, and the parser refuses one outside the theorem that uses it, where `recursion_cited` reads it first",
    ),
];

fn cases() -> Vec<Case> {
    let mut all = Vec::new();
    all.extend(structure::cases());
    all.extend(imports::cases());
    all.extend(library::cases());
    all.extend(reading::cases());
    all.extend(citations::cases());
    all.extend(defines::cases());
    all.extend(calculations::cases());
    all.extend(methods::cases());
    all.extend(numbers::cases());
    all.extend(geometry::cases());
    all
}
