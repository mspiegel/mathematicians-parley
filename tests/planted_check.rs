//! The checker catches things.
//!
//! Each case takes the corpus, makes one edit that should be a defect, and
//! requires that the checker report it. A checker that passes a clean corpus
//! proves nothing on its own; this is the half that matters.
//!
//! The corpus is read once into memory and each case edits it through an
//! overlay of its own, so no case copies a directory and none can see
//! another's edit. The cases run on as many threads as the machine has, and
//! are reported in the order they are written. The tool itself runs on one.

use std::path::Path;

use parley::source::{Disk, Memory, Overlay, Source};

/// A file that defines a function outside its theorems, for the cases below
/// that import it, use it, or define its name again.
const TRI: &str = "define T(k) := k(k + 1)/2, for k ∈ ℕ                                  (D1)\n       reads the k-th triangular number\n\ntheorem tri-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    calculation\n      T(1) = 1(1 + 1)/2        D1\n           = 1                 arithmetic\n";

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

/// The corpus as it stands: the database, the library, and every proof.
fn clean() -> Memory {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap()
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

/// What one case says, and whether it missed: its edit could not be planted,
/// or the checker did not report it.
fn outcome(case: &Case, clean: &Memory) -> (String, bool) {
    let tree = match plant(case, clean) {
        Ok(tree) => tree,
        Err(why) => return (why, true),
    };
    let out = parley::check::run(&tree).printed;
    if out.contains(case.expect) {
        return (format!("  caught        {}", case.name), false);
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
    )
}

/// `run` over every case, several at once, given back in the cases' order.
///
/// A case reads the clean corpus and writes only its own overlay, and the
/// checker it runs is its own, so the cases share nothing that changes. Each
/// thread takes the next case not yet taken, which keeps them all busy when
/// some cases cost far more than others.
fn in_parallel<T: Send>(cases: &[Case], run: impl Fn(&Case) -> T + Sync) -> Vec<T> {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Mutex;
    let next = AtomicUsize::new(0);
    let done: Mutex<Vec<Option<T>>> = Mutex::new(cases.iter().map(|_| None).collect());
    let workers = std::thread::available_parallelism().map_or(1, |n| n.get());
    std::thread::scope(|scope| {
        for _ in 0..workers.min(cases.len()) {
            scope.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::Relaxed);
                let Some(case) = cases.get(i) else { break };
                let result = run(case);
                done.lock().unwrap()[i] = Some(result);
            });
        }
    });
    done.into_inner()
        .unwrap()
        .into_iter()
        .map(|r| r.expect("every case was run"))
        .collect()
}

#[test]
fn the_checker_catches_every_planted_defect() {
    let clean = clean();
    let base = parley::check::run(&clean);
    assert!(
        base.printed.contains("\n0 problem(s)\n"),
        "the corpus is not clean, so a planted defect proves nothing:\n{}",
        base.printed
    );
    let cases = cases();
    let results = in_parallel(&cases, |case| outcome(case, &clean));
    let missed = results.iter().filter(|(_, missed)| *missed).count();
    let said: Vec<&str> = results.iter().map(|(line, _)| line.as_str()).collect();
    println!("{}", said.join("\n"));
    println!(
        "\n{} caught, {missed} missed, of {} planted defects",
        cases.len() - missed,
        cases.len()
    );
    assert_eq!(missed, 0, "{}", said.join("\n"));
}

fn cases() -> Vec<Case> {
    vec![
        // Definitions outside a theorem, and definitions imported.
        case(
            "import a definition from a file that is not there",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/nonesuch/W (D8)\n\ntheorem cantor\n".to_string()),
            ],
            "names no proof file",
        ),
        case(
            "import a definition the file does not define",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/W (D8)\n\ntheorem cantor\n".to_string()),
            ],
            "defines no W outside its theorems",
        ),
        case(
            "import a definition and never use it",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T (D8)\n\ntheorem cantor\n".to_string()),
            ],
            "imports definition T and never uses it",
        ),
        // A definition imported is cited by its label, as one defined is.
        case(
            "import a definition without a label",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "import definition proofs/tri/T carries no label",
        ),
        case(
            "label an imported definition as a theorem labels a line",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import proof proofs/tri\nimport definition proofs/tri/T (H1)\n\ntheorem use-one\n  let n ∈ ℕ                                                           (H1)\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:proofs/tri/tri-one\n".to_string()),
            ],
            "label H1 is already a define's outside theorem use-one",
        ),
        // A library function is declared on its definition, and nowhere else:
        // take the declaration away and the name is three letters again.
        case(
            "write gcd where the library declares no such function",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("  function    gcd(_, _)\n".to_string()), String::new()),
            ],
            "'d divides gcd(a, b)' has 7 token(s) left over, starting at 'c'",
        ),
        case(
            "let a function of the proof's take a library function's name",
            vec![
                edit("proofs/bezout.proof", Some("  metamath    bezout\n".to_string()), "  metamath    bezout\n  let gcd : ℕ → ℕ                                                     (H9)\n".to_string()),
            ],
            "gcd is the library's function, def:stdlib/divisibility/gcd; name this function something else",
        ),
        case(
            "define a function of the proof's with a library function's name",
            vec![
                edit("proofs/tri.proof", None, TRI.replacen("define T(k)", "define C(k)", 1)),
            ],
            "C is the library's function, def:stdlib/counting/binomial-coefficient; name this function something else",
        ),
        case(
            "import a function under a library function's name",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T as C (D8)\n\ntheorem cantor\n".to_string()),
            ],
            "C is the library's function, def:stdlib/counting/binomial-coefficient; name this function something else",
        ),
        case(
            "name a library function with a word a notation writes",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("  function    gcd(_, _)\n".to_string()), "  function    divides(_, _)\n".to_string()),
            ],
            "'divides' is a word a notation writes, so it cannot also name a function",
        ),
        // Every name on the page is a letter, so a longer name is several.
        case(
            "define a function with a name of several letters",
            vec![
                edit("proofs/tri.proof", None, TRI.replacen("define T(k)", "define tri(k)", 1)),
            ],
            "a define names one letter, perhaps with a subscript or a prime, and 'tri' is not one",
        ),
        case(
            "import a definition under a name of several letters",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T as tri (D8)\n\ntheorem cantor\n".to_string()),
            ],
            "a definition is imported under one letter, perhaps with a subscript or a prime, and 'tri' is not one",
        ),
        case(
            "define one name twice outside the theorems",
            vec![
                edit("proofs/tri.proof", None, format!("{TRI}{}", "\ndefine T(k) := k, for k ∈ ℕ                                          (D2)\n       reads k itself\n")),
            ],
            "T is already defined at line",
        ),
        case(
            "define a name the file also imports",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import proof proofs/tri\nimport definition proofs/tri/T (D2)\n\ndefine T(k) := k, for k ∈ ℕ                                          (D1)\n       reads k itself\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:proofs/tri/tri-one\n".to_string()),
            ],
            "T is already defined at line",
        ),
        case(
            "define inside a proof a name the file defines outside it",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "define B := {1}                                                    (D9)\n       reads the set holding 1\n\ntheorem cantor\n".to_string()),
            ],
            "B is already defined outside theorem cantor",
        ),
        case(
            "use a definition above the line that defines it",
            vec![
                edit("proofs/tri.proof", None, "define T(k) := k(k + 1)/2, for k ∈ ℕ                                  (D1)\n       reads the k-th triangular number\n\ntheorem tri-one\n  then T(1) = 1 + U(0)\n\n1.  T(1) = 1\n    calculation\n      T(1) = 1(1 + 1)/2        D1\n           = 1                 arithmetic\n\ndefine U(k) := k, for k ∈ ℕ                                          (D2)\n       reads k itself\n".to_string()),
            ],
            "U is defined at line 12, below theorem tri-one; a definition is used only below where it is written",
        ),
        // A plain name above its define parses, as a letter nobody introduced.
        case(
            "use a plain definition above the line that defines it",
            vec![
                edit("proofs/early.proof", None, "theorem early-use\n  then c = 5\n\n1.  c = 5\n    arithmetic\n\ndefine c := 5                                                         (D1)\n       reads five\n".to_string()),
            ],
            "c is defined at line 7, below theorem early-use",
        ),
        // A cited theorem's T is its own file's T, and a file with a T of its
        // own cannot cite it as one about that.
        case(
            "cite a theorem about another file's T as one about the file's own",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-own.proof", None, "import proof proofs/tri\n\ndefine T(k) := k·k, for k ∈ ℕ                                         (D1)\n       reads the square of k\n\ntheorem own-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:proofs/tri/tri-one\n".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "cite a line inside a block that has closed",
            vec![
                edit("proofs/intermediate-value.proof", Some("    17.2.  c < b\n           inequalities, from 12, 17.1".to_string()), "    17.2.  c < b\n           inequalities, from 12, 17.1.1".to_string()),
            ],
            "inside a block that has closed",
        ),
        case(
            "cite a line that does not exist",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    3.5.  p is even\n          thm:even-square n := p, from 3.1, 3.4".to_string()), "    3.5.  p is even\n          thm:even-square n := p, from 3.1, 3.99".to_string()),
            ],
            "does not exist",
        ),
        case(
            "cite the assumption of another case",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    2.6.  −x ≤ |x|\n          inequalities, from 2.5".to_string()), "    2.6.  −x ≤ |x|\n          inequalities, from 2.5, C1".to_string()),
            ],
            "not in scope",
        ),
        case(
            "a justification that matches no production",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("3.  (2k + 1)² = 4k² + 4k + 1\n    algebra".to_string()), "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra from 1 and 2".to_string()),
            ],
            "matches no production",
        ),
        case(
            "point at an item that is not in the database",
            vec![
                edit("proofs/cantor.proof", Some("    thm:stdlib/sets/set-builder-subset, from D1".to_string()), "    thm:stdlib/sets/set-builder-nonesuch, from D1".to_string()),
            ],
            "resolves to no item",
        ),
        case(
            "point at a library file that does not exist",
            vec![
                edit("proofs/cantor.proof", Some("    thm:stdlib/sets/set-builder-subset, from D1".to_string()), "    thm:stdlib/nonesuch/set-builder-subset, from D1".to_string()),
            ],
            "resolves to no item",
        ),
        case(
            "cite an item of another file by its bare name",
            vec![
                edit("proofs/cantor.proof", Some("    thm:stdlib/sets/set-builder-subset, from D1".to_string()), "    thm:set-builder-subset, from D1".to_string()),
            ],
            "names no theorem of this file",
        ),
        case(
            "use def: for something that is a theorem",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("          requires n² ∈ ℤ: thm:stdlib/numbers/int-closure, from H1".to_string()), "          requires n² ∈ ℤ: def:stdlib/numbers/int-closure, from H1".to_string()),
            ],
            "names a theorem",
        ),
        case(
            "number a step under a parent that does not exist",
            vec![
                edit("proofs/cantor.proof", Some("1.  B ⊆ A\n    thm:stdlib/sets/set-builder-subset, from D1".to_string()), "1.9.4.  B ⊆ A\n    thm:stdlib/sets/set-builder-subset, from D1".to_string()),
            ],
            "does not exist",
        ),
        case(
            "use a part marker the method does not declare",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    case\n    assume x ≥ 0".to_string()), "    base\n    assume x ≥ 0".to_string()),
            ],
            "is not one of the parts",
        ),
        case(
            "instantiate an item instead of a line",
            vec![
                edit("proofs/intermediate-value.proof", Some("    instantiate u := b in line 9, from H2, 7".to_string()), "    instantiate u := b in def:stdlib/calculus/least-upper-bound, from H2, 7".to_string()),
            ],
            "never an item",
        ),
        case(
            "a character that is in no notation record",
            vec![
                edit("proofs/sum-formula.proof", Some("= 1(1 + 1)/2            arithmetic".to_string()), "= 1(1 ⊕ 1)/2            arithmetic".to_string()),
            ],
            "is in no record",
        ),
        // U+2208 followed by a combining solidus looks like the not-an-element sign
        // and composes to it under NFC, so it is the decomposed form the rule bans.
        case(
            "text that is not in Normalisation Form C",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("3.  √2 ∉ ℚ".to_string()), "3.  √2 ∈\u{0338} ℚ".to_string()),
            ],
            "Normalisation Form C",
        ),
        case(
            "an item that says nothing about where it comes from",
            vec![
                edit("corpus/stdlib/sets.records", Some("theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath    pw0".to_string()), "theorem powerset-empty\n  then        𝒫∅ = {∅}".to_string()),
            ],
            "neither which set.mm label",
        ),
        case(
            "a block whose method takes none",
            vec![
                edit("proofs/sum-formula.proof", Some("                  requires k ∈ ℝ: from K\n".to_string()), "                  requires k ∈ ℝ: from K\n\n                  1.3.3.1.  k = k\n                            algebra\n".to_string()),
            ],
            "takes no block",
        ),
        case(
            "a contradiction whose block does not suppose anything",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    contradiction\n    suppose √2 ∈ ℚ                                                    (S)".to_string()), "    contradiction".to_string()),
            ],
            "does not open with `suppose`",
        ),
        case(
            "cite another proof file without importing it",
            vec![
                edit("proofs/intermediate-value.proof", Some("import proof proofs/triangle-inequality\n".to_string()), "".to_string()),
            ],
            "proofs/triangle-inequality is not imported",
        ),
        // An import says what it brings in, a proof file or a definition.
        case(
            "import without saying what is imported",
            vec![
                edit("proofs/intermediate-value.proof", Some("import proof proofs/triangle-inequality\n".to_string()), "import proofs/triangle-inequality\n".to_string()),
            ],
            "an import says `import proof <file>`",
        ),
        case(
            "import a proof file and cite nothing from it",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import proof proofs/bezout\n\ntheorem cantor\n".to_string()),
            ],
            "imports proofs/bezout and cites nothing from it",
        ),
        case(
            "cite a library file without importing it",
            vec![
                edit("proofs/cantor.proof", Some("import proof stdlib/reasoning\n".to_string()), String::new()),
            ],
            "and stdlib/reasoning is not imported",
        ),
        case(
            "import a library file nothing cites",
            vec![
                edit("proofs/cantor.proof", Some("import proof stdlib/sets\n".to_string()), "import proof stdlib/sets\nimport proof stdlib/geometry\n".to_string()),
            ],
            "imports stdlib/geometry and cites nothing from it",
        ),
        case(
            "import a library file that is not there",
            vec![
                edit("proofs/cantor.proof", Some("import proof stdlib/sets\n".to_string()), "import proof stdlib/sets\nimport proof stdlib/nonesuch\n".to_string()),
            ],
            "import stdlib/nonesuch names no library file",
        ),
        case(
            "import a file that is not there",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import proof proofs/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "import proofs/nonesuch names no proof file",
        ),
        case(
            "import the same file twice",
            vec![
                edit("proofs/intermediate-value.proof", Some("import proof proofs/triangle-inequality\n".to_string()), "import proof proofs/triangle-inequality\nimport proof proofs/triangle-inequality\n".to_string()),
            ],
            "proofs/triangle-inequality is imported twice",
        ),
        case(
            "a proof file that imports itself",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import proof proofs/cantor\n\ntheorem cantor\n".to_string()),
            ],
            "proofs/cantor imports itself",
        ),
        case(
            "two proof files that import each other",
            vec![
                edit("proofs/triangle-inequality.proof", Some("theorem abs-bounds\n".to_string()), "import proof proofs/intermediate-value\n\ntheorem abs-bounds\n".to_string()),
            ],
            "closes a cycle",
        ),
        case(
            "two theorems of one name in one file",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("theorem even-square\n".to_string()), "theorem odd-square\n".to_string()),
            ],
            "theorem odd-square is already proved",
        ),
        case(
            "two items of one name in one library file",
            vec![
                edit("corpus/stdlib/sets.records", Some("theorem powerset-empty\n".to_string()), "theorem powerset-monotone\n".to_string()),
            ],
            "theorem powerset-monotone is already defined",
        ),
        case(
            "an item stated outside the standard library",
            vec![
                edit("corpus/db/methods.records", Some("method algebra\n".to_string()), "theorem stray\n  then        P\n  metamath    exmid\n\nmethod algebra\n".to_string()),
            ],
            "stray is outside stdlib/",
        ),
        case(
            "a theorem field said twice",
            vec![
                edit("proofs/cantor.proof", Some("  metamath    canth\n".to_string()), "  metamath    canth\n  metamath    canth\n".to_string()),
            ],
            "says metamath twice",
        ),
        case(
            "a let line that asserts instead of introducing",
            vec![
                edit("proofs/cantor.proof", Some("  let A be a set                                                      (H1)".to_string()), "  let A = B                                                           (H1)".to_string()),
            ],
            "none of the 10 introductions",
        ),
        // Renaming the isosceles points to a and n makes the distance |an| spell
        // the declared word `an`, which is what the capital-letter convention has
        // been quietly preventing.
        case(
            "two names run together into a declared word",
            vec![
                edit("proofs/isosceles.proof", Some("1.  |AC| = |CA|".to_string()), "1.  |an| = |CA|".to_string()),
            ],
            "run together",
        ),
        // Line 4 of bezout binds s, so substituting a term naming s would capture.
        case(
            "substitute a term that captures a bound variable",
            vec![
                edit("proofs/bezout.proof", Some("          instantiate s := a·x + b·y in line 4, from 8.2".to_string()), "          instantiate s := a·x + b·s in line 4, from 8.2".to_string()),
            ],
            "may not capture",
        ),
        // The same, with a comma inside the value: the pair is read whole.
        case(
            "substitute a term with a comma that captures a bound variable",
            vec![
                edit("proofs/bezout.proof", Some("          instantiate s := a·x + b·y in line 4, from 8.2".to_string()), "          instantiate s := gcd(s, b) in line 4, from 8.2".to_string()),
            ],
            "may not capture",
        ),
        case(
            "obtain a name without stating its sort",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2".to_string()), "1.  n = 2k + 1.\n    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2".to_string()),
            ],
            "without stating its sort",
        ),
        case(
            "write a claim in a notation nobody declared",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("5.  p > 1\n    def:stdlib/divisibility/prime p := p, from 4".to_string()), "5.  p exceeds 1\n    def:stdlib/divisibility/prime p := p, from 4".to_string()),
            ],
            "token(s) left over",
        ),
        case(
            "write a formula that reads two ways because nothing says what a name is",
            vec![
                edit("proofs/subsets.proof", Some("1.2.1.5.  |T| = 2^k".to_string()), "1.2.1.5.  |W| = 2^k".to_string()),
            ],
            "'|W| = 2^k' reads as absolute-value or as cardinality, and nothing says what W is",
        ),
        case(
            "drop a line a citation needs for a hypothesis",
            vec![
                edit("proofs/intermediate-value.proof", Some("    def:stdlib/calculus/interval x := a, from H1, H2".to_string()), "    def:stdlib/calculus/interval x := a, from H1".to_string()),
            ],
            "does not supply them",
        ),
        case(
            "supply a hypothesis with the wrong number system",
            vec![
                edit("proofs/geometric-series.proof", Some("thm:stdlib/numbers/exponent-zero a := a, from H1".to_string()), "thm:stdlib/numbers/exponent-zero a := a, from H3".to_string()),
            ],
            "does not supply them",
        ),
        case(
            "stop declaring which pattern is a negation of which",
            vec![
                edit("corpus/db/notation.records", Some("  level       predicate\n  negates     pattern 3 is logical-not of pattern 2".to_string()), "  level       predicate".to_string()),
            ],
            "does not supply them",
        ),
        case(
            "drop a hole from the term a notation builds",
            vec![
                edit("corpus/db/notation.records", Some("  target      _1 _2 caddc co, _1 _2 cmin co".to_string()), "  target      _1 _1 caddc co, _1 _2 cmin co".to_string()),
            ],
            "leaves a hole out",
        ),
        case(
            "leave a notation without the sort its holes take",
            vec![
                edit("corpus/db/notation.records", Some("  pattern     _ is prime\n  sort        number → formula\n".to_string()), "  pattern     _ is prime\n".to_string()),
            ],
            "notation prime has no `sort` saying what its holes take and what it yields",
        ),
        case(
            "give a notation a sort for more holes than its pattern has",
            vec![
                edit("corpus/db/notation.records", Some("  pattern     _ is prime\n  sort        number → formula\n".to_string()), "  pattern     _ is prime\n  sort        number, number → formula\n".to_string()),
            ],
            "notation prime has a sort for 2 hole(s) but its pattern(s) have [1]",
        ),
        case(
            "write a binder whose binds line does not read",
            vec![
                edit("corpus/db/notation.records", Some("  binds       hole 1 over nothing".to_string()), "  binds       hole 1 above nothing".to_string()),
            ],
            "is not `hole N over hole M`",
        ),
        case(
            "give a notation fewer targets than it has patterns",
            vec![
                edit("corpus/db/notation.records", Some("  target      _1 _2 cmul co, _1 _2 cdiv co".to_string()), "  target      _1 _2 cmul co".to_string()),
            ],
            "target entr",
        ),
        case(
            "point a requires line at an item that does not cover it",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    requires n² ∈ ℤ: thm:stdlib/numbers/int-closure, from H1".to_string()), "    requires n² ∈ ℤ: thm:stdlib/numbers/int-real, from H1".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "drop the dull fact a requires line leans on",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    requires 2 ∈ ℤ: arithmetic\n".to_string()), "".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "claim something the cited item does not conclude",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("5.  p > 1\n    def:stdlib/divisibility/prime p := p, from 4".to_string()), "5.  p > 2\n    def:stdlib/divisibility/prime p := p, from 4".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "stop declaring that juxtaposition is the product",
            vec![
                edit("corpus/db/notation.records", Some("  assoc       left\n  spells      multiplicative ·".to_string()), "  assoc       left".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "stop saying which variable the braces bind",
            vec![
                edit("corpus/stdlib/sets.records", Some("  then        u ∈ {t ∈ X : P(t)} ↔ u ∈ X and P(u)".to_string()), "  then        t ∈ {t ∈ X : P(t)} ↔ t ∈ X and P(t)".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "say a property is a function into a formula",
            vec![
                edit("corpus/stdlib/sets.records", Some("theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P : X → formula                                                 (H2)".to_string()),
            ],
            "which is a sort and not a set",
        ),
        // A define with an argument is a function, and a function is defined
        // somewhere: its rule alone says what it does and not where.
        case(
            "define a function and give no domain",
            vec![
                edit("proofs/cantor.proof", Some("define B := {x ∈ A : x ∉ f(x)}".to_string()), "define B(y) := {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "says no domain",
        ),
        // S is defined on ℕ, so what it is applied to is a number.
        case(
            "apply a defined function outside its domain's sort",
            vec![
                edit("proofs/sum-formula.proof", Some("1.  S(n) = n(n + 1)/2".to_string()), "1.  S({n}) = n(n + 1)/2".to_string()),
            ],
            "a set of numbers where a number is wanted",
        ),
        case(
            "give a domain to a define that takes no argument",
            vec![
                edit("proofs/cantor.proof", Some("define B := {x ∈ A : x ∉ f(x)}".to_string()), "define B := {x ∈ A : x ∉ f(x)}, for y ∈ A".to_string()),
            ],
            "gives a domain and takes no argument",
        ),
        case(
            "define a name and never say what it means",
            vec![
                edit("proofs/cantor.proof", Some("       reads the members of A that their own image leaves out\n".to_string()), "".to_string()),
            ],
            "carries no `reads` line",
        ),
        case(
            "note a step that opens no block",
            vec![
                edit("proofs/cantor.proof", Some("1.  B ⊆ A\n    thm:stdlib/sets/set-builder-subset, from D1".to_string()), "1.  B ⊆ A\n    thm:stdlib/sets/set-builder-subset, from D1\n    note this is where B becomes a part".to_string()),
            ],
            "opens no block",
        ),
        // An item's summand is whatever the sum it concludes sums, read where the
        // sum applies it to what it binds, and every other use of it must agree.
        case(
            "sum over a range the item does not conclude",
            vec![
                edit("proofs/divisibility-by-three.proof", Some("2.  3 divides Σ(k = 0 to n) (d(k)·10^k − d(k))".to_string()), "2.  3 divides Σ(k = 1 to n) (d(k)·10^k − d(k))".to_string()),
            ],
            "step 2 claims something that thm:stdlib/sums/sum-divisible does not conclude",
        ),
        case(
            "read an item's summand two ways",
            vec![
                edit("proofs/divisibility-by-three.proof", Some("= Σ(k = 0 to n) d(k)·10^k − Σ(k = 0 to n) d(k)\n    thm:stdlib/sums/sum-difference".to_string()), "= Σ(k = 0 to n) d(k) − Σ(k = 0 to n) d(k)\n    thm:stdlib/sums/sum-difference".to_string()),
            ],
            "step 3 claims something that thm:stdlib/sums/sum-difference does not conclude",
        ),
        // A congruence is a divisibility of a difference, and which way round
        // the difference goes is part of what is said.
        case(
            "turn a congruence round",
            vec![
                edit("proofs/divisibility-by-three.proof", Some("    1.1.  10^k ≡ 1 (mod 3)\n          thm:ten-power-congruent".to_string()), "    1.1.  1 ≡ 10^k (mod 3)\n          thm:ten-power-congruent".to_string()),
            ],
            "step 1.1 claims something that thm:ten-power-congruent does not conclude",
        ),
        case(
            "note a case part after its assumption",
            vec![
                edit("proofs/subsets.proof", Some("          note V is a subset without a, with a put back\n          assume a ∈ V                                                (C1)".to_string()), "          assume a ∈ V                                                (C1)\n          note V is a subset without a, with a put back".to_string()),
            ],
            "directly under its marker",
        ),
        case(
            "note a case part twice",
            vec![
                edit("proofs/subsets.proof", Some("          note V is a subset without a, with a put back\n".to_string()), "          note V is a subset without a, with a put back\n          note V holds a\n".to_string()),
            ],
            "already carries a note",
        ),
        case(
            "suppose something unrelated to the claim",
            vec![
                edit("proofs/bezout.proof", Some("3.  r = 0\n    contradiction\n    suppose not r = 0".to_string()), "3.  r = 0\n    contradiction\n    suppose not r ≤ 0".to_string()),
            ],
            "neither expansion of `contradiction` applies",
        ),
        case(
            "end a contradiction block without a contradiction",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("    6.8.  p = 1. not p = 1.".to_string()), "    6.8.  p = 1. p = 1.".to_string()),
            ],
            "does not state a formula and that formula negated",
        ),
        case(
            "write a word predicate under a bare not",
            vec![
                edit("corpus/stdlib/geometry.records", Some("              not (P, Q, R are collinear)".to_string()), "              not P, Q, R are collinear".to_string()),
            ],
            "P is a point, and `_, _` wants a statement",
        ),
        case(
            "state an item in a notation nobody declared",
            vec![
                edit("corpus/stdlib/sets.records", Some("theorem subset-transitive\n  assume X ⊆ Y".to_string()), "theorem subset-transitive\n  assume X is within Y".to_string()),
            ],
            "theorem subset-transitive",
        ),
        case(
            "leave the name in an item statement with no sort",
            vec![
                edit("corpus/stdlib/sets.records", Some("theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "theorem set-builder-subset\n  let X be a set                                                      (H1)".to_string()),
            ],
            "theorem set-builder-subset",
        ),
        case(
            "introduce a symbol and say nothing it stands for",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr\n  then        x is irrational".to_string()),
            ],
            "says nothing it stands for",
        ),
        case(
            "define a term and name no symbol for it",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "names no symbol for it",
        ),
        case(
            "introduce a symbol nothing writes",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "cannot be reached",
        ),
        case(
            "introduce a symbol in more than one token",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  symbol      irr ational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "is not one token",
        ),
        case(
            "introduce one symbol from two definitions",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()), "definition irrational\n  symbol      dup\n  defines     cr\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ\n\ndefinition twice\n  symbol      dup\n  defines     cq\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()),
            ],
            "is already introduced by",
        ),
        case(
            "state a field twice, which reads as one field joined",
            vec![
                edit("corpus/stdlib/numbers.records", Some("definition irrational\n  then        x is irrational".to_string()), "definition irrational\n  target      eldif\n  then        x is irrational".to_string()),
            ],
            "a second time",
        ),
        // A field is read by its name, so a misspelt one is not the field: the
        // Archimedean item would have no target, and Theorem 13's citation of it
        // would be taken as stated.
        case(
            "misspell a field name",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  target      nnrecl\n".to_string()), "  taget       nnrecl\n".to_string()),
            ],
            "theorem archimedean has a field 'taget', which a theorem record does not have",
        ),
        // Everything a citation names does work. Line 1 says a + b ∈ ℝ, which
        // is what `thm:stdlib/numbers/nonneg-or-neg` asks; H1 says a ∈ ℝ, which
        // it does not.
        case(
            "cite a line the cited item asks nothing of",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    thm:stdlib/numbers/nonneg-or-neg x := a + b, from 1\n".to_string()), "    thm:stdlib/numbers/nonneg-or-neg x := a + b, from 1, H1\n".to_string()),
            ],
            "step 2 cites H1, and thm:stdlib/numbers/nonneg-or-neg asks for nothing it says",
        ),
        // A "there is" given by an instance is given only where the instance is
        // in the domain. Bezout's step 2 puts a in S by exhibiting 1 and 0, and
        // without `requires 1 ∈ ℤ` the 1 could be anything.
        case(
            "exhibit a witness without saying it is in the domain",
            vec![
                edit("proofs/bezout.proof", Some("    def:stdlib/sets/set-builder u := a, from H1, 1\n    requires 1 ∈ ℤ: arithmetic\n".to_string()), "    def:stdlib/sets/set-builder u := a, from H1, 1\n".to_string()),
            ],
            "step 2 claims something that def:stdlib/sets/set-builder does not conclude",
        ),
        // A sort is stated once, like a declared type, and a step does not cite
        // it to rely on it (`READERS.md`): citing one names a line that does no
        // work.
        case(
            "cite the line that says what sort of thing a name is",
            vec![
                edit("proofs/isosceles.proof", Some("    thm:stdlib/geometry/distance-symmetric P := A, Q := C\n".to_string()), "    thm:stdlib/geometry/distance-symmetric P := A, Q := C, from H1\n".to_string()),
            ],
            "step 1 cites H1, and thm:stdlib/geometry/distance-symmetric asks for nothing it says",
        ),
        // An obtain names its item after the word `obtain`, and the checks that
        // read an item citation read only a step the item heads. The three
        // below went unreported.
        case(
            "obtain from an item without what it asks for",
            vec![
                edit("proofs/intermediate-value.proof", Some("    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7".to_string()), "    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 7".to_string()),
            ],
            "step 8 cites thm:stdlib/calculus/completeness, which asks for",
        ),
        case(
            "obtain from an item and cite a line it does not ask for",
            vec![
                edit("proofs/intermediate-value.proof", Some("    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7".to_string()), "    obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7, H3".to_string()),
            ],
            "step 8 cites H3, and thm:stdlib/calculus/completeness asks for nothing it says",
        ),
        // An item with no target is assumed as it states itself. This one said
        // |X| = k + 1 without saying what k was, and at k = −1 and X = ∅ the
        // axiom it became was false.
        case(
            "leave open a name an item uses as a number",
            vec![
                edit("corpus/stdlib/counting.records", Some("theorem card-nonempty\n  let X be a set                                                      (H1)\n  let k ∈ ℕ₀                                                          (H2)\n".to_string()), "theorem card-nonempty\n  let X be a set                                                      (H1)\n".to_string()),
            ],
            "theorem card-nonempty: k stands where a number goes",
        ),
        // A set's sort says what it holds, and the page never writes it
        // (`READERS.md`); the checker reads it off the text. A sort that said
        // only "a set" would see none of the three below.
        case(
            "put a set of numbers inside a set of sets of numbers",
            vec![
                edit("proofs/intermediate-value.proof", Some("3.  S ⊆ [a, b]\n".to_string()), "3.  S ⊆ 𝒫[a, b]\n".to_string()),
            ],
            "𝒫: a set of sets of numbers where a set of numbers is wanted",
        ),
        case(
            "say an element of a set of numbers is a set",
            vec![
                edit("proofs/intermediate-value.proof", Some("    6.1.  s ∈ [a, b]\n          def:stdlib/sets/set-builder, from K1\n".to_string()), "    6.1.  s ∈ [a, b]\n          def:stdlib/sets/set-builder, from K1\n          requires s is a set: from K1\n".to_string()),
            ],
            "the requires line of step 6.1: 's is a set': s is a number, and `_ is a set` wants a set",
        ),
        // A set declared of any sort stays of any sort. `let a be a set` makes
        // add-element-bijection's X a set of sets, and subsets-count, whose X
        // is a set of any sort, cites it: the counting proof would hold of
        // sets of sets only, and nothing would say so.
        // A citation checks what a proof's names are and does not say it:
        // the elaborator reads a proof's sorts from its own lines, so a name
        // only a citation settles would read differently there.
        case(
            "leave a name's sort to a citation",
            vec![
                edit("proofs/cites.proof", None, "theorem only-cited\n  then c = c\n\n1.  c = c\n    thm:stdlib/numbers/int-real m := c\n".to_string()),
            ],
            "citing stdlib/numbers/int-real with m := c: only the citation says c is a number; say so where c is introduced",
        ),
        case(
            "cite a statement that narrows a set of any sort",
            vec![
                edit("proofs/subsets.proof", Some("  let a ∉ X                                                           (H2)\n".to_string()), "  let a ∉ X                                                           (H2)\n  let a be a set                                                      (H3)\n".to_string()),
            ],
            "citing proofs/subsets/add-element-bijection with X := X ∖ {a}: a set of things of any sort (X)",
        ),
        case(
            "obtain from a definition without the line it unfolds",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    obtain k: def:stdlib/divisibility/odd n := n, from H1, H2".to_string()), "    obtain k: def:stdlib/divisibility/odd n := n, from H1".to_string()),
            ],
            "step 1 obtains from def:stdlib/divisibility/odd, which says there is one only from",
        ),
        // Pascal's rule pairs C(n, k) with C(n, k − 1). The other neighbour is
        // the mistake a reader makes when the index shift goes the wrong way.
        case(
            "Pascal with the shift going the wrong way",
            vec![
                edit("proofs/binomial.proof", Some("    44.5.  C(m, k) + C(m, k − 1) = C(m + 1, k)\n".to_string()), "    44.5.  C(m, k) + C(m, k + 1) = C(m + 1, k)\n".to_string()),
            ],
            "step 44.5 claims something that thm:stdlib/counting/pascal does not conclude",
        ),
        // Shifting the index moves the range with it.
        case(
            "a shifted sum left over the range it came from",
            vec![
                edit("proofs/binomial.proof", Some("24. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 + 1 to m + 1)".to_string()), "24. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 to m)".to_string()),
            ],
            "step 24 claims something that thm:stdlib/sums/sum-shift does not conclude",
        ),
        // A line saying something of every index from 0 to m says nothing of
        // the index m + 1, which the sum to m + 1 takes.
        case(
            "a term-by-term line over too short a range",
            vec![
                edit("proofs/binomial.proof", Some("    thm:stdlib/sums/sum-termwise a := 0, b := m + 1, from 44\n".to_string()), "    thm:stdlib/sums/sum-termwise a := 0, b := m + 1, from 5\n".to_string()),
            ],
            "step 45 cites thm:stdlib/sums/sum-termwise, which asks for",
        ),
        // C(n, k) is zero above n, and C(m + 1, m + 1) is not above it.
        case(
            "a coefficient called zero where k is not above n",
            vec![
                edit("proofs/binomial.proof", Some("    thm:stdlib/counting/binomial-above n := m, k := m + 1, from H3, 1, 7".to_string()), "    thm:stdlib/counting/binomial-above n := m + 1, k := m + 1, from H3, 1, 7".to_string()),
            ],
            "step 8 cites thm:stdlib/counting/binomial-above, which asks for",
        ),
        // Four blocks of binomial-step each fix k under the label J, and J means
        // what the block around the citing step says: here k runs from 1. Read
        // theorem-wide, J was the last block's, from 0, and this edit passed.
        case(
            "a label read as a sibling block's",
            vec![
                edit("proofs/binomial.proof", Some("thm:stdlib/sums/range-integer a := 1, b := m + 1, from J\n           requires 1 ∈ ℤ: arithmetic\n".to_string()), "thm:stdlib/sums/range-integer a := 0, b := m + 1, from J\n           requires 0 ∈ ℤ: arithmetic\n".to_string()),
            ],
            "step 26.1 cites thm:stdlib/sums/range-integer, which asks for",
        ),
        // `arithmetic` may stand where a closed-numeral fact is used, and only
        // there: an equation with a letter in it gives a reader something to
        // check, and is a numbered step. `SYNTAX.md` has the rule.
        case(
            "take an equation with a letter in it from arithmetic",
            vec![
                edit("proofs/binomial.proof", Some("substitute (m + 1) − 0 = m + 1 (line 31)".to_string()), "substitute (m + 1) − 0 = m + 1 (arithmetic)".to_string()),
            ],
            "takes (m + 1) − 0 = m + 1 from arithmetic, and it has a letter in it",
        ),
        case(
            "a chain link with a letter in it naming arithmetic",
            vec![
                edit("proofs/sum-formula.proof", Some("= (k + 1)((k + 1) + 1)/2       1.3.4".to_string()), "= (k + 1)((k + 1) + 1)/2       arithmetic".to_string()),
            ],
            "names arithmetic for",
        ),
        // Steps count 1, 2, 3 in the order they are written: a reader meeting 8
        // after 6 looks for a 7 that is not there.
        case(
            "a gap in the numbering",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("7.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()), "8.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()),
            ],
            "numbers run on without gaps",
        ),
        // `membership` claims a term is in a number system and nothing else.
        case(
            "membership named for a claim that is no membership",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          thm:stdlib/sums/sum-termwise a := 1, b := n, from 1\n".to_string()), "    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          membership, from 1\n".to_string()),
            ],
            "names membership for",
        ),
        // A line said of every k ∈ ℕ answers a hypothesis over {1, …, n}, and not
        // one over {0, …, n}: the table puts the first range inside ℕ and not
        // the second.
        case(
            "a for-every line over a set that does not hold the range",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          thm:stdlib/sums/sum-termwise a := 1, b := n, from 1\n".to_string()), "    2.1.  Σ(k = 0 to n) 1/T(k) = Σ(k = 0 to n) (2/k − 2/(k + 1))\n          thm:stdlib/sums/sum-termwise a := 0, b := n, from 1\n".to_string()),
            ],
            "step 2.1 cites thm:stdlib/sums/sum-termwise, which asks for",
        ),
        // What a summand's function hypothesis asks is the membership of the
        // names the summand is built from, and 1 is none of them.
        case(
            "a requires line the summand does not ask for",
            vec![
                edit("proofs/binomial.proof", Some("    thm:stdlib/sums/sum-real a := 0, b := m\n    requires 0 ∈ ℤ: arithmetic\n".to_string()), "    thm:stdlib/sums/sum-real a := 0, b := m\n    requires 1 ∈ ℤ: arithmetic\n    requires 0 ∈ ℤ: arithmetic\n".to_string()),
            ],
            "says 1 ∈ ℤ, and neither thm:stdlib/sums/sum-real nor",
        ),
        // A hypothesis asking a = b is answered by a line saying b = a, and by
        // nothing else: line 2 says |CB| = |BC|, which is neither way round the
        // |CB| = |CA| side-angle-side asks for.
        case(
            "answer an equation with one that says it neither way round",
            vec![
                edit("proofs/isosceles.proof", Some("      from 5, 6, 3, 4, H5\n".to_string()), "      from 5, 6, 3, 4, 2\n".to_string()),
            ],
            "step 7 cites thm:stdlib/geometry/side-angle-side, which asks for",
        ),
        // A step citing a define by cases says which case it is in, by a line
        // giving the condition or its negation, and claims that case's value.
        case(
            "cite a define by cases for the other case's value",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("    3.6.  h(t) = g⁻¹(t)\n".to_string()), "    3.6.  h(t) = f(t)\n".to_string()),
            ],
            "step 3.6 cites D2 and claims a value it does not give",
        ),
        case(
            "cite a define by cases from no line saying the case",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("          D2, from 3.1\n".to_string()), "          D2, from K1\n".to_string()),
            ],
            "no line it cites says whether a case's condition holds",
        ),
        case(
            "cite a define for a claim that does not name it",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("    3.6.  h(t) = g⁻¹(t)\n".to_string()), "    3.6.  g⁻¹(t) = g⁻¹(t)\n".to_string()),
            ],
            "step 3.6 cites D2 and its claim never names h",
        ),
        // A `let` names a function's type and nothing more, unless `be` says a
        // property of it; a property slipped in as the codomain went unasked.
        case(
            "state a property in a let line as the codomain",
            vec![
                edit("corpus/stdlib/functions.records", Some("  let g : Y → X be one-to-one ".to_string()), "  let g : Y → X is one-to-one ".to_string()),
            ],
            "says more than a function's type",
        ),
        // What `be` says of a function is asked for, as a membership is.
        case(
            "cite an item without the line saying its function is one-to-one",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("          thm:stdlib/functions/inverse-value, from H4, 3.5\n".to_string()), "          thm:stdlib/functions/inverse-value, from 3.5\n".to_string()),
            ],
            "step 3.7 cites thm:stdlib/functions/inverse-value, which asks for",
        ),
        // An image's points come from a part of the function's domain, and the
        // item asks the step to say it is one.
        case(
            "cite a value in an image with nothing saying the set is in the domain",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("                  thm:stdlib/functions/value-in-image, from K2\n                  requires C ⊆ A: from 2\n".to_string()), "                  thm:stdlib/functions/value-in-image, from K2\n".to_string()),
            ],
            "step 4.1.3 cites thm:stdlib/functions/value-in-image, which asks for",
        ),
        // An obtain states what its name is, and ⊆ says it of a part as ∈ 𝒫
        // would; with neither the name's sort is left to be inferred.
        case(
            "obtain a part without saying what it is a part of",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("2.  C ⊆ A. g[B ∖ f[C]] = A ∖ C.\n".to_string()), "2.  g[B ∖ f[C]] = A ∖ C.\n".to_string()),
            ],
            "step 2 obtains C without stating its sort",
        ),
        // Two sets sharing nothing keep a member of one out of the other, and
        // the member is asked for: here a is dropped.
        case(
            "keep a point out of a disjoint set without saying it is in the other",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("                  thm:stdlib/sets/disjoint-member, from 7.2.2, K7\n".to_string()), "                  thm:stdlib/sets/disjoint-member, from 7.2.2\n".to_string()),
            ],
            "step 7.2.3 cites thm:stdlib/sets/disjoint-member, which asks for",
        ),
        // A group is let with its operation and its identity; one without the
        // identity is no introduction at all.
        case(
            "let a group without naming its identity",
            vec![
                edit("proofs/lagrange.proof", Some("let G be a finite group with operation · and identity e".to_string()), "let G be a finite group with operation ·".to_string()),
            ],
            "is none of the 10 introductions",
        ),
        // gH is read as the coset only of a part of the group, and the step
        // says H is one.
        case(
            "read a coset without saying H lies in G",
            vec![
                edit("proofs/lagrange.proof", Some("          def:stdlib/groups/coset u := g, from K3, 5.1, 5.2\n          requires H ⊆ G: from 1\n".to_string()), "          def:stdlib/groups/coset u := g, from K3, 5.1, 5.2\n".to_string()),
            ],
            "step 5.3 cites def:stdlib/groups/coset, which asks for H ⊆ G",
        ),
        // An equation names a witness read either way round, and only so: g
        // is in gH as g = g·h for some h ∈ H, and e·g = g fits that neither
        // way.
        case(
            "name a coset witness by an equation that does not fit either way",
            vec![
                edit("proofs/lagrange.proof", Some("    5.2.  g·e = g\n".to_string()), "    5.2.  e·g = g\n".to_string()),
            ],
            "step 5.3 claims something that def:stdlib/groups/coset does not conclude",
        ),
        // A claim may bind another letter than the definition it reads, and says
        // the same thing only where the letter it binds is the one it uses: with
        // b bound and a free, gH = aH is a claim about a, and 12.3 reads K's
        // condition from it.
        case(
            "read a definition with a bound letter the claim does not use",
            vec![
                edit("proofs/lagrange.proof", Some("    12.2. There is a ∈ G with gH = aH.\n".to_string()), "    12.2. There is b ∈ G with gH = aH.\n".to_string()),
            ],
            "step 12.3 claims something that def:stdlib/sets/part-builder does not conclude",
        ),
        // K binds g, and read at gH it is `there is a ∈ G with gH = aH`: the g
        // of gH is not caught by K's. So the sentence written with it caught
        // says something else, and does not put gH in K.
        case(
            "read a definition at a term its bound letter would catch",
            vec![
                edit("proofs/lagrange.proof", Some("    12.2. There is a ∈ G with gH = aH.\n".to_string()), "    12.2. There is g ∈ G with gH = gH.\n".to_string()),
            ],
            "step 12.3 claims something that def:stdlib/sets/part-builder does not conclude",
        ),
        // An obtain from part-builder finds its "there is" in the condition of
        // the set the cited line puts Y in; K20 says only x ∈ Y ∩ Z.
        case(
            "obtain from part-builder citing no line that puts the set in it",
            vec![
                edit("proofs/lagrange.proof", Some("obtain a: def:stdlib/sets/part-builder, from K18".to_string()), "obtain a: def:stdlib/sets/part-builder, from K20".to_string()),
            ],
            "step 15.1 obtains from def:stdlib/sets/part-builder, which says there is one only from something the step does not cite",
        ),
        // Counting by parts asks that two parts which meet be one part.
        case(
            "count by parts without saying they do not overlap",
            vec![
                edit("proofs/lagrange.proof", Some("from H1, 14, 15, 16, 3".to_string()), "from H1, 14, 16, 3".to_string()),
            ],
            "step 17 cites thm:stdlib/counting/partition-count, which asks for",
        ),
        // A define by recursion gives each name a value at 0 and a rule at the
        // step, the rule naming the sequences only at k, and a citation of it
        // says which case it is in and that the index is one the rule covers.
        case(
            "define a sequence with no value at 0",
            vec![
                edit("proofs/euclid.proof", Some("define a(0) := M,  b(0) := N,".to_string()), "define a(0) := M,".to_string()),
            ],
            "b has no value at 0",
        ),
        case(
            "give a sequence its first value at 1",
            vec![
                edit("proofs/euclid.proof", Some("define a(0) := M,  b(0) := N,".to_string()), "define a(0) := M,  b(1) := N,".to_string()),
            ],
            "b(1) is neither b(0) nor b(k + 1)",
        ),
        case(
            "write a step rule that names the value it defines",
            vec![
                edit("proofs/euclid.proof", Some("  a(k + 1) := a(k)             if b(k) = 0".to_string()), "  a(k + 1) := a(k + 1)         if b(k) = 0".to_string()),
            ],
            "names a at a place other than k",
        ),
        case(
            "write a step rule that names the index itself",
            vec![
                edit("proofs/euclid.proof", Some("  a(k + 1) := a(k)             if b(k) = 0".to_string()), "  a(k + 1) := a(k) + k         if b(k) = 0".to_string()),
            ],
            "names k outside a value at k",
        ),
        case(
            "give a first value in terms of a sequence",
            vec![
                edit("proofs/euclid.proof", Some("define a(0) := M,  b(0) := N,".to_string()), "define a(0) := b(0),  b(0) := N,".to_string()),
            ],
            "names b, which has no value before 0",
        ),
        case(
            "cite a step rule without saying the index is in ℕ₀",
            vec![
                edit("proofs/euclid.proof", Some("3.1.9.2.2.  b(j + 1) = 0\n                                        D1, from C1\n                                        requires j ∈ ℕ₀: from J".to_string()), "3.1.9.2.2.  b(j + 1) = 0\n                                        D1, from C1".to_string()),
            ],
            "no line it cites says the index is in ℕ₀",
        ),
        case(
            "claim the value of the other case",
            vec![
                edit("proofs/euclid.proof", Some("3.1.9.2.1.  a(j + 1) = a(j)".to_string()), "3.1.9.2.1.  a(j + 1) = b(j)".to_string()),
            ],
            "step 3.1.9.2.1 cites D1 and claims a value it does not give",
        ),
        case(
            "cite a step rule by cases without saying which case",
            vec![
                edit("proofs/euclid.proof", Some("3.1.9.2.13. b(j + 1) = a(j) mod b(j)\n                                        D1, from C2".to_string()), "3.1.9.2.13. b(j + 1) = a(j) mod b(j)\n                                        D1".to_string()),
            ],
            "says whether a case's condition holds",
        ),
        // A calculation's link cites the line that says it, and a line saying
        // a(0) = M does not say what substituting it inside a gcd gives.
        case(
            "cite an equation for a link that substitutes it inside a term",
            vec![
                edit("proofs/euclid.proof", Some("                    gcd(a(0), b(0)) = gcd(M, b(0))     3.1.3".to_string()), "                    gcd(a(0), b(0)) = gcd(M, b(0))     1".to_string()),
            ],
            "cites 1, which does not say gcd(a(0), b(0)) = gcd(M, b(0))",
        ),
        case(
            "define a sequence by recursion outside any theorem",
            vec![
                edit("proofs/euclid.proof", Some("theorem euclid".to_string()), "define c(0) := 1, c(k + 1) := c(k), for k ∈ ℕ₀                     (D9)\n       reads a constant sequence\n\ntheorem euclid".to_string()),
            ],
            "is written in the theorem that uses it",
        ),
        // Levels the precedence order leaves unrelated need brackets whichever
        // side each stands on: a trailing "for all" takes one relation, and
        // "and" and "or" are not ordered against each other.
        case(
            "write a trailing for all over an and",
            vec![
                edit("proofs/cantor.proof", Some("3.  There exists B ⊆ A such that f(x) ≠ B for all x ∈ A.".to_string()), "3.  There exists B ⊆ A such that f(x) ≠ B and x ∈ A for all x ∈ A.".to_string()),
            ],
            "`and` and `for all` are not ordered against each other",
        ),
        // The universal is written "for all"; "for every" is no spelling of it.
        case(
            "write for every where for all is meant",
            vec![
                edit("proofs/cantor.proof", Some("2.  For all x ∈ A, f(x) ≠ B.".to_string()), "2.  For every x ∈ A, f(x) ≠ B.".to_string()),
            ],
            "for-all does not fit",
        ),
        case(
            "mix and with or without brackets",
            vec![
                edit("proofs/cantor.proof", Some("          2.1.1.  x ∈ B or x ∉ B".to_string()), "          2.1.1.  x ∈ B or x ∉ B and x ∈ A".to_string()),
            ],
            "`or` and `and` are not ordered against each other",
        ),
        // A quantifier may write a bound where its set stands, "for all ε >
        // 0", only where the statement says what the letter ranges over.
        case(
            "write a bound in place of a set nothing declares",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("  ε ranges over ℝ\n".to_string()), String::new()),
            ],
            "nothing says what set ε belongs to",
        ),
        case(
            "write a bound in place of a set in an item that declares none",
            vec![
                edit("corpus/stdlib/calculus.records", Some("  ε, δ range over ℝ\n".to_string()), String::new()),
            ],
            "nothing says what set δ belongs to",
        ),
        case(
            "let a declared letter be in another set",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    let ε ∈ ℝ ".to_string()), "    let ε ∈ ℚ ".to_string()),
            ],
            "the statement says ε ranges over ℝ, and this line puts it in ℚ",
        ),
        case(
            "declare a letter's range twice",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("  n ranges over ℕ\n".to_string()), "  n ranges over ℕ\n  n ranges over ℤ\n".to_string()),
            ],
            "the statement already says what n ranges over",
        ),
        case(
            "declare a range no quantifier leans on",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("  n ranges over ℕ\n".to_string()), "  n ranges over ℕ\n  x ranges over ℝ\n".to_string()),
            ],
            "the statement says what x ranges over, and no quantifier leaves x's set out",
        ),
        case(
            "declare a range over something that is not a set",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("  ε ranges over ℝ\n".to_string()), "  ε ranges over 2\n".to_string()),
            ],
            "'2' is not a set, so nothing can range over it",
        ),
    ]
}
