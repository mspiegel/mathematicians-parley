//! The checker catches things.
//!
//! Each case takes the corpus, makes one edit that should be a defect, and
//! requires that the checker report it. A checker that passes a clean corpus
//! proves nothing on its own; this is the half that matters.
//!
//! The corpus is read once into memory and each case edits it through an
//! overlay of its own, so no case copies a directory and none can see
//! another's edit. The clean corpus is checked whole; a case checks the
//! theorems its edits can reach (`check::run_edited`). The cases run side by
//! side (`threads::in_order`), and are reported in the order they are
//! written.

use std::path::Path;

use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::in_order;

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
    // Only what the edits reach is checked: a case passes only where its
    // problem is reported, and a theorem left unchecked can only leave a
    // problem out.
    let edited: Vec<String> = case.edits.iter().map(|e| e.file.to_string()).collect();
    let out = parley::check::run_edited(&tree, &edited).printed;
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

/// A file that does not import the library's C may give the letter to a
/// function of its own: the library function is in scope only where it is
/// imported.
#[test]
fn a_file_that_does_not_import_a_library_function_may_use_its_name() {
    let clean = clean();
    let case = case(
        "import a function as C where the library's C is not imported",
        vec![
            edit("proofs/tri.proof", None, TRI.to_string()),
            edit(
                "proofs/tri-use.proof",
                None,
                "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T as C\n\ntheorem use-one\n  then C(1) = 1\n\n1.  C(1) = 1\n    thm:tri-one\n".to_string(),
            ),
        ],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::check::run(&tree).printed;
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
        vec![edit("proofs/quotient.proof", None, QUOTIENT.to_string())],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::check::run(&tree).printed;
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

/// A requires line whose fact the step's own citation gives is not repeated
/// where a line below needs it: the line below sees only its reason and the
/// lines above it (R2). Here the birthday problem's step 8 cites line 1,
/// which says {1, …, 23} is finite, and `|{1, …, 23}| ∈ ℕ₀: mun:card-nat0`
/// below asks that of the line above it.
#[test]
fn a_line_the_step_cites_may_be_restated_for_a_line_below() {
    let clean = clean();
    let case = case(
        "restate a fact the step cites, for a requires line below",
        vec![edit(
            "proofs/birthday.proof",
            Some(
                "\
    inequalities, from 3, 4
    requires |{1, …, 23}| ∈ ℕ₀: mun:card-nat0, from 1
"
                .to_string(),
            ),
            "\
    inequalities, from 3, 4, 1
    requires {1, …, 23} is finite: from 1
    requires |{1, …, 23}| ∈ ℕ₀: mun:card-nat0, from 1
"
            .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::check::run(&tree).printed;
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
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
    let results = in_order(&cases, || (), |_, case| outcome(case, &clean));
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
        // A letter is written only where something introduced it, and a
        // `for all` introduces its letter to the end of its sentence only.
        case(
            "write a for-all's letter in the sentence after it",
            vec![edit(
                "proofs/reals-uncountable.proof",
                Some("4.  For all k ∈ ℕ₀, L(k) ∈ ℝ and U(k) ∈ ℝ and L(k) ≤ U(k).".to_string()),
                "4.  For all k ∈ ℕ₀, L(k) ∈ ℝ. U(k) ∈ ℝ. L(k) ≤ U(k).".to_string(),
            )],
            "k is not introduced here; a `for all` binds its letter only to the end of its sentence",
        ),
        case(
            "write a letter nothing introduces",
            vec![edit(
                "proofs/euler.proof",
                Some("2.  {0, …, n − 1} ⊆ ℤ".to_string()),
                "2.  {0, …, m − 1} ⊆ ℤ".to_string(),
            )],
            "m is not introduced here",
        ),
        // Definitions outside a theorem, and definitions imported.
        case(
            "import a definition from a file that is not there",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/nonesuch/W\n\ntheorem cantor\n".to_string()),
            ],
            "names no proof file",
        ),
        // A step said of every member is the item applied at one: what the
        // item concludes there has to be the claim's body, and what it asks
        // there has to be supplied, by the member's domain or by a line.
        case(
            "say of every member what the item does not conclude at one",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("2.  For all k ∈ {1, …, n}, a(k)² ≥ 0.".to_string()),
                "2.  For all k ∈ {1, …, n}, a(k)² > 0.".to_string(),
            )],
            "claims something that mun:square-nonneg does not conclude",
        ),
        case(
            "say of every member what the item asks a line for, citing none",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("    mun:square-nonneg x := a(k), from H2\n".to_string()),
                "    mun:square-nonneg x := a(k)\n".to_string(),
            )],
            "asks for x ∈ ℝ",
        ),
        // A function's type says its value is in the codomain only at a point
        // of its domain, so the line putting k in {1, …, n} is cited with it.
        case(
            "cite a function's type for a value without the point's domain",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("mun:square-zero x := a(k), from 5.3.1, H2, K4".to_string()),
                "mun:square-zero x := a(k), from 5.3.1, H2".to_string(),
            )],
            "asks for x ∈ ℝ",
        ),
        case(
            "import a definition the file does not define",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/W\n\ntheorem cantor\n".to_string()),
            ],
            "defines no W outside its theorems",
        ),
        case(
            "import a definition and never use it",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "imports definition T and never uses it",
        ),
        // Every define is imported as a definition, whether or not it takes
        // an argument.
        case(
            "import a define that takes an argument as a function",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import theorem proofs/tri/tri-one\nimport function proofs/tri/T\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import function: an import says the header of the item it names",
        ),
        // An imported define's label is what a line writing it out cites, and
        // is given only where a line does.
        case(
            "label an imported definition no line writes out",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T (D2)\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "import definition proofs/tri/T gives the label D2, which no line cites",
        ),
        case(
            "write out an imported definition its import gives no label",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import definition proofs/tri/T\n\ntheorem use-two\n  then T(2) = 3\n\n1.  T(2) = 3\n    calculation\n      T(2) = 2(2 + 1)/2        T\n           = 3                 arithmetic\n".to_string()),
            ],
            "T is the define import definition proofs/tri/T brings in, which a line cites by a label its import gives, as `(D1)`: add one",
        ),
        case(
            "label an imported definition as a theorem labels a line",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/tri-use.proof", None, "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T (H1)\n\ntheorem use-one\n  let n ∈ ℕ                                                           (H1)\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "label H1 is already a define's outside theorem use-one",
        ),
        // A library function is declared by its record, and nowhere else:
        // give the record another name and gcd is three letters again.
        case(
            "write gcd where the library declares no such function",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("mundane definition gcd\n".to_string()), "mundane definition gcdx\n".to_string()),
            ],
            "'d divides gcd(a, b)' has 7 token(s) left over, starting at 'c'",
        ),
        case(
            "let a function of the proof's take a library function's name",
            vec![
                edit("proofs/bezout.proof", Some("              gcd(a, b) ≤ d.\n".to_string()), "              gcd(a, b) ≤ d.\n  let gcd : ℕ → ℕ                                                     (H9)\n".to_string()),
            ],
            "gcd is the library's function, mun:stdlib/divisibility/gcd, which this file imports; name this function something else",
        ),
        // A file that imports a library function may not give its name to a
        // function of its own; one that does not import it may.
        case(
            "define a function of the proof's with an imported library function's name",
            vec![
                edit("proofs/tri.proof", None, format!("import definition stdlib/counting/C\n\n{}", TRI.replacen("define T(k)", "define C(k)", 1))),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        case(
            "import a function under the name of an imported library function",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/counting/C\nimport definition proofs/tri/T as C\n\ntheorem cantor\n".to_string()),
            ],
            "C is the library's function, def:stdlib/counting/C, which this file imports; name this function something else",
        ),
        // A library function is in scope where it is imported, by its name,
        // from the library file that declares it.
        case(
            "apply a library function the file does not import",
            vec![
                edit("proofs/bezout.proof", Some("import mundane definition stdlib/divisibility/gcd\n".to_string()), String::new()),
            ],
            "gcd is the library's function mun:stdlib/divisibility/gcd, and this file does not import it: write `import mundane definition stdlib/divisibility/gcd`",
        ),
        case(
            "import a library function from a file that does not declare it",
            vec![
                edit("proofs/bezout.proof", Some("import mundane definition stdlib/divisibility/gcd\n".to_string()), "import mundane definition stdlib/numbers/gcd\n".to_string()),
            ],
            "import mundane definition stdlib/numbers/gcd: stdlib/numbers holds no item gcd",
        ),
        // A library function is imported as its record's mark or kind says,
        // as any library item is.
        case(
            "import a mundane library function as a definition",
            vec![
                edit("proofs/bezout.proof", Some("import mundane definition stdlib/divisibility/gcd\n".to_string()), "import definition stdlib/divisibility/gcd\n".to_string()),
            ],
            "import definition stdlib/divisibility/gcd: stdlib/divisibility/gcd is a mundane definition; import it as `import mundane definition stdlib/divisibility/gcd`",
        ),
        // An item's name may open with a Greek letter, as σ's does, and is
        // imported from the file that holds it like any other.
        case(
            "import a Greek-named item from a file that does not hold it",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition stdlib/numbers/σ\n\ntheorem cantor\n".to_string()),
            ],
            "import definition stdlib/numbers/σ: stdlib/numbers holds no item σ",
        ),
        case(
            "import a name that is no item's name",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/numbers/σ₁\n\ntheorem cantor\n".to_string()),
            ],
            "import mundane theorem stdlib/numbers/σ₁: 'σ₁' is not an item's name",
        ),
        case(
            "import a definition by a subscripted name the file does not define",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T₁\n\ntheorem cantor\n".to_string()),
            ],
            "defines no T₁ outside its theorems",
        ),
        case(
            "import a library function the file never applies",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane definition stdlib/numbers/max\n\ntheorem cantor\n".to_string()),
            ],
            "imports max and never applies it",
        ),
        case(
            "import a library function with a label",
            vec![
                edit("proofs/bezout.proof", Some("import mundane definition stdlib/divisibility/gcd\n".to_string()), "import mundane definition stdlib/divisibility/gcd (D9)\n".to_string()),
            ],
            "import mundane definition stdlib/divisibility/gcd: only a define of a proof file carries a label",
        ),
        case(
            "import a library function under another name",
            vec![
                edit("proofs/bezout.proof", Some("import mundane definition stdlib/divisibility/gcd\n".to_string()), "import mundane definition stdlib/divisibility/gcd as hcf\n".to_string()),
            ],
            "a library function is imported by its name alone, with no `as`",
        ),
        case(
            "name a library function with a word a notation writes",
            vec![
                edit("corpus/stdlib/divisibility.records", Some("mundane definition gcd\n".to_string()), "mundane definition divides\n".to_string()),
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
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import definition proofs/tri/T as tri\n\ntheorem cantor\n".to_string()),
            ],
            "a define is imported under one letter, perhaps with a subscript or a prime, and 'tri' is not one",
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
                edit("proofs/tri-use.proof", None, "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T (D2)\n\ndefine T(k) := k, for k ∈ ℕ                                          (D1)\n       reads k itself\n\ntheorem use-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
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
                edit("proofs/tri-own.proof", None, "import theorem proofs/tri/tri-one\n\ndefine T(k) := k·k, for k ∈ ℕ                                         (D1)\n       reads the square of k\n\ntheorem own-one\n  then T(1) = 1\n\n1.  T(1) = 1\n    thm:tri-one\n".to_string()),
            ],
            "does not conclude",
        ),
        case(
            "cite a line inside a block that has closed",
            vec![
                edit("proofs/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.1.1".to_string()),
            ],
            "inside a block that has closed",
        ),
        case(
            "cite a line that does not exist",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    2.5.  p is even\n          thm:even-square n := p, from 2.4".to_string()), "    2.5.  p is even\n          thm:even-square n := p, from 2.99".to_string()),
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
            "import an item that is not in the database",
            vec![
                edit("proofs/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-nonesuch\n".to_string()),
                edit("proofs/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:set-builder-nonesuch, from D1".to_string()),
            ],
            "import mundane theorem stdlib/sets/set-builder-nonesuch: stdlib/sets holds no item set-builder-nonesuch",
        ),
        case(
            "import an item from a library file that does not exist",
            vec![
                edit("proofs/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/nonesuch/set-builder-subset\n".to_string()),
            ],
            "import mundane theorem stdlib/nonesuch/set-builder-subset: stdlib/nonesuch is no file",
        ),
        case(
            "cite an item the file does not import",
            vec![
                edit("proofs/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:subset-transitive, from D1".to_string()),
            ],
            "mun:subset-transitive is neither imported nor a theorem of this file",
        ),
        // An import says where an item comes from, so a citation does not.
        case(
            "cite an item by its path",
            vec![
                edit("proofs/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:stdlib/sets/set-builder-subset, from D1".to_string()),
            ],
            "mun:stdlib/sets/set-builder-subset is cited by its path",
        ),
        case(
            "use def: for something that is mundane",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    mun:even-or-odd n := n\n".to_string()), "    def:even-or-odd n := n\n".to_string()),
            ],
            "def:even-or-odd names a mundane",
        ),
        case(
            "cite a mundane item as a theorem",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    mun:even-or-odd n := n\n".to_string()), "    thm:even-or-odd n := n\n".to_string()),
            ],
            "thm:even-or-odd names a mundane",
        ),
        case(
            "cite an axiom as a theorem",
            vec![
                edit("proofs/intermediate-value.proof", Some("obtain c: axi:completeness".to_string()), "obtain c: thm:completeness".to_string()),
            ],
            "thm:completeness names an axiom",
        ),
        case(
            "number a step under a parent that does not exist",
            vec![
                edit("proofs/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.9.4.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()),
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
                edit("proofs/intermediate-value.proof", Some("    instantiate u := b in line 9, from 7".to_string()), "    instantiate u := b in mun:least-upper-bound, from 7".to_string()),
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
                edit("proofs/sqrt2-irrational.proof", Some("2.  √2 ∉ ℚ".to_string()), "2.  √2 ∈\u{0338} ℚ".to_string()),
            ],
            "Normalisation Form C",
        ),
        case(
            "an item that says nothing about where it comes from",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n  then        𝒫∅ = {∅}\n  metamath    pw0".to_string()), "mundane theorem powerset-empty\n  then        𝒫∅ = {∅}".to_string()),
            ],
            "neither which set.mm label",
        ),
        case(
            "a block whose method takes none",
            vec![
                edit("proofs/sum-formula.proof", Some("    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra\n".to_string()), "    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra\n\n          1.6.1.  k = k\n                  algebra\n".to_string()),
            ],
            "takes no block",
        ),
        // `requires C ≠ A: mun:triangle` unfolds a line saying B, C, A form a
        // triangle; written above it, that line is what it rests on, and
        // without it nothing is.
        case(
            "unfold a triangle no line above says",
            vec![
                edit("proofs/angle-sum.proof", Some("    requires B, C, A form a triangle: mun:triangle-rotate P := A, Q := B, R := C, from H4\n".to_string()), "".to_string()),
            ],
            "the requires line of step 2 needs something that mun:triangle does not conclude",
        ),
        // A requires line's item asks for what the lines it cites supply:
        // `nat0-nonzero` asks m ≠ 0, and without C2, which says b(k) ≠ 0,
        // the line says what is missing rather than that the item concludes
        // something else.
        case(
            "a requires line whose item's hypothesis nothing supplies",
            vec![
                edit("proofs/euclid.proof", Some("thm:gcd-mod\n                   requires b(k) ∈ ℕ: mun:nat0-nonzero, from IH, C2\n".to_string()), "thm:gcd-mod\n                   requires b(k) ∈ ℕ: mun:nat0-nonzero, from IH\n".to_string()),
            ],
            "the requires line of step 3.10.17 cites mun:nat0-nonzero, which asks for m ∈ ℕ₀; m ≠ 0, and what it cites does not supply them",
        ),
        // A define of two arguments gives each one's domain in the order
        // the brackets name them (`SYNTAX.md`).
        case(
            "a define of two whose domains are out of order",
            vec![
                edit("proofs/geometric-series.proof", Some("for a ∈ ℝ, n ∈ ℕ₀".to_string()), "for n ∈ ℕ₀, a ∈ ℝ".to_string()),
            ],
            "define G(a, n) gives the domain of n",
        ),
        // An induction's step part assumes its own claim's statement, and
        // names that claim by the induction's number (`SYNTAX.md`).
        case(
            "an induction hypothesis naming another step",
            vec![
                edit("proofs/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 2 is true for k".to_string()),
            ],
            "the induction hypothesis names step 2, and the induction is step 1",
        ),
        // The hypothesis is the claim's words where they stand; written out
        // again, the step part does not say it is the induction hypothesis.
        case(
            "a step part that writes its hypothesis out",
            vec![
                edit("proofs/sum-formula.proof", Some("    assume step 1 is true for k, the induction hypothesis             (IH)".to_string()), "    assume S(k) = k(k + 1)/2                                          (IH)".to_string()),
            ],
            "the step part of step 1 does not open with `let k ∈ ℕ` and `assume step 1 is true for k, the induction hypothesis`",
        ),
        // An induction proves a statement of every k; a claim about the
        // theorem's own n leaves the step part no letter of the claim's.
        case(
            "an induction whose claim is not said for all",
            vec![
                edit("proofs/sum-formula.proof", Some("1.  For all k ∈ ℕ, S(k) = k(k + 1)/2.".to_string()), "1.  S(n) = n(n + 1)/2".to_string()),
            ],
            "step 1 is an induction whose claim does not say \"for all k ∈ X, …\"",
        ),
        case(
            "a contradiction whose block does not suppose anything",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    contradiction\n    suppose √2 ∈ ℚ                                                    (S)".to_string()), "    contradiction".to_string()),
            ],
            "does not open with `suppose`",
        ),
        case(
            "cite another proof file's theorem without importing it",
            vec![
                edit("proofs/intermediate-value.proof", Some("import theorem            proofs/triangle-inequality/abs-bounds\n".to_string()), "".to_string()),
            ],
            "thm:abs-bounds is neither imported nor a theorem of this file",
        ),
        // An import names one item, and its keyword is the kind of the item.
        case(
            "import without saying what is imported",
            vec![
                edit("proofs/intermediate-value.proof", Some("import theorem            proofs/triangle-inequality/abs-bounds\n".to_string()), "import proofs/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "an import says `import <kind> <file>/<name>`",
        ),
        case(
            "import a whole proof file",
            vec![
                edit("proofs/intermediate-value.proof", Some("import theorem            proofs/triangle-inequality/abs-bounds\n".to_string()), "import proof proofs/triangle-inequality\n".to_string()),
            ],
            "import proof: an import says the header of the item it names",
        ),
        // An item taken for granted is imported as mundane, whatever its kind,
        // and an item that is not is imported by its kind.
        // An import says its record's header: the mark and the kind both.
        case(
            "import a mundane item without its kind",
            vec![
                edit("proofs/cantor.proof", Some("import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()), "import mundane stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane: an import says the header of the item it names",
        ),
        case(
            "import a mundane item under another kind",
            vec![
                edit("proofs/cantor.proof", Some("import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()), "import mundane theorem    stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import mundane theorem stdlib/reasoning/excluded-middle: stdlib/reasoning/excluded-middle is a mundane axiom; import it as `import mundane axiom stdlib/reasoning/excluded-middle`",
        ),
        case(
            "import a proof's define as mundane",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane definition proofs/tri/T\n\ntheorem cantor\n".to_string()),
            ],
            "a proof's define is where the proof gives a name its meaning, so it is never mundane",
        ),
        case(
            "import a mundane axiom by its kind",
            vec![
                edit("proofs/cantor.proof", Some("import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()), "import axiom      stdlib/reasoning/excluded-middle\n".to_string()),
            ],
            "import axiom stdlib/reasoning/excluded-middle: stdlib/reasoning/excluded-middle is a mundane axiom",
        ),
        case(
            "import a named axiom as mundane",
            vec![
                edit("proofs/intermediate-value.proof", Some("import axiom              stdlib/calculus/completeness\n".to_string()), "import mundane axiom      stdlib/calculus/completeness\n".to_string()),
            ],
            "import mundane axiom stdlib/calculus/completeness: stdlib/calculus/completeness is an axiom",
        ),
        case(
            "cite a mundane axiom by its kind",
            vec![
                edit("proofs/cantor.proof", Some("mun:excluded-middle".to_string()), "axi:excluded-middle".to_string()),
            ],
            "axi:excluded-middle names a mundane axiom",
        ),
        case(
            "cite a mundane definition by its kind",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("obtain k: mun:odd".to_string()), "obtain k: def:odd".to_string()),
            ],
            "def:odd names a mundane definition",
        ),
        case(
            "cite a named definition as mundane",
            vec![
                edit("proofs/isosceles.proof", Some("def:congruent".to_string()), "mun:congruent".to_string()),
            ],
            "mun:congruent names a definition",
        ),
        // `mundane` is a mark before a kind, and only before a kind a proof
        // may take for granted.
        case(
            "mark a record mundane and give it no kind",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n".to_string()), "mundane powerset-empty\n".to_string()),
            ],
            "mundane powerset-empty has no kind",
        ),
        case(
            "mark a notation mundane",
            vec![
                edit("corpus/db/notation.records", Some("\nnotation ".to_string()), "\nmundane notation ".to_string()),
            ],
            "mundane notation: a notation is never cited, so nothing takes it for granted",
        ),
        case(
            "import a proof's theorem as a library kind",
            vec![
                edit("proofs/intermediate-value.proof", Some("import theorem            proofs/triangle-inequality/abs-bounds\n".to_string()), "import mundane theorem proofs/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/triangle-inequality/abs-bounds is a theorem",
        ),
        case(
            "import a theorem and cite nothing by it",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/bezout/bezout\n\ntheorem cantor\n".to_string()),
            ],
            "imports bezout and cites nothing by it",
        ),
        case(
            "cite a library item without importing it",
            vec![
                edit("proofs/cantor.proof", Some("import mundane axiom      stdlib/reasoning/excluded-middle\n".to_string()), String::new()),
            ],
            "mun:excluded-middle is neither imported nor a theorem of this file",
        ),
        case(
            "import a library item nothing cites",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive\n\ntheorem cantor\n".to_string()),
            ],
            "imports subset-transitive and cites nothing by it",
        ),
        case(
            "import from a proof file that is not there",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/nonesuch/lemma\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/nonesuch/lemma: proofs/nonesuch is no file",
        ),
        case(
            "import a theorem a proof file does not prove",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/bezout/nonesuch\n\ntheorem cantor\n".to_string()),
            ],
            "import theorem proofs/bezout/nonesuch: proofs/bezout holds no item nonesuch",
        ),
        case(
            "import the same item twice",
            vec![
                edit("proofs/intermediate-value.proof", Some("import theorem            proofs/triangle-inequality/abs-bounds\n".to_string()), "import theorem            proofs/triangle-inequality/abs-bounds\nimport theorem            proofs/triangle-inequality/abs-bounds\n".to_string()),
            ],
            "proofs/triangle-inequality/abs-bounds is imported twice",
        ),
        // Every name a file cites is distinct within it.
        case(
            "import an item under the name of a theorem of the file",
            vec![
                edit("proofs/cantor.proof", Some("import mundane theorem    stdlib/sets/set-builder-subset\n".to_string()), "import mundane theorem    stdlib/sets/set-builder-subset as cantor\n".to_string()),
                edit("proofs/cantor.proof", Some("    mun:set-builder-subset, from D1".to_string()), "    mun:cantor, from D1".to_string()),
            ],
            "cantor is already the name of theorem cantor of this file; import one of them under another name with `as`",
        ),
        case(
            "import two items under one name",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import mundane theorem stdlib/sets/subset-transitive as set-builder-subset\n\ntheorem cantor\n".to_string()),
            ],
            "set-builder-subset is already the name of the import at line",
        ),
        case(
            "a proof file that imports its own theorem",
            vec![
                edit("proofs/cantor.proof", Some("theorem cantor\n".to_string()), "import theorem proofs/cantor/cantor\n\ntheorem cantor\n".to_string()),
            ],
            "proofs/cantor/cantor is a theorem of this file, which is cited with no import",
        ),
        case(
            "two proof files that import each other",
            vec![
                edit("proofs/triangle-inequality.proof", Some("theorem abs-bounds\n".to_string()), "import theorem proofs/intermediate-value/intermediate-value\n\ntheorem abs-bounds\n".to_string()),
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
                edit("corpus/stdlib/sets.records", Some("mundane theorem powerset-empty\n".to_string()), "mundane theorem powerset-monotone\n".to_string()),
            ],
            "mundane theorem powerset-monotone is already defined",
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
            "none of the 13 introductions",
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
                edit("proofs/sqrt2-irrational.proof", Some("1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: mun:odd n := n, from H2".to_string()), "1.  n = 2k + 1.\n    obtain k: mun:odd n := n, from H2".to_string()),
            ],
            "without stating its sort",
        ),
        case(
            "write a claim in a notation nobody declared",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("4.  p > 1\n    mun:prime p := p, from 3".to_string()), "4.  p exceeds 1\n    mun:prime p := p, from 3".to_string()),
            ],
            "token(s) left over",
        ),
        case(
            "write a formula that reads two ways because nothing says what a name is",
            vec![
                edit("proofs/subsets.proof", Some("1.2.5.  |T| = 2^k".to_string()), "1.2.5.  |W| = 2^k".to_string()),
            ],
            "'|W| = 2^k' reads as absolute-value or as cardinality, and nothing says what W is",
        ),
        // `divides-difference` asks that d divide b, which line 5.2 says.
        case(
            "drop a line a citation needs for a hypothesis",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2".to_string()), "mun:divides-difference d := p, a := n! + 1, b := n!, from 3".to_string()),
            ],
            "does not supply them",
        ),
        // `mod-natural` asks b ∈ ℕ, and IH says b(k) ∈ ℕ₀: a function's
        // value is in what a line says it is in, and ℕ₀ holds 0.
        case(
            "supply a hypothesis with the wrong number system",
            vec![
                edit("proofs/euclid.proof", Some("mun:mod-natural\n                   requires b(k) ∈ ℕ: mun:nat0-nonzero, from IH, C2\n".to_string()), "mun:mod-natural, from IH\n".to_string()),
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
                edit("proofs/sqrt2-irrational.proof", Some("theorem odd-square\n".to_string()), "import mundane theorem stdlib/numbers/int-real\n\ntheorem odd-square\n".to_string()),
                edit("proofs/sqrt2-irrational.proof", Some("    requires √2 ∈ ℝ: mun:sqrt x := 2".to_string()), "    requires √2 ∈ ℝ: mun:int-real m := 2".to_string()),
            ],
            "does not conclude",
        ),
        // `requires √2 ∈ ℝ: mun:sqrt x := 2` rests on 2 ≥ 0 written above it.
        case(
            "drop the dull fact a requires line leans on",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    mun:irrational x := √2, from 2\n    requires 2 ≥ 0: arithmetic\n".to_string()), "    mun:irrational x := √2, from 2\n".to_string()),
            ],
            "the requires line of step 3 cites mun:sqrt, which asks for x ∈ ℝ; x ≥ 0, and what it cites does not supply them",
        ),
        case(
            "claim something the cited item does not conclude",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("4.  p > 1\n    mun:prime p := p, from 3".to_string()), "4.  p > 2\n    mun:prime p := p, from 3".to_string()),
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
                edit("corpus/stdlib/sets.records", Some("mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P : X → formula                                                 (H2)".to_string()),
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
                edit("proofs/sum-formula.proof", Some("2.  S(n) = n(n + 1)/2".to_string()), "2.  S({n}) = n(n + 1)/2".to_string()),
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
                edit("proofs/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.  B ⊆ A\n    mun:set-builder-subset, from D1\n    note this is where B becomes a part".to_string()),
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
            "step 2 claims something that mun:sum-divisible does not conclude",
        ),
        case(
            "read an item's summand two ways",
            vec![
                edit("proofs/divisibility-by-three.proof", Some("= Σ(k = 0 to n) d(k)·10^k − Σ(k = 0 to n) d(k)\n    mun:sum-difference".to_string()), "= Σ(k = 0 to n) d(k) − Σ(k = 0 to n) d(k)\n    mun:sum-difference".to_string()),
            ],
            "step 3 claims something that mun:sum-difference does not conclude",
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
                edit("proofs/bezout.proof", Some("3.  r = 0\n    contradiction\n    suppose r ≠ 0".to_string()), "3.  r = 0\n    contradiction\n    suppose not r ≤ 0".to_string()),
            ],
            "neither expansion of `contradiction` applies",
        ),
        case(
            "end a contradiction block without saying what it contradicts",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("inequalities, from 4, contradicting 5.6".to_string()), "inequalities, from 4".to_string()),
            ],
            "does not say which line it contradicts",
        ),
        case(
            "contradict a line that is not the claim's opposite",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("inequalities, from 4, contradicting 5.6".to_string()), "inequalities, from 4, contradicting 5.5".to_string()),
            ],
            "says it contradicts 5.5, and neither is the other negated",
        ),
        case(
            "give a method that combines letters for a fact of numerals alone",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("    requires 2 ≠ 0: arithmetic\n".to_string()), "    requires 2 ≠ 0: inequalities\n".to_string()),
            ],
            "gives inequalities for 2 ≠ 0, which has no letter in it",
        ),
        case(
            "say a step is impossible and contradict a line as well",
            vec![
                edit("proofs/reals-uncountable.proof", Some("          mun:divides-le e := 10, m := 1, from 2.3\n".to_string()), "          mun:divides-le e := 10, m := 1, from 2.3, contradicting 2.3\n".to_string()),
            ],
            "says it is impossible and contradicts a line",
        ),
        case(
            "say a claim with a letter in it is impossible",
            vec![
                edit("proofs/reals-uncountable.proof", Some("    2.4.  10 ≤ 1, which is impossible\n".to_string()), "    2.4.  10 ≤ t, which is impossible\n".to_string()),
            ],
            "says it is impossible and names t",
        ),
        case(
            "contradict a line before the end of the block",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("mun:divides-one d := p, from 5.5".to_string()), "mun:divides-one d := p, from 5.5, contradicting 5.5".to_string()),
            ],
            "only the last step of a contradiction block, a case or a proof block may do",
        ),
        case(
            "say a case is the claim when it is not",
            vec![
                edit("proofs/euclid.proof", Some("assume b(N) = 0, which is the claim".to_string()), "assume b(N) = 1, which is the claim".to_string()),
            ],
            "case C3 says it is the claim of step 6, and it is not",
        ),
        case(
            "say a case with steps is the claim",
            vec![
                edit("proofs/euclid.proof", Some("assume b(N) ≠ 0                                                   (C4)".to_string()), "assume b(N) ≠ 0, which is the claim                               (C4)".to_string()),
            ],
            "case C4 is the claim and has steps of its own",
        ),
        case(
            "say a line is the claim outside any cases block",
            vec![
                edit("proofs/cantor.proof", Some("suppose f(x) = B                                            (S)".to_string()), "suppose f(x) = B, which is the claim                        (S)".to_string()),
            ],
            "a line saying it is the claim outside any `cases` block",
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
                edit("corpus/stdlib/sets.records", Some("mundane theorem subset-transitive\n  assume X ⊆ Y".to_string()), "mundane theorem subset-transitive\n  assume X is within Y".to_string()),
            ],
            "mundane theorem subset-transitive",
        ),
        case(
            "leave the name in an item statement with no sort",
            vec![
                edit("corpus/stdlib/sets.records", Some("mundane theorem set-builder-subset\n  let X be a set                                                      (H1)\n  let P be a property of the elements of X                            (H2)".to_string()), "mundane theorem set-builder-subset\n  let X be a set                                                      (H1)".to_string()),
            ],
            "mundane theorem set-builder-subset",
        ),
        case(
            "introduce a symbol and say nothing it stands for",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational".to_string()), "mundane definition irrational\n  symbol      irr\n  then        x is irrational".to_string()),
            ],
            "says nothing it stands for",
        ),
        case(
            "define a term and name no symbol for it",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational".to_string()), "mundane definition irrational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "names no symbol for it",
        ),
        case(
            "introduce a symbol nothing writes",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational".to_string()), "mundane definition irrational\n  symbol      irr\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "cannot be reached",
        ),
        case(
            "introduce a symbol in more than one token",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational".to_string()), "mundane definition irrational\n  symbol      irr ational\n  defines     cr cq cdif\n  then        x is irrational".to_string()),
            ],
            "is not one token",
        ),
        case(
            "introduce one symbol from two definitions",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()), "mundane definition irrational\n  symbol      dup\n  defines     cr\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ\n\ndefinition twice\n  symbol      dup\n  defines     cq\n  then        x is irrational ↔ x ∈ ℝ and x ∉ ℚ".to_string()),
            ],
            "is already introduced by",
        ),
        case(
            "state a field twice, which reads as one field joined",
            vec![
                edit("corpus/stdlib/numbers.records", Some("mundane definition irrational\n  then        x is irrational".to_string()), "mundane definition irrational\n  target      eldif\n  then        x is irrational".to_string()),
            ],
            "a second time",
        ),
        // A field is read by its name, so a misspelt one is not the field: the
        // Archimedean item would have no target, and Theorem 13's citation of it
        // would stop the build.
        case(
            "misspell a field name",
            vec![
                edit("corpus/stdlib/numbers.records", Some("  target      nnrecl\n".to_string()), "  taget       nnrecl\n".to_string()),
            ],
            "theorem archimedean has a field 'taget', which a theorem record does not have",
        ),
        // Everything a citation names does work. The requires line says
        // a + b ∈ ℝ, which is what `mun:nonneg-or-neg` asks; H1 says a ∈ ℝ,
        // which it does not.
        case(
            "cite a line the cited item asks nothing of",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    mun:nonneg-or-neg x := a + b\n".to_string()), "    mun:nonneg-or-neg x := a + b, from H1\n".to_string()),
            ],
            "step 1 cites H1, and mun:nonneg-or-neg asks for nothing it says",
        ),
        // A "there is" given by an instance is given only where the instance is
        // in the domain. The mean value theorem's step 30 exhibits c, and
        // without line 24, which says c ∈ (a, b), the witness could be
        // anywhere.
        case(
            "exhibit a witness without saying it is in the domain",
            vec![
                edit("proofs/mean-value.proof", Some("    exhibit, from 24, 29\n".to_string()), "    exhibit, from 29\n".to_string()),
            ],
            "step 30 exhibits c := c, so it needs c ∈ (a, b)",
        ),
        // The witness is read off what the body says, not off the bare
        // membership, which any number in ℕ satisfies: harmonic-unbounded's
        // step 6 exhibits 2^N, which line 4 says the sum is above M at, and
        // without line 5 nothing says 2^N ∈ ℕ. The numeral 1 in the sum is
        // in ℕ too, and is no candidate.
        case(
            "exhibit a witness whose membership is not said, with a numeral in the body",
            vec![
                edit("proofs/harmonic.proof", Some("    exhibit, from 5, 4\n".to_string()), "    exhibit, from 4\n".to_string()),
            ],
            "step 6 exhibits n := 2^N, so it needs 2^N ∈ ℕ",
        ),
        // A requires line rests on the lines above it, read top to bottom
        // (`SYNTAX.md`). Written first, |numer(x)| ∈ ℕ₀ asks for numer(x) ∈ ℤ,
        // which no line above it states.
        case(
            "a requires line resting on one written below it",
            vec![
                edit("proofs/rationals-countable.proof", Some("    requires numer(x) ∈ ℤ: mun:lowest-terms-parts x := x\n    requires denom(x) ∈ ℕ: mun:lowest-terms-parts x := x\n    requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n".to_string()), "    requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n    requires numer(x) ∈ ℤ: mun:lowest-terms-parts x := x\n    requires denom(x) ∈ ℕ: mun:lowest-terms-parts x := x\n".to_string()),
            ],
            "the requires line of step 5 cites mun:abs-integer, which asks for z ∈ ℤ, and what it cites does not supply them",
        ),
        // A sort is stated once, like a declared type, and a step does not cite
        // it to rely on it (`READERS.md`): citing one names a line that does no
        // work.
        case(
            "cite the line that says what sort of thing a name is",
            vec![
                edit("proofs/isosceles.proof", Some("    mun:distance-symmetric P := A, Q := C\n".to_string()), "    mun:distance-symmetric P := A, Q := C, from H1\n".to_string()),
            ],
            "step 1 cites H1, and mun:distance-symmetric asks for nothing it says",
        ),
        // A count step's claim fixes the property it is applied to, and so
        // supplies its hypotheses with no search for them; a line named
        // beside them still has to do work. 1.2.12.3 says c(j, y) is not
        // odd, which count-step-holds does not ask.
        case(
            "cite a line a count step asks nothing of",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("mun:count-step-holds k := j, from 1.2.12.7, D1\n".to_string()), "mun:count-step-holds k := j, from 1.2.12.7, 1.2.12.3, D1\n".to_string()),
            ],
            "step 1.2.12.8 cites 1.2.12.3, and mun:count-step-holds asks for nothing it says",
        ),
        // A requires line citing a define is the step it would be, and has
        // each argument in its domain as a step does: c(j, y) is defined for
        // y ∈ V, which 1.2.1 says.
        case(
            "cite a define in a requires line without its argument's domain",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("requires c(j, y) ∈ ℕ₀: mun:count-nat0 k := j, from D1, 1.2.1\n".to_string()), "requires c(j, y) ∈ ℕ₀: mun:count-nat0 k := j, from D1\n".to_string()),
            ],
            "cites D1 at y, so it needs y ∈ V, and nothing it cites or the requires lines above it say it",
        ),
        // An obtain names its item after the word `obtain`, and the checks that
        // read an item citation read only a step the item heads. The three
        // below went unreported.
        case(
            "obtain from an item without what it asks for",
            vec![
                edit("proofs/intermediate-value.proof", Some("    obtain c: axi:completeness S := S, from 5, 2, 7".to_string()), "    obtain c: axi:completeness S := S, from 5, 7".to_string()),
            ],
            "step 8 cites axi:completeness, which asks for",
        ),
        case(
            "obtain from an item and cite a line it does not ask for",
            vec![
                edit("proofs/intermediate-value.proof", Some("    obtain c: axi:completeness S := S, from 5, 2, 7".to_string()), "    obtain c: axi:completeness S := S, from 5, 2, 7, H3".to_string()),
            ],
            "step 8 cites H3, and axi:completeness asks for nothing it says",
        ),
        // An item states what its target proves of every value of its names.
        // This one said |X| = k + 1 without saying what k was, and at k = −1
        // and X = ∅ it is false.
        case(
            "leave open a name an item uses as a number",
            vec![
                edit("corpus/stdlib/counting.records", Some("mundane theorem card-nonempty\n  let X be a set                                                      (H1)\n  let k ∈ ℕ₀                                                          (H2)\n".to_string()), "mundane theorem card-nonempty\n  let X be a set                                                      (H1)\n".to_string()),
            ],
            "mundane theorem card-nonempty: k stands where a number goes",
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
                edit("proofs/intermediate-value.proof", Some("    6.1.  s ∈ [a, b]\n          mun:set-builder, from D1, K1\n".to_string()), "    6.1.  s ∈ [a, b]\n          mun:set-builder, from D1, K1\n          requires s is a set: from K1\n".to_string()),
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
                edit("proofs/cites.proof", None, "import mundane theorem stdlib/numbers/int-real\n\ntheorem only-cited\n  then c = c\n\n1.  c = c\n    mun:int-real m := c\n".to_string()),
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
                edit("proofs/sqrt2-irrational.proof", Some("    obtain k: mun:odd n := n, from H2".to_string()), "    obtain k: mun:odd n := n".to_string()),
            ],
            "step 1 obtains from mun:odd, which says there is one only from",
        ),
        // Pascal's rule pairs C(n, k) with C(n, k − 1). The other neighbour is
        // the mistake a reader makes when the index shift goes the wrong way.
        case(
            "Pascal with the shift going the wrong way",
            vec![
                edit("proofs/binomial.proof", Some("    50.3.  C(m, k) + C(m, k − 1) = C(m + 1, k)\n".to_string()), "    50.3.  C(m, k) + C(m, k + 1) = C(m + 1, k)\n".to_string()),
            ],
            "step 50.3 claims something that thm:pascal does not conclude",
        ),
        // Shifting the index moves the range with it.
        case(
            "a shifted sum left over the range it came from",
            vec![
                edit("proofs/binomial.proof", Some("30. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 + 1 to m + 1)".to_string()), "30. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 to m)".to_string()),
            ],
            "step 30 claims something that mun:sum-shift does not conclude",
        ),
        // A line saying something of every index from 0 to m says nothing of
        // the index m + 1, which the sum to m + 1 takes.
        case(
            "a term-by-term line over too short a range",
            vec![
                edit("proofs/binomial.proof", Some("    mun:sum-termwise a := 0, b := m + 1, from 50\n".to_string()), "    mun:sum-termwise a := 0, b := m + 1, from 10\n".to_string()),
            ],
            "step 51 cites mun:sum-termwise, which asks for",
        ),
        // C(n, k) is zero above n, and C(m + 1, m + 1) is not above it.
        case(
            "a coefficient called zero where k is not above n",
            vec![
                edit("proofs/binomial.proof", Some("    def:C n := m, k := m + 1, from 12".to_string()), "    def:C n := m + 1, k := m + 1, from 12".to_string()),
            ],
            "step 13 claims something that def:C does not conclude",
        ),
        // Every block of binomial-step fixes k under the label J, and J means
        // what the block around the citing step says: here k runs from 1. Read
        // theorem-wide, J was the last block's, from 0, and this edit passed.
        case(
            "a label read as a sibling block's",
            vec![
                edit("proofs/binomial.proof", Some("           requires k ∈ ℤ: mun:range-integer a := 1, b := m + 1, from J\n".to_string()), "           requires k ∈ ℤ: mun:range-integer a := 0, b := m + 1, from J\n".to_string()),
            ],
            "the requires line of step 32.1 cites mun:range-integer, which asks for a ∈ ℤ; b ∈ ℤ; k ∈ {a, …, b}, and what it cites does not supply them",
        ),
        // `arithmetic` may stand where a closed-numeral fact is used, and only
        // there: an equation with a letter in it gives a reader something to
        // check, and is a numbered step. `SYNTAX.md` has the rule.
        case(
            "take an equation with a letter in it from arithmetic",
            vec![
                edit("proofs/binomial.proof", Some("substitute (m + 1) − 0 = m + 1 (line 37)".to_string()), "substitute (m + 1) − 0 = m + 1 (arithmetic)".to_string()),
            ],
            "takes (m + 1) − 0 = m + 1 from arithmetic, and it has a letter in it",
        ),
        case(
            "a chain link with a letter in it naming arithmetic",
            vec![
                edit("proofs/sum-formula.proof", Some("= (k + 1)((k + 1) + 1)/2       1.6".to_string()), "= (k + 1)((k + 1) + 1)/2       arithmetic".to_string()),
            ],
            "names arithmetic for",
        ),
        // Steps count 1, 2, 3 in the order they are written: a reader meeting 8
        // after 6 looks for a 7 that is not there.
        case(
            "a gap in the numbering",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("6.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()), "7.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()),
            ],
            "numbers run on without gaps",
        ),
        // `membership` claims a term is in a number system and nothing else.
        case(
            "membership named for a claim that is no membership",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1\n".to_string()), "    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          membership, from 1\n".to_string()),
            ],
            "names membership for",
        ),
        // A line said of every k ∈ ℕ answers a hypothesis over {1, …, n}, and not
        // one over {0, …, n}: the table puts the first range inside ℕ and not
        // the second.
        case(
            "a for-every line over a set that does not hold the range",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    2.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1\n".to_string()), "    2.1.  Σ(k = 0 to n) 1/T(k) = Σ(k = 0 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 0, b := n, from 1\n".to_string()),
            ],
            "step 2.1 cites mun:sum-termwise, which asks for",
        ),
        // What a summand's function hypothesis asks is the membership of the
        // names the summand is built from, and asks nothing of 1 > 0.
        case(
            "a requires line the summand does not ask for",
            vec![
                edit("proofs/binomial.proof", Some("    mun:sum-scaled a := 0, b := m, c := x, t := t\n".to_string()), "    mun:sum-scaled a := 0, b := m, c := x, t := t\n    requires 1 > 0: arithmetic\n".to_string()),
            ],
            "says 1 > 0, and neither mun:sum-scaled nor",
        ),
        // A hypothesis asking a = b is answered by a line saying b = a, and by
        // nothing else: line 2 says |CB| = |BC|, which is neither way round the
        // |CB| = |CA| side-angle-side asks for.
        case(
            "answer an equation with one that says it neither way round",
            vec![
                edit("proofs/isosceles.proof", Some("      from 3, 4, H5\n".to_string()), "      from 3, 4, 2\n".to_string()),
            ],
            "step 5 cites axi:side-angle-side, which asks for",
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
        // A defined name is the term it names only where the step cites the
        // define (`SYNTAX.md`). Without D2 cited, x₁ ∈ ℝ is said of x₁, and
        // min-real concludes it only of min(b, c + δ/2).
        case(
            "lean on a define the line does not cite",
            vec![
                edit("proofs/intermediate-value.proof", Some("requires x₁ ∈ ℝ: mun:min-real x := b, y := c + δ/2, from D2\n".to_string()), "requires x₁ ∈ ℝ: mun:min-real x := b, y := c + δ/2\n".to_string()),
            ],
            "the requires line of step 16.10 needs something that mun:min-real does not conclude",
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
                edit("proofs/schroeder-bernstein.proof", Some("          mun:inverse-value, from H4, 3.5\n".to_string()), "          mun:inverse-value, from 3.5\n".to_string()),
            ],
            "step 3.7 cites mun:inverse-value, which asks for",
        ),
        // An image's points come from a part of the function's domain, and the
        // item asks the step to say it is one.
        case(
            "cite a value in an image with nothing saying the set is in the domain",
            vec![
                edit("proofs/schroeder-bernstein.proof", Some("                  mun:value-in-image, from D1, K2\n                  requires C ⊆ A: from 2\n".to_string()), "                  mun:value-in-image, from D1, K2\n".to_string()),
            ],
            "step 4.1.2 cites mun:value-in-image, which asks for",
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
                edit("proofs/schroeder-bernstein.proof", Some("                  mun:disjoint-member, from 7.2.2, K7, contradicting 7.2.1\n".to_string()), "                  mun:disjoint-member, from 7.2.2, contradicting 7.2.1\n".to_string()),
            ],
            "step 7.2.3 cites mun:disjoint-member, which asks for",
        ),
        // A group is let with its operation and its identity; one without the
        // identity is no introduction at all.
        case(
            "let a group without naming its identity",
            vec![
                edit("proofs/lagrange.proof", Some("let G be a finite group with operation · and identity e".to_string()), "let G be a finite group with operation ·".to_string()),
            ],
            "is none of the 13 introductions",
        ),
        // gH is read as the coset only of a part of the group, and the step
        // says H is one.
        case(
            "read a coset without saying H lies in G",
            vec![
                edit("proofs/lagrange.proof", Some("          mun:coset u := g, from K3, 4.1, 4.2\n          requires H ⊆ G: from 1\n".to_string()), "          mun:coset u := g, from K3, 4.1, 4.2\n".to_string()),
            ],
            "step 4.3 cites mun:coset, which asks for H ⊆ G",
        ),
        // An equation names a witness read either way round, and only so: g
        // is in gH as g = g·h for some h ∈ H, and e·g = g fits that neither
        // way.
        case(
            "name a coset witness by an equation that does not fit either way",
            vec![
                edit("proofs/lagrange.proof", Some("    4.2.  g·e = g\n".to_string()), "    4.2.  e·g = g\n".to_string()),
            ],
            "step 4.3 claims something that mun:coset does not conclude",
        ),
        // A claim may bind another letter than the definition it reads, and says
        // the same thing only where the letter it binds is the one it uses: with
        // b bound and a free, gH = aH is a claim about a, and 12.3 reads K's
        // condition from it.
        case(
            "read a definition with a bound letter the claim does not use",
            vec![
                edit("proofs/lagrange.proof", Some("    11.2. There is a ∈ G with gH = aH.\n".to_string()), "    11.2. There is b ∈ G with gH = aH.\n".to_string()),
            ],
            "step 11.3 claims something that mun:part-builder does not conclude",
        ),
        // K binds g, and read at gH it is `there is a ∈ G with gH = aH`: the g
        // of gH is not caught by K's. So the sentence written with it caught
        // says something else, and does not put gH in K.
        case(
            "read a definition at a term its bound letter would catch",
            vec![
                edit("proofs/lagrange.proof", Some("    11.2. There is a ∈ G with gH = aH.\n".to_string()), "    11.2. There is g ∈ G with gH = gH.\n".to_string()),
            ],
            "step 11.3 claims something that mun:part-builder does not conclude",
        ),
        // An obtain from part-builder finds its "there is" in the condition of
        // the set the cited line puts Y in; K20 says only x ∈ Y ∩ Z.
        case(
            "obtain from part-builder citing no line that puts the set in it",
            vec![
                edit("proofs/lagrange.proof", Some("obtain a: mun:part-builder, from D1, K18".to_string()), "obtain a: mun:part-builder, from D1, K20".to_string()),
            ],
            "step 14.1 obtains from mun:part-builder, which says there is one only from something the step does not cite",
        ),
        // A requires line says what the step's other lines do not: k ∈ ℤ
        // above already says k is real.
        case(
            "repeat a fact a line above already says",
            vec![
                edit("proofs/binomial.proof", Some("          requires k ∈ ℤ: mun:range-integer a := 0, b := m, from J\n\n".to_string()), "          requires k ∈ ℤ: mun:range-integer a := 0, b := m, from J\n          requires k ∈ ℝ: membership\n\n".to_string()),
            ],
            "the requires line of step 10.3 says k ∈ ℝ, which the step's other lines already say",
        ),
        // A line saying a term is not zero is asked for by a line below that
        // divides by it, and only by such a line: nothing in step 11 divides
        // by b − a.
        case(
            "a term said not zero that nothing below divides by",
            vec![
                edit("proofs/mean-value.proof", Some("    requires F : [a, b] → ℝ: from 9\n    requires g : [a, b] → ℝ: from 7\n".to_string()), "    requires b − a ≠ 0: inequalities, from H1, H2, H3\n    requires F : [a, b] → ℝ: from 9\n    requires g : [a, b] → ℝ: from 7\n".to_string()),
            ],
            "the requires line of step 11 says b − a ≠ 0, and neither thm:continuous-sum nor the step's other lines ask for it",
        ),
        // Counting by parts asks that two parts which meet be one part.
        case(
            "count by parts without saying they do not overlap",
            vec![
                edit("proofs/lagrange.proof", Some("from H1, 13, 14, 15".to_string()), "from H1, 13, 15".to_string()),
            ],
            "step 16 cites mun:partition-count, which asks for",
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
            "take cases from a disjunction in the other order",
            vec![
                edit("proofs/euclid.proof", Some("    3.9.  b(k) = 0 or b(k) ≠ 0".to_string()), "    3.9.  b(k) ≠ 0 or b(k) = 0".to_string()),
            ],
            "step 3.10 takes its cases from 3.9, which does not claim their assumptions joined by \"or\", in the order the cases take them",
        ),
        case(
            "give a first value in terms of the index",
            vec![
                edit("proofs/euclid.proof", Some("define a(0) := M,  b(0) := N,".to_string()), "define a(0) := k,  b(0) := N,".to_string()),
            ],
            "names k, which has no value at 0",
        ),
        case(
            "give a first value in terms of a sequence",
            vec![
                edit("proofs/euclid.proof", Some("define a(0) := M,  b(0) := N,".to_string()), "define a(0) := b(0),  b(0) := N,".to_string()),
            ],
            "names b, which has no value before 0",
        ),
        // n − 1 for n ∈ ℕ is an integer by what the page says once, and in ℕ₀
        // only by a line saying so.
        case(
            "cite a step rule without saying the index is in ℕ₀",
            vec![
                edit("proofs/reals-uncountable.proof", Some("          D3\n          requires n − 1 ∈ ℕ₀: from 16.1\n".to_string()), "          D3\n".to_string()),
            ],
            "no line it cites says the index is in ℕ₀",
        ),
        case(
            "claim the value of the other case",
            vec![
                edit("proofs/euclid.proof", Some("3.10.1.  a(k + 1) = a(k)".to_string()), "3.10.1.  a(k + 1) = b(k)".to_string()),
            ],
            "step 3.10.1 cites D1 and claims a value it does not give",
        ),
        case(
            "cite a step rule by cases without saying which case",
            vec![
                edit("proofs/euclid.proof", Some("3.10.13. b(k + 1) = a(k) mod b(k)\n                   D1, from C2".to_string()), "3.10.13. b(k + 1) = a(k) mod b(k)\n                   D1".to_string()),
            ],
            "says whether a case's condition holds",
        ),
        // A calculation's link cites the line that says it, and a line saying
        // a(0) = M does not say what substituting it inside a gcd gives.
        case(
            "cite an equation for a link that substitutes it inside a term",
            vec![
                edit("proofs/euclid.proof", Some("            gcd(a(0), b(0)) = gcd(M, b(0))     3.3".to_string()), "            gcd(a(0), b(0)) = gcd(M, b(0))     1".to_string()),
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
        case(
            "give the type of a define the citation does not bind",
            vec![
                edit("proofs/mean-value.proof", Some("requires g : [a, b] → ℝ: from 7".to_string()), "requires F : [a, b] → ℝ: from 9".to_string()),
            ],
            "says F : [a, b] → ℝ, and neither thm:continuous-linear nor the step's other lines ask for it",
        ),
        case(
            "give a bound define a type other than the item asks",
            vec![
                edit("proofs/mean-value.proof", Some("requires g : [a, b] → ℝ: from 7".to_string()), "requires g : ℕ → ℝ: from 7".to_string()),
            ],
            "says g : ℕ → ℝ, and neither thm:continuous-linear nor the step's other lines ask for it",
        ),
        case(
            "name a number with the derivative's spelling",
            vec![
                edit("proofs/mean-value.proof", Some("  assume a < b ".to_string()), "  let f′ ∈ ℝ                                                          (H9)\n  assume a < b ".to_string()),
            ],
            "f′ is how the derivative of the function f is written, so it cannot name anything else: call it f₁",
        ),
        // A defined function standing alone is read as its rule, so what is
        // said of it and what is said of its values are about one thing; it
        // is still only what the lines say of those values.
        case(
            "say a defined function maps into a set its values were not shown to lie in",
            vec![
                edit("proofs/euler.proof", Some("8.  f : S → S\n".to_string()), "8.  f : S → ℕ\n".to_string()),
            ],
            "step 8 claims something that mun:function-into does not conclude",
        ),
        case(
            "reorder a product by a map not shown to be one-to-one",
            vec![
                edit("proofs/euler.proof", Some("thm:product-reorder, from 5, 4, 9".to_string()), "thm:product-reorder, from 5, 4, 8".to_string()),
            ],
            "step 10 cites thm:product-reorder, which asks for",
        ),
        // `let p be a polynomial` says p is one, and an item asking that of
        // what it is cited at asks it of the lines the step names.
        case(
            "divide by x − a without saying p is a polynomial",
            vec![
                edit("proofs/factor.proof", Some("p := p, a := a, from H1".to_string()), "p := p, a := a".to_string()),
            ],
            "step 1 cites thm:remainder, which asks for p is a polynomial",
        ),
        // `inequalities` takes two terms differing only from a line it cites:
        // r ≠ 0 written above for 0 < r to rest on is asked for by nothing.
        case(
            "write r ≠ 0 above an inequalities line instead of citing it",
            vec![
                edit("proofs/bezout.proof", Some("          requires 0 < r: inequalities, from 1, S\n".to_string()), "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n".to_string()),
            ],
            "the requires line of step 3.1 says r ≠ 0, and neither mun:pos-int-nat nor the step's other lines ask for it",
        ),
        // A range is no number system, and a line putting r in one says
        // nothing past itself (`SYNTAX.md`): that r is whole is
        // `mun:range-integer`, cited.
        case(
            "read a member of a range as an integer without range-integer",
            vec![
                edit("proofs/euler.proof", Some("          requires r ∈ ℤ: mun:range-integer, from 6.1\n".to_string()), String::new()),
            ],
            "step 6.2 cites mun:coprime-product, which asks for x ∈ ℤ",
        ),
        // An exhibit's lines say each part of its body at the value, a
        // numeral's facts among them, and what is missing is named.
        case(
            "exhibit 2 for a d > 1 without saying 2 > 1",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("          requires 2 > 1: arithmetic\n".to_string()), String::new()),
            ],
            "step 2.16 exhibits d := 2, so it needs 2 > 1, and nothing it cites or requires says it",
        ),
        // An instantiation's value is in what its letter ranges over, as a
        // line the step names says: −f(c) > 0 says nothing of ℝ.
        case(
            "instantiate ε := −f(c) without saying −f(c) is real",
            vec![
                edit("proofs/intermediate-value.proof", Some("           requires −f(c) ∈ ℝ: membership, from H4, 13\n".to_string()), String::new()),
            ],
            "step 16.4 puts −f(c) for ε in line 15, so it needs −f(c) ∈ ℝ, and nothing it cites or requires says it",
        ),
        // A define used for what it is has its argument in its domain: c(j, y)
        // is defined for y ∈ V, which no line introduces y in.
        case(
            "unfold c(0, y) without saying y ∈ V",
            vec![
                edit("tests/elaborator/induction-under-a-condition.proof", Some("                  D1\n                  requires y ∈ V: from 1.1.1\n".to_string()), "                  D1\n".to_string()),
            ],
            "step 1.1.2 cites D1 at y, so it needs y ∈ V, and nothing it cites or requires says it",
        ),
        // A recursion's domain is its index: N((n − 1) + 1) asks n − 1.
        case(
            "unfold N((n − 1) + 1) without saying n − 1 ∈ ℕ₀",
            vec![
                edit("proofs/reals-uncountable.proof", Some("          D3\n          requires n − 1 ∈ ℕ₀: from 16.1\n".to_string()), "          D3\n".to_string()),
            ],
            "step 16.2 cites D3 at n − 1 + 1, so it needs n − 1 ∈ ℕ₀, and nothing it cites or requires says it",
        ),
        // The edges of the rule that a membership is said once (`READERS.md`).
        // A quotient is in a number system only where its divisor is not
        // zero, and for a letter that is the step's to say: x/y is real only
        // with y ≠ 0 cited.
        case(
            "divide by a letter without saying it is not zero",
            vec![
                edit("proofs/quotient.proof", None, QUOTIENT.replacen("x := x/y, from H3", "x := x/y", 1)),
            ],
            "step 1 cites mun:square-nonneg, which asks for x ∈ ℝ",
        ),
        // A define's name is not a letter introduced in a number system:
        // that x₁ is real rests on min-real, and abs-difference-lt asks it.
        case(
            "leave out a define's membership where an item asks it",
            vec![
                edit("proofs/intermediate-value.proof", Some("           mun:abs-difference-lt x := x₁, c := c, δ := δ, from 16.13, 16.14\n           requires x₁ ∈ ℝ: mun:min-real x := b, y := c + δ/2, from D2\n".to_string()), "           mun:abs-difference-lt x := x₁, c := c, δ := δ, from 16.13, 16.14\n".to_string()),
            ],
            "step 16.15 cites mun:abs-difference-lt, which asks for",
        ),
        // `let k ∈ ℕ` says k ≥ 1 beyond the membership, and a step using it
        // cites the line: sum-extended asks n ≥ a at n := k, a := 1.
        case(
            "lean on let k ∈ ℕ for k ≥ 1 without citing it",
            vec![
                edit("proofs/sum-formula.proof", Some("          requires k ≥ 1: from K\n".to_string()), String::new()),
            ],
            "step 1.3 cites mun:sum-extended, which asks for",
        ),
        // A letter's membership is said where it is introduced, and a line
        // cited only for it does no work: H1 says a ∈ ℝ, and exponent-zero
        // asks nothing else of it.
        case(
            "cite a let line only for the membership it introduces",
            vec![
                edit("proofs/geometric-series.proof", Some("    1.2.  a^0 = 1\n          mun:exponent-zero a := a\n".to_string()), "    1.2.  a^0 = 1\n          mun:exponent-zero a := a, from H1\n".to_string()),
            ],
            "step 1.2 cites H1, and mun:exponent-zero asks for nothing it says",
        ),
        // The same of an obtain's sentence `p ∈ ℤ`: even-square asks
        // p ∈ ℤ at n := p, which 2.1 says once, where it obtains p.
        case(
            "cite an obtain only for the membership it states",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("          thm:even-square n := p, from 2.4\n".to_string()), "          thm:even-square n := p, from 2.1, 2.4\n".to_string()),
            ],
            "step 2.5 cites 2.1, and thm:even-square asks for nothing it says",
        ),
    ]
}
