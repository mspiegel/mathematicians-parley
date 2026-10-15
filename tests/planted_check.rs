//! The checker catches things.
//!
//! Each case takes the corpus, makes one edit that should be a defect, and
//! requires that the checker report it. A checker that passes a clean corpus
//! proves nothing on its own; this is the half that matters.
//!
//! The corpus is read once into memory and each case edits it through an
//! overlay of its own, so no case copies a directory and none can see
//! another's edit. The clean corpus is checked whole; a case checks the
//! theorems its edits can reach (`checker::run_edited`). The cases run side by
//! side (`threads::in_order`), and are reported in the order they are
//! written.
//!
//! Every message the checker writes out where it reports it is said by some
//! case, so that a check no case reaches is found: one that had stopped
//! running said nothing, and nothing here noticed. A message put together
//! elsewhere and handed to the report is not read this way.

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

/// What one case says, whether it missed, and everything the checker
/// printed: a case misses where its edit could not be planted, or the
/// checker did not report it.
fn outcome(case: &Case, clean: &Memory) -> (String, bool, String) {
    let tree = match plant(case, clean) {
        Ok(tree) => tree,
        Err(why) => return (why, true, String::new()),
    };
    // Only what the edits reach is checked: a case passes only where its
    // problem is reported, and a theorem left unchecked can only leave a
    // problem out.
    let edited: Vec<String> = case.edits.iter().map(|e| e.file.to_string()).collect();
    let out = parley::checker::run_edited(&tree, &edited).printed;
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
    let mut files: Vec<_> = std::fs::read_dir(&root)
        .expect("src/checker reads")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .collect();
    files.sort();
    let mut out = Vec::new();
    for file in files {
        let text = std::fs::read_to_string(&file).expect("a source file reads");
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
            edit("proofs/tri.proof", None, TRI.to_string()),
            edit(
                "proofs/tri-use.proof",
                None,
                "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T as C (D1)\n\ntheorem use-one\n  then C(1) = 1\n\n1.  C(1) = 1\n    thm:tri-one, from D1\n".to_string(),
            ),
        ],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::checker::run(&tree).printed;
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
    let out = parley::checker::run(&tree).printed;
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

/// A citation whose claim is what the item concludes, with one hypothesis
/// not supplied, is reported once, naming that hypothesis: here
/// divides-difference without line 5.2, which says p divides n!. The other
/// hypotheses are supplied, and the claim is the item's conclusion.
#[test]
fn a_hypothesis_not_supplied_is_named_alone() {
    let clean = clean();
    let case = case(
        "drop the line that supplies one hypothesis",
        vec![edit(
            "proofs/infinitely-many-primes.proof",
            Some(
                "mun:divides-difference d := p, a := n! + 1, b := n!, from 3, 5.2"
                    .to_string(),
            ),
            "mun:divides-difference d := p, a := n! + 1, b := n!, from 3".to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::checker::run(&tree).printed;
    assert!(
        out.contains(
            "which asks for p divides n!, and what it cites does not supply it"
        ),
        "{out}"
    );
    assert!(!out.contains("does not conclude"), "{out}");
    assert!(out.contains("\n1 problem(s)\n"), "{out}");
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
            "proofs/twice.proof",
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
        parley::checker::run_edited(&tree, &["proofs/twice.proof".to_string()]).printed;
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
            "proofs/twice.proof",
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
        parley::checker::run_edited(&tree, &["proofs/twice.proof".to_string()]).printed;
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
        "write a factorial twice in an arithmetic step",
        vec![edit(
            "proofs/twice.proof",
            None,
            "theorem twice\n  then 1! = 1!\n\n1.  1! = 1!\n    arithmetic\n"
                .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out =
        parley::checker::run_edited(&tree, &["proofs/twice.proof".to_string()]).printed;
    assert_eq!(out.matches("works out factorial").count(), 1, "{out}");
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
    inequalities, from 1, 3, 4
    requires {1, …, 23} is finite: from 1
    requires |{1, …, 23}| ∈ ℕ₀: mun:card-nat0, from 1
"
            .to_string(),
        )],
        "",
    );
    let tree = plant(&case, &clean).unwrap();
    let out = parley::checker::run(&tree).printed;
    assert!(out.contains("\n0 problem(s)\n"), "{out}");
}

#[test]
fn the_checker_catches_every_planted_defect() {
    let clean = clean();
    let base = parley::checker::run(&clean);
    assert!(
        base.printed.contains("\n0 problem(s)\n"),
        "the corpus is not clean, so a planted defect proves nothing:\n{}",
        base.printed
    );
    let cases = cases();
    let results = in_order(&cases, || (), |_, case| outcome(case, &clean));
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
    vec![
        // A step's proof rests only on what it names (`GOALS.md` decision 9).
        // Without its requires line, `algebra` combines n!, and the scope
        // holds n! ∈ ℕ from line 1, which step 5.4 does not cite. A factorial
        // is not a membership said once, so only a line can give it.
        case(
            "lean on a line the step does not name",
            vec![edit(
                "proofs/infinitely-many-primes.proof",
                Some("    5.4.  (n! + 1) − n! = 1\n          algebra\n          requires n! ∈ ℝ: from 1\n".to_string()),
                "    5.4.  (n! + 1) − n! = 1\n          algebra\n".to_string(),
            )],
            "proofs/infinitely-many-primes.proof:45  nothing says n! ∈ ℝ or ∈ ℂ, which this step needs",
        ),
        // An angle is no letter, numeral or term built from them, so the
        // `algebra` step combining it writes its membership, unless a cited
        // equation gives it: H9 does for ∠QPR, and nothing does for ∠QRP,
        // which line 3 holds only inside a sum.
        case(
            "leave out the membership of an angle an algebra step combines",
            vec![edit(
                "proofs/pythagoras.proof",
                Some("    requires ∠QRP ∈ ℝ: mun:triangle-angle-real, from H7\n".to_string()),
                String::new(),
            )],
            "nothing says ∠QRP ∈ ℝ or ∈ ℂ, which this step needs",
        ),
        // k + 1 is a membership said once, and its being no zero is not: a
        // divisor's `≠ 0` is written, and a product's is its factors'. The
        // step divides by k(k + 1)/2, and nothing says its factor k + 1 is
        // not zero.
        case(
            "leave out a divisor's ≠ 0 built from a letter said once",
            vec![edit(
                "proofs/triangular-reciprocals.proof",
                Some("          requires k + 1 ≠ 0: inequalities, from K1\n".to_string()),
                String::new(),
            )],
            "nothing says k + 1 ≠ 0, which this step needs to divide by it",
        ),
        // A difference of numerals is no numeral, so a step dividing by one
        // writes its `≠ 0`.
        case(
            "divide by a difference of numerals without saying it is not zero",
            vec![edit(
                "proofs/perfect-numbers.proof",
                Some("    requires 1 − 2 ≠ 0: arithmetic\n".to_string()),
                String::new(),
            )],
            "nothing says 1 − 2 ≠ 0, which this step needs to divide by it",
        ),
        // Where the proof has no letter of the subject's name in scope, the
        // pair is the only thing that says what the definition is about:
        // even-leg has no d, and its step claims an impossible fold.
        case(
            "leave out a definition's subject where the proof has no such letter",
            vec![edit(
                "proofs/pythagorean-triples.proof",
                Some("mun:divides d := 4, n := 2, from 2.2.11".to_string()),
                "mun:divides n := 2, from 2.2.11".to_string(),
            )],
            "mun:divides is about d, and the step gives d no value and the proof has no d; write it, as d := t",
        ),
        // A step citing a theorem of its own file reads the defines that
        // theorem is stated over, those above it, and no other: D2 is
        // written below `above`, so `below` claims R(k) = k + 1 of a theorem
        // that says nothing of R, and does not cite D2.
        case(
            "read a define written below the theorem of the file a step cites",
            vec![edit(
                "proofs/stated-over.proof",
                None,
                "define S(k) := k + 1, for k ∈ ℕ                                      (D1)\n       reads one more than k\n\ntheorem above\n  let k ∈ ℕ                                                           (H1)\n  then S(k) = k + 1\n\n1.  S(k) = k + 1\n    D1\n\ndefine R(k) := k + 1, for k ∈ ℕ                                      (D2)\n       reads also one more than k\n\ntheorem below\n  let k ∈ ℕ                                                           (H1)\n  then R(k) = k + 1\n\n1.  R(k) = k + 1\n    thm:above\n".to_string(),
            )],
            "proofs/stated-over.proof:19  step 1 claims something that thm:above does not conclude",
        ),
        // abs asks that x be real, at x := ⌊A + 1/2⌋ − A, and line 1 says
        // only that the floor is an integer: the difference's membership is
        // a closure no line the step names states.
        case(
            "a hypothesis supplied only by a closure of what the step names",
            vec![edit(
                "tests/elaborator/floor-in-a-bound.proof",
                Some("    mun:abs x := ⌊A + 1/2⌋ − A, from H2, 2\n".to_string()),
                "    mun:abs x := ⌊A + 1/2⌋ − A, from H2, 1\n".to_string(),
            )],
            "step 3 cites mun:abs, which asks for ⌊A + 1 / 2⌋ − A ∈ ℝ, and what it cites does not supply it",
        ),
        // A sum of squares of reals is not shown to be a natural number by
        // the let's reason. The checker does not judge a let's kind against
        // its reason; it reports what the planted kind makes surplus below.
        case(
            "a let saying a kind of number its reason does not show",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("    let A = Σ(k = 1 to n) a(k)², a real number                        (D1)".to_string()),
                "    let A = Σ(k = 1 to n) a(k)², a natural number                     (D1)".to_string(),
            )],
            "the requires line of step 5.11 says A > 0, which the step's other lines already say",
        ),
        // A false divisibility of numerals, on a requires line: the checker
        // works it out as `arithmetic` does (`check_arithmetic_holds`).
        case(
            "a divisibility of numerals that does not hold",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 3 divides 10 − 2: arithmetic\n".to_string(),
            )],
            "the requires line 3 divides 10 − 2 of step 1.3 is arithmetic, which is false",
        ),
        // A method decides a word only where the word's record names it
        // (`DATABASE.md`, `decided`). With `arithmetic` struck from
        // `divides`, every divisibility of numerals it settles is refused.
        case(
            "a divisibility arithmetic decides with its record not naming it",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        d divides n ↔ there is k ∈ ℤ with n = d·k\n  decided     arithmetic, inspection".to_string()),
                "  then        d divides n ↔ there is k ∈ ℤ with n = d·k\n  decided     inspection".to_string(),
            )],
            "4 divides 2 is a word divides defines, and arithmetic decides a word only where its record says so in a `decided` field",
        ),
        // A requires line of `from` alone rests on the lines it names: f(b)
        // is real by f's type H4 and b's place in its domain, and with H4
        // left out nothing it names types f, the type in scope being no
        // line it names.
        case(
            "a from line that leaves out the type its value needs",
            vec![edit(
                "proofs/mean-value.proof",
                Some("    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 24\n    requires f(a) ∈ ℝ: from H4, 1\n    requires f(b) ∈ ℝ: from H4, 2\n".to_string()),
                "    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 24\n    requires f(a) ∈ ℝ: from H4, 1\n    requires f(b) ∈ ℝ: from 2\n".to_string(),
            )],
            "from 2 does not reach f(b) ∈ ℝ, which this line claims it supplies",
        ),
        // A claim the method named does not decide, a membership said by
        // `inequalities`: no closure step is taken without examining it.
        case(
            "rest a claim on a method that does not decide it",
            vec![edit(
                "proofs/sqrt2-irrational.proof",
                Some("2.  q > 0\n    inequalities, from 1\n".to_string()),
                "2.  q ∈ ℤ\n    inequalities, from 1\n".to_string(),
            )],
            "step 2 names inequalities, which does not decide what it claims",
        ),
        // A link of numerals alone naming arithmetic, worked out whole.
        case(
            "a chain link of numerals that is false",
            vec![edit(
                "proofs/sum-formula.proof",
                Some("= 1(1 + 1)/2            arithmetic".to_string()),
                "= 1(1 + 1)/3            arithmetic".to_string(),
            )],
            "a link of step 1.2 names arithmetic for 1 = 1(1 + 1)/3, which is false",
        ),
        // Inspection decides "is prime" by the number: a composite at any
        // size by its least factor, and a prime only below 29², past which
        // trial division by the primes up to 23 settles nothing.
        case(
            "claim by inspection that a composite number is prime",
            vec![edit(
                "tests/notations/primes.proof",
                Some("  then 97 is prime\n\n1.  97 is prime\n".to_string()),
                "  then 91 is prime\n\n1.  91 is prime\n".to_string(),
            )],
            "step 1 claims 91 is prime, which inspection of what it cites shows false",
        ),
        case(
            "claim by inspection that a prime past 841 is prime",
            vec![edit(
                "tests/notations/primes.proof",
                Some("  then 97 is prime\n\n1.  97 is prime\n".to_string()),
                "  then 853 is prime\n\n1.  853 is prime\n".to_string(),
            )],
            "and 853 is not below 841",
        ),
        // A count of the odd vertices that leaves A out, 5 being odd, which
        // the checker counts by inspection as the reader does.
        case(
            "a parity inspection settles that a count leaves out",
            vec![edit(
                "proofs/konigsberg.proof",
                Some("6.  |{x ∈ V : deg(x) is odd}| = 4".to_string()),
                "6.  |{x ∈ V : deg(x) is odd}| = 3".to_string(),
            )],
            "step 6 claims |{x ∈ V : deg(x) is odd}| = 3, which inspection of what it cites shows false",
        ),
        // `substitute` walks its equation both ways and each sentence of the
        // line it names, trying the next where one declines. A name the proof
        // never introduced is not one of those: it is a defect.
        case(
            "substitute a name the proof never introduced",
            vec![edit(
                "proofs/geometric-series.proof",
                Some("          substitute a^((k + 1) + 1) = a^(k + 1)·a (line 1.9)".to_string()),
                "          substitute a^((k + 1) + 1) = z (line 1.9)".to_string(),
            )],
            "step 1.11 takes a^(k + 1 + 1) = z from 1.9, which does not say it",
        ),
        // A step claims of a definition something it does not say.
        case(
            "claim of a definition what it does not say",
            vec![edit(
                "proofs/triangle-inequality.proof",
                Some("    2.5.  |x| = −x".to_string()),
                "    2.5.  |x| = x".to_string(),
            )],
            "step 2.5 claims something that mun:abs does not conclude",
        ),
        // A base may be written without an identity element its instance
        // has, and nothing else: 1 = (1 − a)/(1 − a) is no instance of
        // G(a, 0) = (1 − a^(0 + 1))/(1 − a) however its elements are read.
        case(
            "end an induction's base on what is not its instance",
            vec![edit(
                "proofs/geometric-series.proof",
                Some("    1.5.  G(a, 0) = (1 − a)/(1 − a)\n          calculation\n            G(a, 0) = 1                    1.3\n                    = (1 − a)/(1 − a)      1.4\n\n".to_string()),
                "".to_string(),
            )],
            "step 1.4 ends the base part of step 1, which owes G(a, 0) = (1 − a^(0 + 1)) / (1 − a)",
        ),
        // A conclusion is matched with an identity element dropped where the
        // instance has one, and with nothing else changed: the shifted sum
        // starts at 0 + 1, which is 1 and not 2.
        case(
            "claim a lemma's conclusion with more than an identity element dropped",
            vec![edit(
                "proofs/binomial.proof",
                Some("29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 1 to m + 1)".to_string()),
                "29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 2 to m + 1)".to_string(),
            )],
            "step 29 claims something that mun:sum-shift does not conclude",
        ),
        // A substitution's line may leave out the + 0 it makes, and nothing
        // else: the product written the other way round is a reordering, which
        // no identity law gives.
        case(
            "a substitution that reorders where it drops a 0",
            vec![edit(
                "proofs/factor.proof",
                Some("    2.2.  p(x) = (x − a)·q(x)\n".to_string()),
                "    2.2.  p(x) = q(x)·(x − a)\n".to_string(),
            )],
            "step 2.2 claims p(x) = q(x) · (x − a), which putting one side of p(a) = 0 for the other does not make",
        ),
        // 0 is an identity on the right of a difference and not on its left:
        // C(m, 0 − 1) is not C(m, −1) by any identity law.
        case(
            "drop a 0 from the side of a difference where it is no identity",
            vec![edit(
                "proofs/binomial.proof",
                Some("= C(m, 0 − 1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()),
                "= C(m, −1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string(),
            )],
            "step 38 claims something that mun:sum-first does not conclude",
        ),
        // A `requires` line has a claim and a reason, and the reason is what
        // proves it. Here H5 does not say `C ≠ A`, and no line above this one
        // does.
        case(
            "name a line that does not state the side condition",
            vec![edit(
                "proofs/pythagoras.proof",
                Some("    requires C ≠ A: mun:triangle, from H4\n".to_string()),
                "    requires C ≠ A: mun:triangle, from H5\n".to_string(),
            )],
            "the requires line of step 2 needs something that mun:triangle does not conclude",
        ),
        // The same, where the scope already holds the claim for another reason:
        // the hypothesis says A, B, C form a triangle, so `C ≠ B` is held before
        // the line is read, and H5 does not say it.
        case(
            "name a line that does not state a claim the scope already holds",
            vec![edit(
                "proofs/pythagoras.proof",
                Some("    requires C ≠ B: mun:triangle, from H4\n".to_string()),
                "    requires C ≠ B: mun:triangle, from H5\n".to_string(),
            )],
            "the requires line of step 8 needs something that mun:triangle does not conclude",
        ),
        // A requires line below that cites an item asks for that item's
        // hypotheses, and only those: mun:sum-real asks nothing of x^m, and
        // nothing asks x^m ∈ ℝ of a substitution that drops the 0 before the
        // sum. A power to a letter is written where it is needed, so the line
        // is not one the step is spared; it is one nothing needs.
        case(
            "a requires line above an item's line that the item does not ask for",
            vec![edit(
                "proofs/binomial.proof",
                Some("    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 37) into line 38\n    requires Σ(k = 1 to m + 1)".to_string()),
                "    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 37) into line 38\n    requires x^m ∈ ℝ: mun:power-real a := x, m := m, from H1\n    requires Σ(k = 1 to m + 1)".to_string(),
            )],
            "the requires line of step 39 cites H1, and mun:power-real asks for nothing it says",
        ),
        // A requires line rests only on its reason. Line 2 does not say n! is
        // an integer, and `mun:int-real` asks it; the scope has it from line
        // 1, which the line does not cite, so the item it names reaches
        // nothing.
        case(
            "give a requires line a reason that is not where its proof comes from",
            vec![
                edit(
                    "proofs/infinitely-many-primes.proof",
                    Some("import theorem            stdlib/divisibility/prime-factor\n".to_string()),
                    "import theorem            stdlib/divisibility/prime-factor\nimport mundane theorem stdlib/numbers/int-real\n".to_string(),
                ),
                edit(
                    "proofs/infinitely-many-primes.proof",
                    Some("          algebra\n          requires n! ∈ ℝ: from 1\n".to_string()),
                    "          algebra\n          requires n! ∈ ℝ: mun:int-real, from 2\n".to_string(),
                ),
            ],
            "the requires line of step 5.4 cites mun:int-real, which asks for n! ∈ ℤ, and what it cites does not supply it",
        ),
        // Everything a step names does work. A numeral's membership is said
        // once (`SYNTAX.md`), so the line is true, well formed, and does
        // nothing.
        case(
            "write a requires line nothing asks for",
            vec![edit(
                "proofs/sum-formula.proof",
                Some("    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra\n".to_string()),
                "    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra\n          requires 2 ∈ ℝ: arithmetic\n".to_string(),
            )],
            "the requires line of step 1.6 says 2 ∈ ℝ, which the step's other lines already say",
        ),
        // A claim of numerals said to be impossible, given to `inequalities`:
        // a claim of numerals alone is arithmetic's, and is refused there.
        case(
            "say a true claim is impossible",
            vec![edit(
                "proofs/reals-uncountable.proof",
                Some("    2.3.  10 divides 1, which is impossible\n          substitute (t + 1) − t = 1 (line 2.2) into line 2.1\n".to_string()),
                "    2.3.  10 divides 1\n          substitute (t + 1) − t = 1 (line 2.2) into line 2.1\n\n    2.4.  1 ≤ 10, which is impossible\n          inequalities\n".to_string(),
            )],
            "step 2.4 gives inequalities for 1 ≤ 10, which has no letter in it; a claim of numerals alone is arithmetic's",
        ),
        // A claim of `algebra` that is not an identity, and one asking a
        // power past what algebra may multiply out: the checker decides
        // algebra (`check_algebra_holds`).
        case(
            "claim an algebra step the cited lines do not give",
            vec![edit(
                "proofs/geometric-series.proof",
                Some("    1.10. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a)".to_string()),
                "    1.10. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1".to_string(),
            )],
            "(1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1 is not an identity, nor does it follow from what step 1.10 cites",
        ),
        // A bound the cited lines do not give: q ∈ ℕ says q ≥ 1 and so
        // q > 0, never q > 1 (`check_inequalities_holds`).
        case(
            "claim an inequalities step the cited lines do not give",
            vec![edit(
                "proofs/sqrt2-irrational.proof",
                Some("2.  q > 0\n    inequalities, from 1\n".to_string()),
                "2.  q > 1\n    inequalities, from 1\n".to_string(),
            )],
            "q > 1 does not follow from what step 2 cites",
        ),
        case(
            "ask algebra to multiply out a power past its cost",
            vec![edit(
                "proofs/geometric-series.proof",
                Some("    1.10. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a)".to_string()),
                "    1.10. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + (a + 1)^30 − (a + 1)^30".to_string(),
            )],
            "(a + 1)^30 is a power algebra does not multiply out",
        ),
        // A side condition is supplied by what the step names, not by
        // everything in scope: the scope holds |T| = 2^k, and with 1.2.5 no
        // longer cited nothing the step names says it.
        case(
            "settle a side condition from a line the step does not cite",
            vec![edit(
                "proofs/subsets.proof",
                Some("n := 2^k, from 1.2.3, 1.2.5, 1.2.6".to_string()),
                "n := 2^k, from 1.2.3, 1.2.6".to_string(),
            )],
            "step 1.2.8 cites mun:card-disjoint-union, which asks for |T| = 2^k, and what it cites does not supply it",
        ),
        // `card-remove` loses its target, and the edit to its record changes
        // what it concludes, so the step citing it claims what it does not.
        case(
            "cite a theorem the database gives no target for",
            vec![edit(
                "corpus/stdlib/counting.records",
                Some("  then        |X ∖ {a}| = k\n  metamath    hashdifsnp1\n  target      hashdifsnp1 with V := X, N := a, Y := k\n".to_string()),
                "  then        |X ∖ {a}| ≤ k\n  metamath    hashdifsnp1\n".to_string(),
            )],
            "step 1.2.2 claims something that mun:card-remove does not conclude",
        ),
        // A definition with no target concludes only what its record says,
        // and a step claiming something else of it is refused.
        case(
            "unfold a definition with no target into what it does not say",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("10. For all s ∈ S, s ≤ c.".to_string()),
                "10. For all s ∈ S, s < c.".to_string(),
            )],
            "step 10 claims something that mun:upper-bound does not conclude",
        ),
        // Continuity unfolds into what its definition says: with δ where ε
        // belongs, or with δ ≥ 0 where the definition says δ > 0, it is not
        // what the definition concludes.
        case(
            "unfold continuity into what it does not say",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("|f(x) − f(c′)| < ε for all x".to_string()),
                "|f(x) − f(c′)| < δ for all x".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        case(
            "unfold continuity with a weaker bound than it gives",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("there exists δ > 0 such that".to_string()),
                "there exists δ ≥ 0 such that".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        // The least upper bound is the supremum, which is a number only of a
        // set bounded above, and line 7 is what says S is. Without it cited
        // nothing supplies the hypothesis naming a bound, and the step says
        // which.
        case(
            "obtain the least upper bound without the line bounding the set",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("obtain c: axi:completeness, from 2, 5, 7".to_string()),
                "obtain c: axi:completeness, from 2, 5".to_string(),
            )],
            "step 8 cites axi:completeness, which asks for S ⊆ ℝ; there is s ∈ S; there is u ∈ ℝ with u is an upper bound of S, and what it cites does not supply them",
        ),
        // False closed claims, and below them claims with no exact value, on
        // a requires line: the checker works out what `arithmetic` makes of
        // each (`check_arithmetic_holds`).
        case(
            "claim a false numeral fact with a number past one digit",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 10 − 1 = 3·4: arithmetic\n".to_string(),
            )],
            "the requires line 10 − 1 = 3·4 of step 1.3 is arithmetic, which is false",
        ),
        case(
            "claim a false numeral fact of digits",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 9 = 3·4: arithmetic\n".to_string(),
            )],
            "the requires line 9 = 3·4 of step 1.3 is arithmetic, which is false",
        ),
        case(
            "divide by zero in a numeral fact",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 3/0 ∈ ℝ: arithmetic\n".to_string(),
            )],
            "the requires line 3/0 ∈ ℝ of step 1.3 is arithmetic, which divides by zero",
        ),
        case(
            "state a numeral too large to work out",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 9^(9^9) ∈ ℕ: arithmetic\n".to_string(),
            )],
            "the requires line 9^(9^9) ∈ ℕ of step 1.3 is arithmetic, which is too large to work out",
        ),
        case(
            "raise a numeral to a power that is not whole",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 4^(1/2) ∈ ℕ: arithmetic\n".to_string(),
            )],
            "the requires line 4^(1/2) ∈ ℕ of step 1.3 is arithmetic, which is not a rational number: its exponent is not whole",
        ),
        case(
            "prove a false numeral fact by arithmetic",
            vec![edit(
                "tests/notations/numbers.proof",
                Some("  then 2³ = 8\n\n1.  2³ = 8\n".to_string()),
                "  then 2³ = 9\n\n1.  2³ = 9\n".to_string(),
            )],
            "step 1 claims 2³ = 9, which is false",
        ),
        // A substitution by a false fact of numerals, 0 − 1 = 1, which the
        // checker works out as `arithmetic` does.
        case(
            "substitute by a false fact of numerals",
            vec![edit(
                "proofs/binomial.proof",
                Some("substitute 0 − 1 = −1 (arithmetic)".to_string()),
                "substitute 0 − 1 = 1 (arithmetic)".to_string(),
            )],
            "step 33 takes 0 − 1 = 1 from arithmetic, which is false",
        ),
        // g(a) is the rule at a only where a is in g's domain [a, b]. That
        // is no number system, so no introducing line says it once, and
        // line 1, which does, is not named.
        case(
            "read a defined function at a value nothing puts in its domain",
            vec![edit(
                "proofs/mean-value.proof",
                Some("    D1, from 1\n".to_string()),
                "    D1\n".to_string(),
            )],
            "step 17 cites D1 at a, so it needs a ∈ [a, b], and nothing it cites or requires says it",
        ),
        // a ∈ S because S is the points of [a, b] where f is below zero; the
        // item speaks of a set written by its condition, and without the
        // define S is only a name.
        case(
            "membership in a defined set without citing its define",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("u := a, from D1, H6, 1".to_string()),
                "u := a, from H6, 1".to_string(),
            )],
            "step 2 claims something that mun:set-builder does not conclude",
        ),
        // Said of every member, a term's divisor must not be zero for each: k ∈ ℤ
        // gives no k ≠ 0.
        case(
            "membership said of every integer where a divisor may be zero",
            vec![edit(
                "proofs/triangular-reciprocals.proof",
                Some("requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: from 2".to_string()),
                "requires for all k ∈ ℤ, 1/T(k) ∈ ℝ: membership, from D1".to_string(),
            )],
            "the requires line for all k ∈ ℤ, 1/T(k) ∈ ℝ of step 8 cites D1 at k, so it needs k ∈ ℕ, and nothing it cites or the requires lines above it say it",
        ),
        // A membership line says what the table in `rules` says it does and
        // nothing more: k ∈ ℤ gives no k ≠ 0, and n ∈ ℝ gives no n ∈ ℤ, since
        // the table goes one way. A membership said once is carried up the
        // same table and never down: with n let into ℝ, nothing gives the
        // n ∈ ℤ that sum-telescopes asks of its range's end. Its bound line
        // goes too, as n ∈ ℝ gives no n + 1 ≥ 1 either, and would be reported
        // first. sum-termwise asks the same of its b := n, so step 2.1 is
        // where the citation is first refused.
        case(
            "a membership read for a bound it does not give",
            vec![edit(
                "proofs/triangular-reciprocals.proof",
                Some("    let k ∈ ℕ                                                         (K1)".to_string()),
                "    let k ∈ ℤ                                                         (K1)".to_string(),
            )],
            "step 1.2 cites D1 at k, so it needs k ∈ ℕ, and nothing it cites or requires says it",
        ),
        case(
            "a membership read into a smaller number system",
            vec![edit(
                "proofs/triangular-reciprocals.proof",
                Some("    let n ∈ ℕ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1, 2, 4\n\n    5.2.  Σ(k = 1 to n) (2/k − 2/(k + 1)) = 2 − 2/(n + 1)\n          thm:sum-telescopes a := 1, b := n, from 3\n          requires n + 1 ≥ 1: inequalities, from K5\n".to_string()),
                "    let n ∈ ℝ                                                         (K5)\n\n    5.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1, 2, 4\n\n    5.2.  Σ(k = 1 to n) (2/k − 2/(k + 1)) = 2 − 2/(n + 1)\n          thm:sum-telescopes a := 1, b := n, from 3\n".to_string(),
            )],
            "the statement says n ranges over ℕ, and this line puts it in ℝ",
        ),
        // A link naming `arithmetic` for a piece of numerals that is false,
        // 2/1 is not 3, with the claim changed to match: the checker works
        // the piece out as `arithmetic` does.
        case(
            "a chain link whose closed piece is false",
            vec![edit(
                "proofs/triangular-reciprocals.proof",
                Some("    5.3.  Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    5.1\n                                 = 2 − 2/(n + 1)                      5.2\n".to_string()),
                "    5.3.  Σ(k = 1 to n) 1/T(k) = 3 − 2/(n + 1)\n          calculation\n            Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))    5.1\n                                 = 2/1 − 2/(n + 1)                    5.2\n                                 = 3 − 2/(n + 1)                      arithmetic\n".to_string(),
            )],
            "names arithmetic for 2/1 − 2/(n + 1) = 3 − 2/(n + 1), which is false",
        ),
        // sum-divisible asks that 3 divide each term, and line 1 says it for
        // all k ∈ ℕ₀. Without line 1 cited nothing says it.
        case(
            "sum what no cited line says each term of is divisible",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("    mun:sum-divisible m := 3, from 1\n".to_string()),
                "    mun:sum-divisible m := 3\n".to_string(),
            )],
            "step 2 cites mun:sum-divisible, which asks for for all a ∈ ℕ₀, 3 divides d(a) · 10^a − d(a), and what it cites does not supply it",
        ),
        // A link of a calculation is what the line it cites says, and a line
        // saying something else is not taken for it.
        case(
            "cite a line for a link it does not say",
            vec![edit(
                "proofs/sum-formula.proof",
                Some("= k(k + 1)/2 + (k + 1)         1.5".to_string()),
                "= k(k + 1)/2 + (k + 1)         1.4".to_string(),
            )],
            "a link of step 1.7 cites 1.4, which does not say S(k) + (k + 1) = k(k + 1)/2 + (k + 1); a link cites the line that states it, and a substitution is a step of its own",
        ),
        // What says f is continuous is H5. Without it cited, the step unfolds
        // a continuity nothing it names says.
        case(
            "unfold continuity without the line saying f is continuous",
            vec![edit(
                "proofs/intermediate-value.proof",
                Some("    def:continuous-on, from H5".to_string()),
                "    def:continuous-on".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        // The item asks |X| = k + 1, which C2 says. Without C2 cited, the
        // equation is in scope and not in hand, and the hypothesis must go
        // unanswered rather than be answered by a line the step does not name.
        // C2 is also what binds the item's k, so k ∈ ℕ₀ goes unanswered with
        // it: the item's letter is not the proof's k said once by K2.
        case(
            "answer a side condition by an equation the step does not cite",
            vec![edit(
                "proofs/subsets.proof",
                Some("obtain a: mun:card-nonempty, from C2\n".to_string()),
                "obtain a: mun:card-nonempty\n".to_string(),
            )],
            "step 1.2.1 cites mun:card-nonempty, which asks for k ∈ ℕ₀; |X| = k + 1, and what it cites does not supply them",
        ),
        // What is put in an image comes from a cited line saying where the
        // map is read. With the line gone nothing says it.
        case(
            "put something in an image without the line saying where it comes from",
            vec![edit(
                "proofs/subsets.proof",
                Some("s := V ∖ {a},\n                    from 1.3.2".to_string()),
                "s := V ∖ {a}".to_string(),
            )],
            "step 1.3.3 cites mun:added-element-in-image, which asks for V ∖ {a} ∈ 𝒫(X ∖ {a}), and what it cites does not supply it",
        ),
        // Σ(a(k)t + b(k))² is t²Σa(k)² + 2tΣa(k)b(k) + Σb(k)², and with 3t
        // in place of 2t the `algebra` claim is no identity, which the
        // checker finds reading the sums as linear, as the build does.
        case(
            "expand a sum linearly with a wrong coefficient",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("    1.3.  Σ(k = 1 to n) (a(k)·t + b(k))² = t²·(Σ(k = 1 to n) a(k)²) + 2t·".to_string()),
                "    1.3.  Σ(k = 1 to n) (a(k)·t + b(k))² = t²·(Σ(k = 1 to n) a(k)²) + 3t·".to_string(),
            )],
            "is not an identity, nor does it follow from what step 1.3 cites",
        ),
        // A closed exponent that comes to −1, which is not in ℕ₀. The checker
        // does not work the exponent out; it reports the link below that
        // cites the changed line for what it no longer says.
        case(
            "a closed exponent that is not a whole number",
            vec![edit(
                "proofs/binomial.proof",
                Some("    1.1.  Σ(k = 0 to 0) C(0, k)·x^(0 − k)·y^k = C(0, 0)·x^0·y^0\n".to_string()),
                "    1.1.  Σ(k = 0 to 0) C(0, k)·x^((0 − 1) − k)·y^k = C(0, 0)·x^((0 − 1) − 0)·y^0\n".to_string(),
            )],
            "a link of step 1.6 cites 1.1, which does not say C(0, 0)·x^0·y^0 = Σ(k = 0 to 0) C(0, k)·x^(0 − k)·y^k; a link cites the line that states it, and a substitution is a step of its own",
        ),
        // A link reads its cited equation from either side, and nothing on the
        // page says which: line 2 says |CB| = |BC|, which is neither way round
        // the link's |CA| = |CB|.
        case(
            "cite an equation that says the link neither way round",
            vec![edit(
                "proofs/isosceles.proof",
                Some("           = |CB|       H5\n".to_string()),
                "           = |CB|       2\n".to_string(),
            )],
            "a link of step 3 cites 2, which does not say |CA| = |CB|; a link cites the line that states it, and a substitution is a step of its own",
        ),
        // A claim of u = a where the item says u ≠ a is not what it says.
        case(
            "claim what a lemma says with one relation changed",
            vec![edit(
                "tests/stdlib/sets.proof",
                Some("then u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n".to_string()),
                "then u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n".to_string(),
            )],
            "step 1 claims something that mun:sets-remove-member does not conclude",
        ),
        // A step citing a define by cases takes the case from a line it cites.
        // Here the only line cited says x ∈ A, which is h's domain and no case.
        case(
            "cite a define by cases from a line that does not say the case",
            vec![edit(
                "proofs/schroeder-bernstein.proof",
                Some("                  D2, from 8.2.1\n".to_string()),
                "                  D2, from 8.2.2\n".to_string(),
            )],
            "step 8.2.3 cites D2 and claims a value it does not give: no line it cites says whether a case's condition holds or fails",
        ),
        // An obtain from part-builder claims what K's condition says of the set
        // the cited line puts in K: K18 gives Y = aH, and Z = aH is another
        // claim.
        case(
            "obtain from part-builder a claim the condition does not give",
            vec![edit(
                "proofs/lagrange.proof",
                Some("    14.1. a ∈ G. Y = aH.\n".to_string()),
                "    14.1. a ∈ G. Z = aH.\n".to_string(),
            )],
            "step 14.4 takes Y = aH from 14.1, which does not say it",
        ),
        // An obtain from a definition reads its left side off a line it cites,
        // through a define's name where the line uses one: C9 says b ∈ R, and R
        // is f[C]. K7 says only that b is in B.
        case(
            "obtain from a definition citing no line that says its left side",
            vec![edit(
                "proofs/schroeder-bernstein.proof",
                Some("obtain x: mun:image u := b, Y := C, from C9, D1".to_string()),
                "obtain x: mun:image u := b, Y := C, from D1, K7".to_string(),
            )],
            "step 8.2.1 obtains from mun:image, which says there is one only from something the step does not cite",
        ),
        // g ∈ gH is shown by the member of H that g is g times, and the line
        // saying g·e = g is what names it.
        case(
            "a coset member with no line naming what it is the element times",
            vec![edit(
                "proofs/lagrange.proof",
                Some("mun:coset u := g, from H2, K3, 4.1, 4.2".to_string()),
                "mun:coset u := g, from H2, K3, 4.1".to_string(),
            )],
            "step 4.3 claims something that mun:coset does not conclude",
        ),
        // `inequalities` takes two terms differing only from a line it cites,
        // and not from a requires line above: 0 ≤ r alone gives no 0 < r.
        case(
            "rest an inequalities line on r ≠ 0 above it instead of citing it",
            vec![edit(
                "proofs/bezout.proof",
                Some("          requires 0 < r: inequalities, from S, 1\n".to_string()),
                "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n".to_string(),
            )],
            "the requires line of step 3.1 says r ≠ 0, and neither mun:pos-int-nat nor the step's other lines ask for it",
        ),
        // A method decides a word only where the word's record names it
        // (`DATABASE.md`, `decided`). With `inspection` struck from the
        // record of `odd`, Königsberg's count of its odd vertices asks it to
        // decide "is odd", which no line the count cites says.
        case(
            "a parity inspection decides with its record not naming it",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        n is odd ↔ there is k ∈ ℤ with n = 2k + 1\n  decided     arithmetic, inspection".to_string()),
                "  then        n is odd ↔ there is k ∈ ℤ with n = 2k + 1\n  decided     arithmetic".to_string(),
            )],
            "step 6 asks inspection to decide a word odd defines",
        ),
        // A line fills every hypothesis it says, so it is cited once.
        case(
            "cite one line twice in a step's list",
            vec![edit(
                "proofs/sqrt2-irrational.proof",
                Some("thm:divides-gcd a := p, b := q, from 3.1\n".to_string()),
                "thm:divides-gcd a := p, b := q, from 3.1, 3.1\n".to_string(),
            )],
            "step 3.2 cites 3.1 more than once",
        ),
        case(
            "cite one line twice in a requires line's list",
            vec![edit(
                "proofs/mean-value.proof",
                Some(
                    "    algebra, from 28\n    requires b − a ≠ 0: inequalities, from H1, H2, H3\n"
                        .to_string(),
                ),
                "    algebra, from 28\n    requires b − a ≠ 0: inequalities, from H1, H2, H1, H3\n"
                    .to_string(),
            )],
            "cites H1 more than once",
        ),
        // Labels come first and then lines, each in order.
        case(
            "cite a list out of order",
            vec![edit(
                "proofs/sqrt2-irrational.proof",
                Some("Q := n is odd, from 1, 2\n".to_string()),
                "Q := n is odd, from 2, 1\n".to_string(),
            )],
            "cites 2, 1 out of order",
        ),
        case(
            "cite a line before a label",
            vec![edit(
                "proofs/bezout.proof",
                Some("algebra, from H9, H10, 1\n".to_string()),
                "algebra, from 1, H9, H10\n".to_string(),
            )],
            "from H9, H10, 1",
        ),
        // A chain's congruence says what it is modulo, on its own line, and
        // every congruence of the chain says the same (`GRAMMAR.md`).
        case(
            "a congruence link that says no modulus",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("                       ≡ 1·10 (mod 3)     1.3".to_string()),
                "                       ≡ 1·10     1.3".to_string(),
            )],
            "says ≡ and not what modulo",
        ),
        case(
            "two congruence links modulo different numbers",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic".to_string()),
                "                       ≡ 1 (mod 9)        arithmetic".to_string(),
            )],
            "is a congruence modulo 9, and an earlier one modulo 3",
        ),
        case(
            "a congruence and an order in one chain",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("            10^0 = 1              arithmetic".to_string()),
                "            10^0 ≤ 1              arithmetic".to_string(),
            )],
            "joins a congruence with an order",
        ),
        // Once a chain says ≡, it says ≡ to the end: 1·10 = 10 holds, and is
        // written as a congruence after one.
        case(
            "go back to equality after a congruence",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("                       ≡ 10 (mod 3)       arithmetic".to_string()),
                "                       = 10               arithmetic".to_string(),
            )],
            "says = after a congruence",
        ),
        // That 3 is prime holds plainly, and the record of `prime` does not
        // say `arithmetic` decides it.
        case(
            "ask arithmetic to decide a word its record does not name it for",
            vec![edit(
                "proofs/divisibility-by-three.proof",
                Some("          requires 10^m ∈ ℤ: mun:power-integer a := 10\n".to_string()),
                "          requires 10^m ∈ ℤ: mun:power-integer a := 10\n          requires 3 is prime: arithmetic\n".to_string(),
            )],
            "is a word prime defines, and arithmetic decides a word only where its record says so",
        ),
        // A `decided` field names a method that decides words.
        case(
            "say a method decides a word that decides none",
            vec![edit(
                "corpus/stdlib/divisibility.records",
                Some("  then        n is even ↔ there is k ∈ ℤ with n = 2k\n  decided     arithmetic, inspection".to_string()),
                "  then        n is even ↔ there is k ∈ ℤ with n = 2k\n  decided     arithmetic, algebra".to_string(),
            )],
            "even says algebra decides it, and algebra decides no word",
        ),
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
            "asks for a(k) ∈ ℝ",
        ),
        // A function's type says its value is in the codomain only at a point
        // of its domain, so the line putting k in {1, …, n} is cited with it.
        case(
            "cite a function's type for a value without the point's domain",
            vec![edit(
                "proofs/cauchy-schwarz.proof",
                Some("mun:square-zero x := a(k), from H2, K4, 5.3.1".to_string()),
                "mun:square-zero x := a(k), from H2, 5.3.1".to_string(),
            )],
            "asks for a(k) ∈ ℝ",
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
        // A name one theorem gives is a let, and a name the file gives, which
        // another file may import, is a define (`SYNTAX.md`): each word stands
        // only where its name lives.
        case(
            "write define for a name one theorem gives",
            vec![
                edit("proofs/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "define B := {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "a define inside a theorem",
        ),
        case(
            "write let for a name the file gives",
            vec![
                edit("proofs/tri.proof", None, TRI.replacen("define T(k) := ", "let T(k) = ", 1)),
            ],
            "a let names a thing within a theorem",
        ),
        case(
            "say a let's name is a kind of number no record names",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("let m = gcd(s, w), a positive integer".to_string()), "let m = gcd(s, w), a whole number".to_string()),
            ],
            "and the kinds of number are",
        ),
        case(
            "say what kind of number a let's name is with no reason under it",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("    mun:gcd a := s, b := w, from 2, 28\n    reads the number whose square is s".to_string()), "    reads the number whose square is s".to_string()),
            ],
            "the line under it gives no reason",
        ),
        case(
            "give a let a reason that shows another term in the set",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("    mun:gcd a := t, b := w, from 2, 27".to_string()), "    mun:gcd a := s, b := w, from 2, 28".to_string()),
            ],
            "the reason under let D2 needs gcd(t, w) ∈ ℕ",
        ),
        case(
            "cite in a let's reason a step below the let",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("    mun:gcd a := t, b := w, from 2, 27".to_string()), "    mun:gcd a := t, b := w, from 27, 49".to_string()),
            ],
            "the reason under let D2 cites 49, which is not above the let",
        ),
        case(
            "say what kind of number a let in a theorem's statement names",
            vec![
                edit("proofs/birthday.proof", Some("  let S = the functions from {1, …, 23} to {1, …, 365}                (D1)\n".to_string()), "  let S = |{1, …, 23}|, a natural number                              (D1)\n    mun:range-size a := 1, b := 23\n".to_string()),
            ],
            "a let in a theorem's statement says no kind of number",
        ),
        case(
            "say what kind of number a define's name is",
            vec![
                edit("proofs/tri.proof", None, TRI.replacen("k(k + 1)/2, for k ∈ ℕ", "1, a natural number", 1).replacen("T(k) :=", "T :=", 1)),
            ],
            "a define says no kind of number",
        ),
        case(
            "say what kind of number a let's function is",
            vec![
                edit("proofs/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B(x) = x, a natural number".to_string()),
            ],
            "and a function is no number",
        ),
        case(
            "give a let's name with :=",
            vec![
                edit("proofs/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B := {x ∈ A : x ∉ f(x)}".to_string()),
            ],
            "a let names with `=`",
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
        // odd is about n, the proof has N and no n, and the fold from N = 2j + 1
        // gives n no value.
        case(
            "fold a definition about a letter the proof does not have",
            vec![edit(
                "proofs/odd-letter.proof",
                None,
                "import mundane definition stdlib/divisibility/odd\n\ntheorem odd-letter\n  let N ∈ ℤ            (H1)\n  let j ∈ ℤ            (H2)\n  assume N = 2j + 1    (H3)\n  then N is odd\n\n1.  N is odd\n    mun:odd, from H3\n".to_string(),
            )],
            "mun:odd is about n, and the step gives n no value and the proof has no n; write it, as n := t",
        ),
        // A mod 1 = A − 1·⌊A/1⌋ with its identity elements dropped is the
        // claim, and dropping 1· asks that ⌊A⌋ be a number, which only the
        // requires line says.
        case(
            "drop an identity element from what no line says is a number",
            vec![edit(
                "tests/elaborator/mod-on-the-reals.proof",
                Some("    requires 1 > 0: arithmetic\n    requires ⌊A⌋ ∈ ℤ: mun:floor-integer x := A\n".to_string()),
                "    requires 1 > 0: arithmetic\n".to_string(),
            )],
            "step 1 drops an identity element from what mun:mod-value concludes, and nothing says ⌊A⌋ is a number; a requires line says it",
        ),
        case(
            "join a sentence no joined line says",
            vec![edit(
                "proofs/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1".to_string(),
            )],
            "which no line it joins says",
        ),
        case(
            "join a line the claim says nothing of",
            vec![edit(
                "proofs/euclid.proof",
                Some("    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 3.1, 3.2".to_string()),
                "    3.3.  a(0) ∈ ℕ₀ and b(0) ∈ ℕ₀\n          join 1, 3.1, 3.2".to_string(),
            )],
            "step 3.3 joins 1, and claims nothing it says",
        ),
        // A letter introduced in a range is an integer said once, and a line
        // writing it says what the step's other lines already do.
        case(
            "a requires line writing a range member's integrality",
            vec![edit(
                "tests/elaborator/a-range-member-is-cited.proof",
                Some("    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n".to_string()),
                "    requires k ∈ ℤ: membership\n    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n".to_string(),
            )],
            "the requires line of step 1 says k ∈ ℤ, which the step's other lines already say",
        ),
        // No function is typed over {0, …, N}, so H2 is cited for k ∈ ℤ, which
        // the range says once, and binomial-nat0 asks nothing more of it.
        case(
            "an item's requires line naming a range let only for its integrality",
            vec![edit(
                "tests/elaborator/a-range-member-is-cited.proof",
                Some("    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n".to_string()),
                "    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0, from H2\n".to_string(),
            )],
            "the requires line of step 1 cites H2, and mun:binomial-nat0 asks for nothing it says",
        ),
        // The block's last step is the cases step, not the last step of its
        // last case, and it must name what it contradicts.
        case(
            "a contradiction ending in a cases step that names no line",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("          cases, from H2, contradicting S\n".to_string()),
                "          cases, from H2\n".to_string(),
            )],
            "step 1.1 ends a contradiction block and does not say which line it contradicts",
        ),
        // A substitution's equation is part of the line it names.
        case(
            "substitute an equation from a line that does not say it",
            vec![edit(
                "tests/notations/integrals.proof",
                Some("    substitute F(1) = 1² (line 9) into line 6\n".to_string()),
                "    substitute F(1) = 1² (line 10) into line 6\n".to_string(),
            )],
            "step 11 takes F(1) = 1² from 10, which does not say it",
        ),
        // A define written in one case is no define of the next.
        case(
            "cite a define written in an earlier case",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("    assume x = 2                                                      (C2)\n\n    1.3.  x > 0\n          inequalities, from C2\n".to_string()),
                "    assume x = 2                                                      (C2)\n\n    1.3.  y = x + 1\n          D1\n\n    1.4.  x > 0\n          inequalities, from C2\n".to_string(),
            )],
            "step 1.3 cites D1, which is not in scope here",
        ),
        // What one case shows is no line of the next.
        case(
            "cite a step of an earlier case",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("                  inequalities, from C2\n".to_string()),
                "                  inequalities, from 1.1.1\n".to_string(),
            )],
            "step 1.1.2 cites line 1.1.1, which is in another part of the block",
        ),
        // Step numbers are whole numbers joined by dots.
        case(
            "number a step with a letter",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("1.  b ≤ a\n    inequalities, from H4, H5\n".to_string()),
                "1a. b ≤ a\n    inequalities, from H4, H5\n".to_string(),
            )],
            "`1a.` is no step number",
        ),
        // The item's domain is a's, {1, …, n}, though the step cites a's type:
        // k ∈ ℤ, said once, does not put k in it.
        case(
            "a function's value cited from its type without the point's line",
            vec![edit(
                "tests/elaborator/a-range-a-function-is-typed-over.proof",
                Some("    mun:function-value f := a, from H3\n".to_string()),
                "    mun:function-value f := a, from H2\n".to_string(),
            )],
            "step 1 cites mun:function-value, which asks for x ∈ {1, …, n}, and what it cites does not supply it",
        ),
        // A letter's membership is said once, so a line naming the let that
        // introduces it, for nothing more, names a line it uses nothing of.
        case(
            "a requires line from a function's type naming the let of its point",
            vec![edit(
                "proofs/reals-uncountable.proof",
                Some("          membership, from 16.4, 16.5\n          requires d(n) ∈ ℤ: from H1\n".to_string()),
                "          membership, from 16.4, 16.5\n          requires d(n) ∈ ℤ: from H1, K6\n".to_string(),
            )],
            "the requires line of step 16.7 cites K6, and d(n) ∈ ℤ needs nothing it says",
        ),
        case(
            "an instantiation naming the let of the letter it puts in",
            vec![edit(
                "tests/notations/calculus.proof",
                Some("                  instantiate x := x in H2\n".to_string()),
                "                  instantiate x := x in H2, from K2\n".to_string(),
            )],
            "step 1.2.1 cites K2, and no value it puts in line H2 needs what it says",
        ),
        case(
            "drop an identity element a substitution makes from what no line says is a number",
            vec![edit(
                "tests/elaborator/an-identity-a-substitution-makes.proof",
                Some("    substitute 1^k = 1 (H3)\n    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n".to_string()),
                "    substitute 1^k = 1 (H3)\n".to_string(),
            )],
            "step 1 drops an identity element from what the substitution makes, and nothing says C(N, k) is a number; a requires line says it",
        ),
        case(
            "a link dropping an identity element from what no line says is a number",
            vec![edit(
                "tests/elaborator/an-identity-a-link-drops.proof",
                Some("    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n".to_string()),
                String::new(),
            )],
            "a link of step 1 drops an identity element from C(N, k), which nothing the step names says is a number; a requires line of the step says it",
        ),
        case(
            "cite an item for a function whose let gives it no type, naming no line that does",
            vec![edit(
                "tests/elaborator/a-type-a-line-states.proof",
                Some("    mun:function-value f := F, from H4, H5\n".to_string()),
                "    mun:function-value f := F, from H5\n".to_string(),
            )],
            "step 1 cites mun:function-value, which asks F : A → B, and no line the step names gives F a type; cite the line stating it, or say it in a requires line",
        ),
        // A hypothesis not supplied is said at what the claim fixes, so the
        // instance shows the disjuncts the wrong way round.
        case(
            "cite disjunctive syllogism with its disjuncts the wrong way round",
            vec![edit(
                "proofs/sqrt2-irrational.proof",
                Some("2.  n is even or n is odd\n    mun:even-or-odd\n\n3.  n is even\n    mun:disjunctive-syllogism P := n is even, Q := n is odd, from 1, 2".to_string()),
                "2.  n is odd or n is even\n    mun:even-or-odd\n\n3.  n is even\n    mun:disjunctive-syllogism, from 1, 2".to_string(),
            )],
            "step 3 cites mun:disjunctive-syllogism, which asks for n is even or Q",
        ),
        // A case with no steps says it is the claim; one that does not is
        // reported where it is, not where the step after it lands.
        case(
            "a last case with no steps that does not say it is the claim",
            vec![edit(
                "proofs/cantor.proof",
                Some("assume x ∉ B, which is the claim                    (C2)".to_string()),
                "assume x ∉ B                    (C2)".to_string(),
            )],
            "this case of step 2.1.2 has no steps, and its assumption does not say it is the claim; write its steps, or end the line `, which is the claim`",
        ),
        // A substitution puts one side for the other and reorders nothing.
        case(
            "substitute into a line, claiming its product the other way round",
            vec![edit(
                "proofs/bezout.proof",
                Some("4.  c = q·d\n    substitute r = 0 (line 3) into line 1".to_string()),
                "4.  c = d·q\n    substitute r = 0 (line 3) into line 1".to_string(),
            )],
            "step 4 claims c = d · q, which putting one side of r = 0 for the other does not make",
        ),
        case(
            "substitute with no line, claiming more than the equation puts in",
            vec![edit(
                "proofs/binomial.proof",
                Some("    1.3.  C(0, 0)·x^0·y^0 = x^0·y^0\n".to_string()),
                "    1.3.  C(0, 0)·x^0·y^0 = x^0·y^1\n".to_string(),
            )],
            "step 1.3 claims C(0, 0) · x^0 · y^0 = x^0 · y^1, which putting one side of C(0, 0) = 1 for the other does not make",
        ),
        case(
            "cite a line that comes after the step",
            vec![
                edit("proofs/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.3".to_string()),
            ],
            "step 16.2 cites line 16.3, which comes after it",
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
        // One substitution takes one equation from one source: a second
        // would be read as part of the first equation.
        case(
            "two substitutions in one step",
            vec![
                edit("proofs/angle-sum.proof", Some("    substitute ∠DBA = ∠BAC (line 2)\n".to_string()), "    substitute ∠DBA = ∠BAC (line 2), ∠EBC = ∠BCA (line 3)\n".to_string()),
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
                edit("proofs/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    def:even-or-odd\n".to_string()),
            ],
            "def:even-or-odd names a mundane",
        ),
        case(
            "cite a mundane item as a theorem",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    mun:even-or-odd\n".to_string()), "    thm:even-or-odd\n".to_string()),
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
        // A conclusion is matched with an identity element dropped where the
        // instance has one, and with nothing else changed: the shifted sum
        // starts at 0 + 1, which is 1 and not 2.
        case(
            "claim a lemma's conclusion with more than an identity element dropped",
            vec![
                edit("proofs/binomial.proof", Some("29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 1 to m + 1)".to_string()), "29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 2 to m + 1)".to_string()),
            ],
            "step 29 claims something that mun:sum-shift does not conclude",
        ),
        // 0 is an identity on the right of a difference and not on its left:
        // C(m, 0 − 1) is not C(m, −1) by any identity law.
        case(
            "drop a 0 from the side of a difference where it is no identity",
            vec![
                edit("proofs/binomial.proof", Some("= C(m, 0 − 1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()), "= C(m, −1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()),
            ],
            "step 38 claims something that mun:sum-first does not conclude",
        ),
        // A set-builder's equation needs no line where it is the same on both
        // sides once its witnesses are read off, and one where it is not:
        // a·x + b·y + 1 = a·m + b·n has no m and n of that shape.
        case(
            "a set-builder's equation that no witness makes the same on both sides",
            vec![
                edit("proofs/bezout.proof", Some("    8.1.  a·x + b·y ∈ S\n          mun:set-builder u := a·x + b·y, from D1, K3\n".to_string()), "    8.1.  a·x + b·y + 1 ∈ S\n          mun:set-builder u := a·x + b·y + 1, from D1, K3\n".to_string()),
            ],
            "step 8.1",
        ),
        // `requires C ≠ A: mun:triangle` unfolds a line saying A, B, C form a
        // triangle; cited, that line is what it rests on, and without it
        // nothing is.
        case(
            "unfold a triangle no line above says",
            vec![
                edit("proofs/pythagoras.proof", Some("    requires C ≠ A: mun:triangle, from H4\n".to_string()), "    requires C ≠ A: mun:triangle\n".to_string()),
            ],
            "the requires line of step 2 needs something that mun:triangle does not conclude",
        ),
        // A requires line's item asks for what the lines it cites supply:
        // `mod-natural` asks b ∈ ℕ, and without 4.6.9, which says b(k) ∈ ℕ,
        // the line says what is missing rather than that the item concludes
        // something else.
        case(
            "a requires line whose item's hypothesis nothing supplies",
            vec![
                edit("proofs/euclid.proof", Some("requires a(k) mod b(k) ∈ ℕ₀: mun:mod-natural, from 4.6.9, 4.6.10\n".to_string()), "requires a(k) mod b(k) ∈ ℕ₀: mun:mod-natural, from 4.6.10\n".to_string()),
            ],
            "the requires line of step 4.6.12 cites mun:mod-natural, which asks for",
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
        // It is for the letter the claim binds, and no other.
        case(
            "an induction hypothesis for another letter",
            vec![
                edit("proofs/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 1 is true for j".to_string()),
            ],
            "the induction hypothesis is for j, and step 1 is said for all k",
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
        // Each part of a block ends on what it owes (`SYNTAX.md`): the base
        // on the claim's statement at the start, the step on it at k + 1, a
        // case on the block's claim, a proof block on its claim with what
        // its openers took off it. Each of these stops one line short.
        case(
            "an induction's base that stops short of the claim's first instance",
            vec![
                edit("proofs/sum-formula.proof", Some("    1.2.  S(1) = 1(1 + 1)/2\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     1.1\n                 = 1(1 + 1)/2            arithmetic".to_string()), "    1.2.  S(1) = 1\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     1.1".to_string()),
            ],
            "step 1.2 ends the base part of step 1, which owes",
        ),
        case(
            "an induction's step that stops short of the next instance",
            vec![
                edit("proofs/sum-formula.proof", Some("    1.7.  S(k + 1) = (k + 1)((k + 1) + 1)/2\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.4\n                     = k(k + 1)/2 + (k + 1)         1.5\n                     = (k + 1)((k + 1) + 1)/2       1.6".to_string()), "    1.7.  S(k + 1) = k(k + 1)/2 + (k + 1)\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.4\n                     = k(k + 1)/2 + (k + 1)         1.5".to_string()),
            ],
            "step 1.7 ends the step part of step 1, which owes",
        ),
        case(
            "a case that stops short of the block's claim",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    2.4.  x ≤ |x|. −x ≤ |x|.\n          join 2.2, 2.3\n\n    case\n    assume x < 0".to_string()), "    case\n    assume x < 0".to_string()),
            ],
            "step 2.3 ends case 1 of step 2, which owes",
        ),
        case(
            "a proof block that stops short of its claim",
            vec![
                edit("proofs/reals-uncountable.proof", Some("    4.8.  L(k) ∈ ℝ. U(k) ∈ ℝ. L(k) ≤ U(k).\n          join 4.3, 4.4, 4.7".to_string()), "    4.8.  L(k) ∈ ℝ. U(k) ∈ ℝ.\n          join 4.3, 4.4".to_string()),
            ],
            "step 4.8 ends the proof block of step 4, which owes",
        ),
        // What an obtain claims is the "there is" it obtains from, the line
        // it names or what the item gives (`SYNTAX.md`), and no more.
        case(
            "an obtain from a line that claims more than the line's there is",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    3.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()), "    3.1.  d ∈ ℤ. d > 2. d divides p. d divides q.".to_string()),
            ],
            "step 3.1 claims other than what it obtains, which says",
        ),
        case(
            "an obtain from an item that claims more than the item's there is",
            vec![
                edit("proofs/bezout.proof", Some("4.  d ∈ S. For all s ∈ S, d ≤ s.".to_string()), "4.  d ∈ S. For all s ∈ S, d < s.".to_string()),
            ],
            "step 4 claims other than what it obtains, which says",
        ),
        case(
            "an obtain whose membership is not the one its there is gives",
            vec![
                edit("proofs/harmonic.proof", Some("    2.2.  B ∈ ℝ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.".to_string()), "    2.2.  B ∈ ℚ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.".to_string()),
            ],
            "step 2.2 claims B ∈ ℚ, and what it obtains says B ∈ ℝ",
        ),
        case(
            "an obtain from a line that says no there is",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("          obtain k, m, n from D2".to_string()), "          obtain k, m, n from H1".to_string()),
            ],
            "step 1.2 obtains k, m, n from a line that says no \"there is\" of as many",
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
                edit("proofs/cantor.proof", Some("  let A be a set                                                      (H1)".to_string()), "  let A ≠ B                                                           (H1)".to_string()),
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
        // Line 15 of intermediate-value still binds δ once c′ and ε are given,
        // so a value naming δ would be caught by it.
        case(
            "substitute a term that captures a bound variable",
            vec![
                edit("proofs/intermediate-value.proof", Some("           instantiate c′ := c, ε := −f(c) in line 15, from H4, 13, 16.3".to_string()), "           instantiate c′ := c, ε := −f(δ) in line 15, from H4, 13, 16.3".to_string()),
            ],
            "may not capture",
        ),
        // The same, with a comma inside the value: the pair is read whole.
        case(
            "substitute a term with a comma that captures a bound variable",
            vec![
                edit("proofs/intermediate-value.proof", Some("           instantiate c′ := c, ε := −f(c) in line 15, from H4, 13, 16.3".to_string()), "           instantiate c′ := c, ε := −f(c)·|[δ, c]| in line 15, from H4, 13, 16.3".to_string()),
            ],
            "may not capture",
        ),
        case(
            "obtain a name without stating its sort",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("1.  k ∈ ℤ. n = 2k + 1.\n    obtain k: mun:odd, from H2".to_string()), "1.  n = 2k + 1.\n    obtain k: mun:odd, from H2".to_string()),
            ],
            "without stating its sort",
        ),
        case(
            "write a claim in a notation nobody declared",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("4.  p > 1\n    mun:prime, from 3".to_string()), "4.  p exceeds 1\n    mun:prime, from 3".to_string()),
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
            "does not supply",
        ),
        // `mod-natural` asks b ∈ ℕ, and IH1 says b(k) ∈ ℕ₀: a function's
        // value is in what a line says it is in, and ℕ₀ holds 0.
        case(
            "supply a hypothesis with the wrong number system",
            vec![
                edit("proofs/euclid.proof", Some("mun:mod-natural, from 3.5.8\n".to_string()), "mun:mod-natural, from IH1\n".to_string()),
            ],
            "does not supply",
        ),
        case(
            "stop declaring which pattern is a negation of which",
            vec![
                edit("corpus/db/notation.records", Some("  level       predicate\n  negates     pattern 3 is logical-not of pattern 2".to_string()), "  level       predicate".to_string()),
            ],
            "does not supply",
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
            "the requires line of step 3 cites mun:sqrt, which asks for 0 ≤ 2, and what it cites does not supply it",
        ),
        case(
            "claim something the cited item does not conclude",
            vec![
                edit("proofs/infinitely-many-primes.proof", Some("4.  p > 1\n    mun:prime, from 3".to_string()), "4.  p > 2\n    mun:prime, from 3".to_string()),
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
                edit("proofs/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B(y) = {x ∈ A : x ∉ f(x)}".to_string()),
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
                edit("proofs/cantor.proof", Some("let B = {x ∈ A : x ∉ f(x)}".to_string()), "let B = {x ∈ A : x ∉ f(x)}, for y ∈ A".to_string()),
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
                edit("proofs/pythagorean-triples.proof", Some("          mun:divides d := 2, n := 1, from 8.5\n".to_string()), "          mun:divides d := 2, n := 1, from 8.5, contradicting 8.5\n".to_string()),
            ],
            "says it is impossible and contradicts a line",
        ),
        case(
            "say a claim with a letter in it is impossible",
            vec![
                edit("proofs/reals-uncountable.proof", Some("    2.3.  10 divides 1, which is impossible\n".to_string()), "    2.3.  10 divides t, which is impossible\n".to_string()),
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
            "case C7 says it is the claim of step 10, and it is not",
        ),
        case(
            "say a case with steps is the claim",
            vec![
                edit("proofs/euclid.proof", Some("assume b(N) ≠ 0                                                   (C8)".to_string()), "assume b(N) ≠ 0, which is the claim                               (C8)".to_string()),
            ],
            "case C8 is the claim and has steps of its own",
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
                edit("proofs/harmonic.proof", Some("    exhibit, from 5, 6\n".to_string()), "    exhibit, from 5\n".to_string()),
            ],
            "step 7 exhibits n := 2^N, so it needs 2^N ∈ ℕ",
        ),
        // A requires line rests on the lines above it, read top to bottom
        // (`SYNTAX.md`). Written first, |numer(x)| ∈ ℕ₀ asks for numer(x) ∈ ℤ,
        // which no line above it states.
        case(
            "a requires line resting on one written below it",
            vec![
                edit("proofs/rationals-countable.proof", Some("    requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n    requires denom(x) ∈ ℕ: mun:lowest-terms-parts\n    requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n".to_string()), "    requires |numer(x)| ∈ ℕ₀: mun:abs-integer z := numer(x)\n    requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n    requires denom(x) ∈ ℕ: mun:lowest-terms-parts\n".to_string()),
            ],
            "the requires line of step 5 cites mun:abs-integer, which asks for numer(x) ∈ ℤ, and what it cites does not supply it",
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
                edit("tests/elaborator/induction-under-a-condition.proof", Some("mun:count-step-holds k := j, from D1, 1.2.12.7\n".to_string()), "mun:count-step-holds k := j, from D1, 1.2.12.3, 1.2.12.7\n".to_string()),
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
                edit("proofs/intermediate-value.proof", Some("    obtain c: axi:completeness, from 2, 5, 7".to_string()), "    obtain c: axi:completeness, from 5, 7".to_string()),
            ],
            "step 8 cites axi:completeness, which asks for",
        ),
        case(
            "obtain from an item and cite a line it does not ask for",
            vec![
                edit("proofs/intermediate-value.proof", Some("    obtain c: axi:completeness, from 2, 5, 7".to_string()), "    obtain c: axi:completeness, from H3, 2, 5, 7".to_string()),
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
                edit("proofs/sqrt2-irrational.proof", Some("    obtain k: mun:odd, from H2".to_string()), "    obtain k: mun:odd".to_string()),
            ],
            "step 1 obtains from mun:odd, which says there is one only from",
        ),
        // Pascal's rule pairs C(n, k) with C(n, k − 1). The other neighbour is
        // the mistake a reader makes when the index shift goes the wrong way.
        case(
            "Pascal with the shift going the wrong way",
            vec![
                edit("proofs/binomial.proof", Some("    44.3.  C(m, k) + C(m, k − 1) = C(m + 1, k)\n".to_string()), "    44.3.  C(m, k) + C(m, k + 1) = C(m + 1, k)\n".to_string()),
            ],
            "step 44.3 claims something that thm:pascal does not conclude",
        ),
        // Shifting the index moves the range with it.
        case(
            "a shifted sum left over the range it came from",
            vec![
                edit("proofs/binomial.proof", Some("29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 1 to m + 1)".to_string()), "29. Σ(k = 0 to m) C(m, k)·x^(m − k)·y^(k + 1) = Σ(k = 0 to m)".to_string()),
            ],
            "step 29 claims something that mun:sum-shift does not conclude",
        ),
        // A line saying something of every index from 0 to m says nothing of
        // the index m + 1, which the sum to m + 1 takes.
        case(
            "a term-by-term line over too short a range",
            vec![
                edit("proofs/binomial.proof", Some("    mun:sum-termwise a := 0, b := m + 1, from 44\n".to_string()), "    mun:sum-termwise a := 0, b := m + 1, from 10\n".to_string()),
            ],
            "step 45 cites mun:sum-termwise, which asks for",
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
                edit("proofs/binomial.proof", Some("    30.1.  m − (k − 1) = (m + 1) − k\n           algebra\n".to_string()), "    30.1.  m − (k − 1) = (m + 1) − k\n           algebra\n           requires (m + 1) − k ∈ ℕ₀: mun:range-difference a := 0, n := m + 1, from J\n".to_string()),
            ],
            "the requires line of step 30.1 cites mun:range-difference",
        ),
        // `arithmetic` may stand where a closed-numeral fact is used, and only
        // there: an equation with a letter in it gives a reader something to
        // check, and is a numbered step. `SYNTAX.md` has the rule.
        case(
            "take an equation with a letter in it from arithmetic",
            vec![
                edit("proofs/binomial.proof", Some("substitute m − (k − 1) = (m + 1) − k (line 30.1)".to_string()), "substitute m − (k − 1) = (m + 1) − k (arithmetic)".to_string()),
            ],
            "takes m − (k − 1) = (m + 1) − k from arithmetic, and it has a letter in it",
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
                edit("proofs/triangular-reciprocals.proof", Some("    5.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1, 2, 4\n".to_string()), "    5.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          membership, from 1\n".to_string()),
            ],
            "names membership for",
        ),
        // A line said of every k ∈ ℕ answers a hypothesis over {1, …, n}, and not
        // one over {0, …, n}: the table puts the first range inside ℕ and not
        // the second.
        case(
            "a for-every line over a set that does not hold the range",
            vec![
                edit("proofs/triangular-reciprocals.proof", Some("    5.1.  Σ(k = 1 to n) 1/T(k) = Σ(k = 1 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 1, b := n, from 1, 2, 4\n".to_string()), "    5.1.  Σ(k = 0 to n) 1/T(k) = Σ(k = 0 to n) (2/k − 2/(k + 1))\n          mun:sum-termwise a := 0, b := n, from 1, 2, 4\n".to_string()),
            ],
            "step 5.1 cites mun:sum-termwise, which asks",
        ),
        // What a summand's function hypothesis asks is the membership of the
        // names the summand is built from, and asks nothing of 1 > 0.
        case(
            "a requires line the summand does not ask for",
            vec![
                edit("proofs/binomial.proof", Some("    mun:sum-scaled a := 0, b := m, c := x\n".to_string()), "    mun:sum-scaled a := 0, b := m, c := x\n    requires 1 > 0: arithmetic\n".to_string()),
            ],
            "says 1 > 0, and neither mun:sum-scaled nor",
        ),
        // A hypothesis asking a = b is answered by a line saying b = a, and by
        // nothing else: line 2 says |CB| = |BC|, which is neither way round the
        // |CB| = |CA| side-angle-side asks for.
        case(
            "answer an equation with one that says it neither way round",
            vec![
                edit("proofs/isosceles.proof", Some("      from H4, H5, 3, 4\n".to_string()), "      from H4, 2, 3, 4\n".to_string()),
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
                edit("proofs/konigsberg.proof", Some("requires S ⊆ {1, …, n}: mun:set-builder-subset, from D1\n".to_string()), "requires S ⊆ {1, …, n}: mun:set-builder-subset\n".to_string()),
            ],
            "the requires line of step 8 needs something that mun:set-builder-subset does not conclude",
        ),
        // So is a define from outside the theorem, here one imported: C(1)
        // is C applied, and tri-one concludes it of T's rule only where the
        // step cites C's define.
        case(
            "lean on an imported define the step does not cite",
            vec![
                edit("proofs/tri.proof", None, TRI.to_string()),
                edit(
                    "proofs/tri-use.proof",
                    None,
                    "import theorem proofs/tri/tri-one\nimport definition proofs/tri/T as C (D1)\n\ntheorem use-one\n  then C(1) = 1\n\n1.  C(1) = 1\n    thm:tri-one\n".to_string(),
                ),
            ],
            "step 1 claims something that thm:tri-one does not conclude",
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
                edit("proofs/schroeder-bernstein.proof", Some("                  mun:disjoint-member, from K7, 7.2.2, contradicting 7.2.1\n".to_string()), "                  mun:disjoint-member, from 7.2.2, contradicting 7.2.1\n".to_string()),
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
        // gH is read as a coset of a subgroup, and the step cites the line
        // that says H is one.
        case(
            "read a coset without saying H is a subgroup",
            vec![
                edit("proofs/lagrange.proof", Some("          mun:coset u := g, from H2, K3, 4.1, 4.2\n".to_string()), "          mun:coset u := g, from K3, 4.1, 4.2\n".to_string()),
            ],
            "step 4.3 cites mun:coset, which asks for H is a subgroup of G",
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
        // A requires line says what the step's other lines do not: m − k ∈ ℕ₀
        // above already says m − k is real.
        case(
            "repeat a fact a line above already says",
            vec![
                edit("proofs/binomial.proof", Some("          requires m − k ∈ ℕ₀: mun:range-difference a := 0, n := m, from J\n          requires x^(m − k) ∈ ℝ: mun:power-real, from H1\n".to_string()), "          requires m − k ∈ ℕ₀: mun:range-difference a := 0, n := m, from J\n          requires m − k ∈ ℝ: membership\n          requires x^(m − k) ∈ ℝ: mun:power-real, from H1\n".to_string()),
            ],
            "the requires line of step 10.6 says m − k ∈ ℝ, which the step's other lines already say",
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
                edit("proofs/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = M,".to_string()),
            ],
            "b has no value at 0",
        ),
        case(
            "give a sequence its first value at 1",
            vec![
                edit("proofs/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = M,  b(1) = N,".to_string()),
            ],
            "b(1) is neither b(0) nor b(k + 1)",
        ),
        case(
            "write a step rule that names the value it defines",
            vec![
                edit("proofs/euclid.proof", Some("  a(k + 1) = a(k)             if b(k) = 0".to_string()), "  a(k + 1) = a(k + 1)         if b(k) = 0".to_string()),
            ],
            "names a at a place other than k",
        ),
        case(
            "take cases from a disjunction in the other order",
            vec![
                edit("proofs/euclid.proof", Some("    3.4.  b(k) = 0 or b(k) ≠ 0".to_string()), "    3.4.  b(k) ≠ 0 or b(k) = 0".to_string()),
            ],
            "step 3.5 takes its cases from 3.4, which does not claim their assumptions joined by \"or\", in the order the cases take them",
        ),
        case(
            "give a first value in terms of the index",
            vec![
                edit("proofs/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = k,  b(0) = N,".to_string()),
            ],
            "names k, which has no value at 0",
        ),
        case(
            "give a first value in terms of a sequence",
            vec![
                edit("proofs/euclid.proof", Some("let a(0) = M,  b(0) = N,".to_string()), "let a(0) = b(0),  b(0) = N,".to_string()),
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
                edit("proofs/euclid.proof", Some("3.5.1.  a(k + 1) = a(k)".to_string()), "3.5.1.  a(k + 1) = b(k)".to_string()),
            ],
            "step 3.5.1 cites D1 and claims a value it does not give",
        ),
        case(
            "cite a step rule by cases without saying which case",
            vec![
                edit("proofs/euclid.proof", Some("3.5.7.  b(k + 1) = a(k) mod b(k)\n                  D1, from C2".to_string()), "3.5.7.  b(k + 1) = a(k) mod b(k)\n                  D1".to_string()),
            ],
            "says whether a case's condition holds",
        ),
        // A calculation's link cites the line that says it, and a line saying
        // a(0) = M does not say what substituting it inside a gcd gives.
        case(
            "cite an equation for a link that substitutes it inside a term",
            vec![
                edit("proofs/euclid.proof", Some("            gcd(a(0), b(0)) = gcd(M, b(0))     4.1".to_string()), "            gcd(a(0), b(0)) = gcd(M, b(0))     1".to_string()),
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
            "step 8 cites mun:function-into, which asks for for all x ∈ S, f(x) ∈ ℕ, and what it cites does not supply it",
        ),
        case(
            "reorder a product by a map not shown to be one-to-one",
            vec![
                edit("proofs/euler.proof", Some("thm:product-reorder, from 4, 5, 9".to_string()), "thm:product-reorder, from 4, 5, 8".to_string()),
            ],
            "step 10 cites thm:product-reorder, which asks for",
        ),
        // `let p be a polynomial` says p is one, and an item asking that of
        // what it is cited at asks it of the lines the step names.
        case(
            "divide by x − a without saying p is a polynomial",
            vec![
                edit("proofs/factor.proof", Some("thm:remainder, from H1".to_string()), "thm:remainder".to_string()),
            ],
            "step 1 cites thm:remainder, which asks for p is a polynomial",
        ),
        // `inequalities` takes two terms differing only from a line it cites:
        // r ≠ 0 written above for 0 < r to rest on is asked for by nothing.
        case(
            "write r ≠ 0 above an inequalities line instead of citing it",
            vec![
                edit("proofs/bezout.proof", Some("          requires 0 < r: inequalities, from S, 1\n".to_string()), "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n".to_string()),
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
            "step 6.2 cites mun:coprime-product, which asks for r ∈ ℤ",
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
            "step 1 cites mun:square-nonneg, which asks for x / y ∈ ℝ",
        ),
        // A define's name is not a letter introduced in a number system:
        // that x₁ is real rests on min-real, and abs-difference-lt asks it.
        case(
            "leave out a define's membership where an item asks it",
            vec![
                edit("proofs/intermediate-value.proof", Some("    let x₁ = min(b, c + δ/2), a real number                            (D2)\n           mun:min-real x := b, y := c + δ/2\n".to_string()), "    let x₁ = min(b, c + δ/2)                                           (D2)\n".to_string()),
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
                edit("proofs/geometric-series.proof", Some("    1.2.  a^0 = 1\n          mun:exponent-zero\n".to_string()), "    1.2.  a^0 = 1\n          mun:exponent-zero, from H1\n".to_string()),
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
        case(
            "an exhibit citing nothing that says the claim of a value",
            vec![
                edit("proofs/bezout.proof", Some("    exhibit, from 19\n".to_string()), "    exhibit, from 17\n".to_string()),
            ],
            "step 20 exhibits a value, and nothing it cites or requires says the claim's body of any one value",
        ),
        // A record states what it says; one with nothing to say is a
        // record of nothing.
        case(
            "a theorem record with no then line",
            vec![
                edit("corpus/stdlib/sums.records", Some("  then        Σ(k = 0 to n) t(k) ∈ ℤ\n  metamath    fsumzcl".to_string()), "  metamath    fsumzcl".to_string()),
            ],
            "sum-integer has no `then` line",
        ),
        case(
            "a method declaring a part that is no part marker",
            vec![
                edit("corpus/db/methods.records", Some("  parts       base, step\n".to_string()), "  parts       basis, step\n".to_string()),
            ],
            "method induction declares part",
        ),
        // A notation record says what it writes, what each hole takes, and
        // what its target makes of the holes.
        case(
            "a notation with no pattern",
            vec![
                edit("corpus/db/notation.records", Some("notation sum\n  pattern     Σ(_ = _ to _) _\n".to_string()), "notation sum\n".to_string()),
            ],
            "notation sum declares no pattern",
        ),
        case(
            "a notation whose sort does not read",
            vec![
                edit("corpus/db/notation.records", Some("  sort        number, number, number, number → number\n  level       summation".to_string()), "  sort        number number\n  level       summation".to_string()),
            ],
            "notation sum: sort",
        ),
        case(
            "a notation target naming a hole it does not have",
            vec![
                edit("corpus/db/notation.records", Some("  target      _2 _3 cfz co _4 _1 csu".to_string()), "  target      _2 _3 cfz co _5 _1 csu".to_string()),
            ],
            "notation sum target",
        ),
        case(
            "a notation that can nest in itself with no assoc",
            vec![
                edit("corpus/db/notation.records", Some("  assoc       left\n  identity    0 on either side, 0 on the right".to_string()), "  identity    0 on either side, 0 on the right".to_string()),
            ],
            "notation additive has a hole at each edge",
        ),
        case(
            "a notation with an assoc it does not need",
            vec![
                edit("corpus/db/notation.records", Some("  level       summation\n".to_string()), "  level       summation\n  assoc       left\n".to_string()),
            ],
            "notation indexed-union declares an assoc it does not need",
        ),
        // arithmetic works out + − · / and powers of numerals, and another
        // operation only where its record says so: mod's does.
        case(
            "arithmetic working out an operation its record does not give it",
            vec![
                edit("corpus/db/notation.records", Some("  reads       the remainder on dividing by\n  decided     arithmetic\n".to_string()), "  reads       the remainder on dividing by\n".to_string()),
                edit("proofs/sum-formula.proof", Some("          algebra\n".to_string()), "          algebra\n          requires 7 mod 3 = 1: arithmetic\n".to_string()),
            ],
            "7 mod 3 = 1 works out",
        ),
        case(
            "a step that is impossible and not the last of its block",
            vec![
                edit("proofs/reals-uncountable.proof", Some("    2.3.  10 divides 1, which is impossible\n          substitute (t + 1) − t = 1 (line 2.2) into line 2.1\n".to_string()), "    2.3.  10 divides 1, which is impossible\n          substitute (t + 1) − t = 1 (line 2.2) into line 2.1\n\n    2.4.  10 divides 1\n          substitute (t + 1) − t = 1 (line 2.2) into line 2.1\n".to_string()),
            ],
            "step 2.3 says it is impossible, which only the last step",
        ),
        case(
            "contradicting a line that is not in scope",
            vec![
                edit("proofs/bezout.proof", Some("inequalities, from 1, contradicting 3.4".to_string()), "inequalities, from 1, contradicting 3.9".to_string()),
            ],
            "contradicts 3.9, which is no line in scope",
        ),
        case(
            "a direction that does not assume a side of the claim",
            vec![
                edit("proofs/pythagorean-triples.proof", Some("    assume a² + b² = c²                                               (D1)".to_string()), "    assume a² + b² = c² + 1                                           (D1)".to_string()),
            ],
            "step 1 proves both directions, and direction 1 does not assume the claim's side it starts from",
        ),
        case(
            "a chain link saying a modulus after a relation that is not ≡",
            vec![
                edit("proofs/divisibility-by-three.proof", Some("                 ≡ 1 (mod 3)      arithmetic".to_string()), "                 = 1 (mod 3)      arithmetic".to_string()),
            ],
            "says (mod 3) after a relation that is not ≡",
        ),
        case(
            "algebra giving a claim of numerals alone",
            vec![
                edit("proofs/sum-formula.proof", Some("    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra".to_string()), "    1.6.  2 + 2 = 4\n          algebra".to_string()),
            ],
            "step 1.6 gives algebra for 2 + 2 = 4, which has no letter in it",
        ),
        // A step citing a define is the define at its values: one equation,
        // or that its name is a function on a set.
        case(
            "a step citing a define for another function on a set",
            vec![
                edit("proofs/binomial.proof", Some("    10.1. t(k) = C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()), "    10.1. p is a function on {0, …, m}\n          D1, from J".to_string()),
            ],
            "and claims that something other than t is a function on a set",
        ),
        case(
            "a step citing a define for no equation",
            vec![
                edit("proofs/binomial.proof", Some("    10.1. t(k) = C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()), "    10.1. t(k) ≠ C(m, k)·x^(m − k)·y^k\n          D1, from J".to_string()),
            ],
            "step 10.1 cites D1 and claims no one equation",
        ),
        // The steps are numbered as a reader counts them.
        case(
            "a step number written twice",
            vec![
                edit("proofs/sum-formula.proof", Some("    1.4.  S(k + 1) = S(k) + (k + 1)".to_string()), "    1.3.  S(k + 1) = S(k) + (k + 1)".to_string()),
            ],
            "step 1.3 is numbered twice",
        ),
        // A method that opens a block has one, with the parts its record
        // declares, each opening as the record says.
        case(
            "a method that needs a block with none",
            vec![
                edit("proofs/sum-formula.proof", Some("2.  S(n) = n(n + 1)/2\n    instantiate k := n in line 1".to_string()), "2.  S(n) = n(n + 1)/2\n    contradiction".to_string()),
            ],
            "step 2 is justified by contradiction, which needs a block, and has no sub-steps",
        ),
        case(
            "an induction block with no part markers",
            vec![
                edit("proofs/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    1.1.".to_string()),
                edit("proofs/sum-formula.proof", Some("\n    step\n    let k ∈ ℕ".to_string()), "\n    let k ∈ ℕ".to_string()),
            ],
            "step 1 cites induction, whose block carries the parts",
        ),
        case(
            "a part marker in a block that has no parts",
            vec![
                edit("proofs/sqrt2-irrational.proof", Some("    3.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()), "    base\n    3.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()),
            ],
            "under a contradiction block, which declares no parts",
        ),
        case(
            "a proof block that opens with neither let nor assume",
            vec![
                edit("proofs/reals-uncountable.proof", Some("    let k ∈ ℕ₀                                                        (K1)\n".to_string()), String::new()),
            ],
            "is a proof whose block does not open with `let` or `assume`",
        ),
        case(
            "a case that does not open with an assumption",
            vec![
                edit("proofs/triangle-inequality.proof", Some("    case\n    assume x ≥ 0                                                      (C1)\n".to_string()), "    case\n".to_string()),
            ],
            "part of step 2 does not open with a labelled `assume`",
        ),
        case(
            "an induction's base that opens with a let",
            vec![
                edit("proofs/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    base\n    let j ∈ ℕ                                                         (J)\n\n    1.1.".to_string()),
            ],
            "the base part of step 1 opens with a",
        ),
        // A calculation joins lines; the reasoning is in the lines it cites.
        case(
            "a calculation with no chain",
            vec![
                edit("proofs/sum-formula.proof", Some("    calculation\n      Σ(k = 1 to n) k = S(n)              D1\n                      = n(n + 1)/2        2".to_string()), "    calculation".to_string()),
            ],
            "step 3 is a calculation with no chain",
        ),
        case(
            "a chain line that cites an item",
            vec![
                edit("proofs/sum-formula.proof", Some("                 = 1                     1.1".to_string()), "                 = 1                     mun:sum-single a := 1".to_string()),
            ],
            "a chain line carries a justification",
        ),
        case(
            "a chain line with no relation",
            vec![
                edit("proofs/sum-formula.proof", Some("                 = 1                     1.1".to_string()), "                 1                       1.1".to_string()),
            ],
            "chain line carries no relation",
        ),
        case(
            "a chain line citing two lines",
            vec![
                edit("proofs/sum-formula.proof", Some("                 = 1                     1.1".to_string()), "                 = 1                     D1, 1.1".to_string()),
            ],
            "a calculation line cites one line or label, and this one cites D1, 1.1",
        ),
        case(
            "a line number after into without the word line",
            vec![
                edit("proofs/bezout.proof", Some("(line 2) into line 3.1".to_string()), "(line 2) into 3.1".to_string()),
            ],
            "a line number after `into` carries the word \"line\": `into line 3.1`",
        ),
        case(
            "a chain that turns round",
            vec![
                edit("tests/elaborator/a-chain-going-down.proof", Some("        > c       H5".to_string()), "        < c       H5".to_string()),
            ],
            "a chain goes one way, and this line says < after one saying ≥",
        ),
        case(
            "an identity element dropped from the middle with nothing saying what is left is a number",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("    requires C(m, k) ∈ ℕ₀: mun:binomial-nat0 n := m\n".to_string()), String::new()),
            ],
            "step 2 drops an identity element from what the substitution makes, and nothing says C(m, k) is a number",
        ),
        case(
            "two memberships claimed by one membership step",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("1.  Σ(k = 1 to n) (k + 1) ∈ ℝ\n".to_string()), "1.  Σ(k = 1 to n) (k + 1) ∈ ℝ. n + 1 ∈ ℝ.\n".to_string()),
            ],
            "step 1 claims 2 sentences by membership, which says one term is in a number system; each is a step of its own",
        ),
        case(
            "a substitute's source label written with the word line",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("substitute K = a/2 (D1) into H4".to_string()), "substitute K = a/2 (line D1) into H4".to_string()),
            ],
            "a label never carries the word \"line\": `(D1)`",
        ),
        case(
            "a requires line under a naming let",
            vec![
                edit("tests/elaborator/textbook-exercise-shapes.proof", Some("    reads half of a\n".to_string()), "    reads half of a\n    requires a ∈ ℝ: from H1\n".to_string()),
            ],
            "requires line under let D1, which carries none",
        ),
        case(
            "a proof block letting a letter other than the claim's",
            vec![
                edit("tests/elaborator/a-for-all-relating-two-sets.proof", Some("    let u ∈ A ".to_string()), "    let v ∈ A ".to_string()),
                edit("tests/elaborator/a-for-all-relating-two-sets.proof", Some("    1.1.  u ∈ B ∪ A".to_string()), "    1.1.  v ∈ B ∪ A".to_string()),
            ],
            "the block of step 1 lets v, and the claim it proves is about every u; the block opens with the claim's own letter",
        ),
        case(
            "an obtain naming no item, its line number without the word line",
            vec![
                edit("proofs/konigsberg.proof", Some("obtain i from line 6.3".to_string()), "obtain i from 6.3".to_string()),
            ],
            "an obtain naming no item takes its line with the word \"line\": `from line 6.3`",
        ),
        case(
            "the word line before a label",
            vec![
                edit("proofs/fundamental-calculus.proof", Some("instantiate x := c in H7, from 3".to_string()), "instantiate x := c in line H7, from 3".to_string()),
            ],
            "a label never carries the word \"line\": `in H7`",
        ),
        case(
            "a method no record declares",
            vec![
                edit("corpus/db/methods.records", Some("method join\n".to_string()), "method joins\n".to_string()),
            ],
            "join is in no record of corpus/db/methods.records",
        ),
        case(
            "a requires line whose reason is neither a method, an item, nor a line",
            vec![
                edit("proofs/sum-formula.proof", Some("          requires k ≥ 1: from K".to_string()), "          requires k ≥ 1: because K".to_string()),
            ],
            "which is neither a method, an item, nor a line",
        ),
        case(
            "a theorem with no steps",
            vec![edit("proofs/empty.proof", None, "theorem empty\n  then 1 = 1\n".to_string())],
            "theorem empty has no steps",
        ),
        // A last step that proves one sentence of a conclusion of two is
        // correct as far as it goes, and every other check passes it.
        case(
            "a last step claiming less than the conclusion",
            vec![edit(
                "proofs/short.proof",
                None,
                "theorem short\n  then 1 + 1 = 2. 2 + 2 = 4.\n\n1.  1 + 1 = 2\n    arithmetic\n"
                    .to_string(),
            )],
            "step 1 is the last, and does not claim what short states",
        ),
        // The item's `let f : D → E` asks for nothing a line writes, and D
        // is the set the citing proof gives v; 5 ∈ ℕ is no reason 5 is in it.
        case(
            "a function applied outside its domain",
            vec![edit(
                "proofs/outside.proof",
                None,
                "import mundane theorem    stdlib/functions/function-value\n\ntheorem outside\n  let v : {0, …, 1} → ℝ                                               (H1)\n  then v(5) ∈ ℝ\n\n1.  v(5) ∈ ℝ\n    mun:function-value f := v, x := 5\n"
                    .to_string(),
            )],
            "step 1 cites mun:function-value, which asks for 5 ∈ {0, …, 1}",
        ),
        // A label outside a file's theorems is one label for every theorem
        // below it, and a define says what its name means.
        case(
            "a label given twice outside the theorems",
            vec![
                edit("proofs/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), "       reads the geometric series: the powers of a, from a^0 up to a^n\n\ndefine H(n) := n + 1, for n ∈ ℕ                                    (D1)\n       reads one more than n\n".to_string()),
            ],
            "label D1 is already used at line 7",
        ),
        case(
            "a define with no reads line",
            vec![
                edit("proofs/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), String::new()),
            ],
            "carries no `reads` line",
        ),
    ]
}
