//! A decision method answers as its oracle does.
//!
//! `arithmetic` decides a claim from its form, and every proof leans on it
//! (`METHODS.md`). Coverage says whether its code ran; this asks whether its
//! answers are right. Claims are drawn at random from the forms the document
//! says it takes (`oracle/gen.rs`), each is worked out by an oracle of the
//! test's own that shares none of the method's code (`oracle/judge.rs`), and
//! each is written as a theorem of one step and asked of the tools:
//!
//! - a claim the oracle says holds is accepted by the checker, built with
//!   nothing assumed, and verified;
//! - a claim it says fails is refused as false;
//! - a claim the document says the method refuses is refused in those words.
//!
//! Any other answer is a fault, printed with the seed that draws it again,
//! and each class found is pinned as a theorem the build elaborates
//! (`tests/elaborator/closed-values.proof`). The test draws `ORACLE_COUNT`
//! claims (1500 where it is not set) from `ORACLE_SEED`, and reads set.mm,
//! so it is not run with the others:
//!
//! ```text
//! cargo test --release --test oracle -- --ignored --nocapture
//! ```

use std::collections::BTreeSet;
use std::path::Path;
use std::sync::Arc;

use parley::corpus::corpus;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::formula::grammar::Grammar;
use parley::mm::where_set_mm;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::threads::in_order;
use parley::tools::build::{library, Libraries, Loaded};
use parley::tools::{path_of, verify};

#[path = "shared/mod.rs"]
mod shared;

#[path = "oracle/gen.rs"]
mod gen;

#[path = "oracle/judge.rs"]
mod judge;

use judge::Verdict;
use shared::{included, Random};

/// The seed claims are drawn from where `ORACLE_SEED` does not say another.
const SEED: u64 = 20_261_012;

/// How many claims are drawn where `ORACLE_COUNT` does not say.
const COUNT: usize = 1500;

/// Where the claims are written, as a proof file of the tree.
const FILE: &str = "tests/oracle/arithmetic.proof";

/// The words `arithmetic` decides, imported as a proof saying them would.
const IMPORTS: &str = "\
import mundane definition stdlib/divisibility/divides
import mundane definition stdlib/divisibility/even
import mundane definition stdlib/divisibility/odd
import mundane definition stdlib/divisibility/congruent-mod

";

/// One claim drawn: what it says, and what the oracle makes of it.
struct Asked {
    theorem: String,
    claim: gen::Claim,
    written: String,
    verdict: Verdict,
    /// The line its theorem starts on, and the line after its last.
    lines: (usize, usize),
}

/// What the tools made of a claim.
enum Answer {
    /// The checker reported it.
    Checker(String),
    /// The elaborator refused it, or panicked.
    Refused(String),
    /// Built, with something assumed rather than proved.
    Assumed(String),
    /// Built and verified, or not verified, as the verifier says.
    Built { verified: bool, said: String },
}

fn env_number<T: std::str::FromStr>(name: &str) -> Option<T> {
    std::env::var(name).ok().map(|s| {
        s.parse::<T>()
            .unwrap_or_else(|_| panic!("{name} is a number"))
    })
}

#[test]
#[ignore = "elaborates and verifies hundreds of claims; run on its own"]
fn a_decision_method_answers_as_its_oracle() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let g = Grammar::load(&corpus(&clean).expect("the corpus reads").records)
        .expect("the grammar loads");
    let seed = env_number("ORACLE_SEED").unwrap_or(SEED);
    let count = env_number("ORACLE_COUNT").unwrap_or(COUNT);

    // Each claim a theorem of its own, so that one refused stops no other.
    let mut random = Random::new(seed);
    let mut text = IMPORTS.to_string();
    let mut asked = Vec::new();
    for i in 0..count {
        let claim = gen::claim(&mut random);
        let written = gen::written(&g, &claim);
        let theorem = format!("arithmetic-{i}");
        let start = text.lines().count() + 1;
        text.push_str(&format!(
            "theorem {theorem}\n  then {written}\n\n1.  {written}\n    arithmetic\n\n"
        ));
        asked.push(Asked {
            theorem,
            verdict: judge::arithmetic(&claim),
            claim,
            written,
            lines: (start, text.lines().count() + 1),
        });
    }
    let mut tree = Overlay::new(&clean);
    tree.write(FILE, text.into_bytes());
    let tree = Memory::copy(&tree, &["corpus", "proofs", "tests"]).unwrap();

    // What the checker says of each, by the lines of its theorem.
    let checked = parley::check::run(&tree).printed;
    let reported = |a: &Asked| -> Vec<String> {
        checked
            .lines()
            .filter_map(|l| {
                let at = l.strip_prefix(FILE)?.strip_prefix(':')?;
                let n: usize = at.split_whitespace().next()?.parse().ok()?;
                (a.lines.0..a.lines.1).contains(&n).then(|| l.to_string())
            })
            .collect()
    };

    // Each built, against set.mm read once.
    let module = FILE.trim_end_matches(".proof");
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let built = in_order(
        &asked,
        || (Library::new(Arc::clone(&read)), None::<Loaded>),
        |(lib, loaded): &mut (Library, Option<Loaded>), a| {
            let qualified = format!("{module}/{}", a.theorem);
            let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let loaded = loaded.get_or_insert_with(|| {
                    Loaded::new(&tree).expect("the tree with the claims reads")
                });
                loaded
                    .elaborate(&qualified, lib, Options::default())
                    .map(|e| e.text)
                    .map_err(|p| p.to_string())
            }));
            run.unwrap_or_else(|panic| {
                // What the library held when it stopped is not to be trusted.
                *lib = Library::new(Arc::clone(&read));
                let said = panic
                    .downcast_ref::<String>()
                    .cloned()
                    .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
                    .unwrap_or_default();
                Err(format!("panicked: {said}"))
            })
        },
    );

    // What was built, verified together as the gate verifies a tree. An
    // answer not yet given is a file built and waiting for the verifier.
    let mut answers: Vec<Option<Answer>> = Vec::new();
    let mut verifying = Overlay::new(&tree);
    let mut files: BTreeSet<String> = BTreeSet::new();
    for (a, result) in asked.iter().zip(&built) {
        let checker = reported(a);
        let answer = match result {
            _ if !checker.is_empty() => Some(Answer::Checker(checker.join(" | "))),
            Err(said) => Some(Answer::Refused(said.clone())),
            Ok(text) => {
                let assumed: Vec<&str> = text
                    .lines()
                    .filter(|l| l.split_whitespace().nth(1) == Some("$a"))
                    .collect();
                if assumed.is_empty() {
                    let path = path_of(&format!("{module}/{}", a.theorem));
                    verifying.write(&path, text.clone().into_bytes());
                    files.insert(path);
                    None
                } else {
                    Some(Answer::Assumed(assumed.join(" | ")))
                }
            }
        };
        answers.push(answer);
    }
    let libraries = Libraries::read(
        &where_set_mm(None, root)
            .expect("set.mm is found: say where it is with SET_MM"),
    )
    .expect("set.mm reads");
    let mut every: BTreeSet<String> = BTreeSet::new();
    for path in &files {
        let text = verifying.read_text(path).expect("a built file reads");
        every.extend(included(&verifying, path, &text));
    }
    let every: Vec<String> = every.into_iter().collect();
    let said = verify::run(&verifying, &every, Some(&libraries));
    let printed = said.printed.trim().replace('\n', " | ");
    for answer in answers.iter_mut() {
        if answer.is_none() {
            *answer = Some(Answer::Built {
                verified: said.green(),
                said: printed.clone(),
            });
        }
    }

    // Each answer against its verdict.
    let mut faults = Vec::new();
    let mut tally = [0usize; 3];
    for (a, answer) in asked.iter().zip(answers) {
        let answer = answer.expect("every claim answered");
        let right = match (&a.verdict, &answer) {
            (Verdict::Holds(true), Answer::Built { verified, .. }) => *verified,
            (Verdict::Holds(false), Answer::Refused(said)) => {
                said.contains("which is false")
            }
            (Verdict::Refused(any), Answer::Refused(said)) => {
                any.iter().any(|why| said.contains(why))
            }
            _ => false,
        };
        tally[match a.verdict {
            Verdict::Holds(true) => 0,
            Verdict::Holds(false) => 1,
            Verdict::Refused(_) => 2,
        }] += 1;
        if !right {
            let got = match answer {
                Answer::Checker(s) => format!("the checker said: {s}"),
                Answer::Refused(s) => format!("refused: {s}"),
                Answer::Assumed(s) => format!("built assuming: {s}"),
                Answer::Built { verified: true, .. } => {
                    "built and verified".to_string()
                }
                Answer::Built { said, .. } => {
                    format!("built, and the verifier said: {said}")
                }
            };
            faults.push(format!(
                "{} ({}): {}\n    drawn:  {:?}\n    oracle: {:?}\n    tools:  {got}",
                a.theorem, seed, a.written, a.claim, a.verdict
            ));
        }
    }
    println!(
        "{count} claims from seed {seed}: {} true, {} false, {} refused by the document; {} faults",
        tally[0],
        tally[1],
        tally[2],
        faults.len()
    );
    assert!(faults.is_empty(), "{}", faults.join("\n"));
}
