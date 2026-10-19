//! A decision method answers as its oracle does.
//!
//! `arithmetic`, `algebra`, `inequalities`, `membership` and `inspection`
//! decide a claim from its form, and every proof leans on them
//! (`METHODS.md`), as it leans on the rule that a membership is said once
//! (`SYNTAX.md`). Coverage says whether their code ran; this asks whether
//! their answers are right. Claims are drawn at random from the forms the
//! document says each takes, each is worked out by an oracle of the test's
//! own that shares none of the method's code (`oracle/judge.rs` for
//! `arithmetic`, `algebra.rs`, `order.rs`, `member.rs`, `inspect.rs` and
//! `said.rs` for the others, and `rows.rs` for an inequalities step's rows,
//! `transitivity` and `antisymmetry`), and each is written as a theorem of
//! one step and asked of the tools:
//!
//! - a claim the oracle says holds is accepted by the checker, built with
//!   nothing assumed, and verified;
//! - a claim it says fails is refused as false;
//! - a claim the document says the method refuses is refused in those words.
//!
//! The checker decides what the build would refuse, in the same words, so
//! a refusal is either tool's.
//!
//! Any other answer is a fault, printed with the seed that draws it again,
//! and each class found is pinned as a theorem the build elaborates
//! (in `tests/elaborator/`: `closed-values`, `combinations`, `powers`,
//! `divisors`, `orders`, `rationals`, `listed-numerals` and
//! `signed-divisibility`). The test draws `ORACLE_COUNT`
//! claims of each method (1500 where it is not set) from `ORACLE_SEED`, of
//! the methods whose names hold `ORACLE_ONLY` where it is set, and reads
//! set.mm, so it is not run with the others:
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
use parley::threads::{in_order, in_order_on};
use parley::tools::build::{library, Libraries, Loaded};
use parley::tools::{path_of, verify};

#[path = "shared/mod.rs"]
mod shared;

#[path = "oracle/gen.rs"]
mod gen;

#[path = "oracle/judge.rs"]
mod judge;

#[path = "oracle/algebra.rs"]
mod algebra;

#[path = "oracle/order.rs"]
mod order;

#[path = "oracle/member.rs"]
mod member;

#[path = "oracle/inspect.rs"]
mod inspect;

#[path = "oracle/said.rs"]
mod said;

#[path = "oracle/rows.rs"]
mod rows;

#[path = "oracle/real.rs"]
mod real;

use gen::Drawn;
use judge::Verdict;
use shared::{included, Random};

/// The seed claims are drawn from where `ORACLE_SEED` does not say another.
const SEED: u64 = 20_261_012;

/// How many claims of each method are drawn where `ORACLE_COUNT` does not
/// say.
const COUNT: usize = 1500;

/// How many built files are verified at once where they are verified one
/// by one.
const VERIFYING: usize = 4;

/// A method held to its oracle: how its claims are drawn, what a proof
/// asking it imports, and the words it refuses a false claim in.
struct Method {
    name: &'static str,
    draw: fn(&mut Random, &Grammar) -> Drawn,
    imports: &'static str,
    false_said: &'static str,
}

fn methods() -> Vec<Method> {
    vec![
        Method {
            name: "arithmetic",
            draw: gen::arithmetic,
            // The words `arithmetic` decides, imported as a proof saying
            // them would.
            imports: "\
import mundane definition stdlib/divisibility/divides
import mundane definition stdlib/divisibility/even
import mundane definition stdlib/divisibility/odd
import mundane definition stdlib/divisibility/congruent-mod
",
            false_said: "which is false",
        },
        Method {
            name: "algebra",
            draw: algebra::claim,
            imports: "",
            false_said: "is not an identity",
        },
        Method {
            name: "algebra-from",
            draw: algebra::derived,
            imports: "",
            false_said: "nor does it follow from what step 1 cites",
        },
        Method {
            name: "algebra-divided",
            draw: algebra::divided,
            imports: "",
            // Said of a claim with nothing cited, and of one that does not
            // follow from what it cites as well.
            false_said: "is not an identity",
        },
        Method {
            name: "inequalities",
            draw: order::claim,
            imports: "",
            false_said: "does not follow from what step 1 cites",
        },
        Method {
            name: "membership",
            draw: member::claim,
            imports: "",
            false_said: "is not built from what step 1 cites",
        },
        Method {
            name: "inspection",
            draw: inspect::claim,
            imports: "",
            // Its false claims are drawn as refusals in either of its words
            // (`inspect.rs`).
            false_said: "is not seen by inspection of what it cites",
        },
        Method {
            name: "said-once",
            draw: said::claim,
            imports: "",
            // Every claim drawn holds, as an identity; what it lacks is
            // drawn as a refusal (`said.rs`).
            false_said: "is not an identity",
        },
        // What these draw false is drawn as a refusal (`rows.rs`).
        Method {
            name: "rows",
            draw: rows::rows,
            imports: "",
            false_said: "is not the row above",
        },
        Method {
            name: "transitivity",
            draw: rows::transitivity,
            imports: "",
            false_said: "and the chain it cites gives",
        },
        Method {
            name: "antisymmetry",
            draw: rows::antisymmetry,
            imports: "",
            false_said: "by antisymmetry what is not two lines",
        },
        Method {
            name: "real-arithmetic",
            draw: real::claim,
            imports: "",
            false_said: "which is false",
        },
    ]
}

/// One claim drawn, where it is written, and what the oracle makes of it.
struct Asked {
    method: usize,
    file: String,
    theorem: String,
    drawn: Drawn,
    /// The line its theorem starts on, and the line after its last.
    lines: (usize, usize),
}

impl Asked {
    fn qualified(&self) -> String {
        format!("{}/{}", self.file.trim_end_matches(".proof"), self.theorem)
    }
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

/// A theorem of one step: its header, its claim, and the step claiming it.
fn theorem(name: &str, d: &Drawn) -> String {
    let mut out = format!("theorem {name}\n");
    for (i, line) in d.header.iter().enumerate() {
        out.push_str(&format!("  {line}    (H{})\n", i + 1));
    }
    out.push_str(&format!(
        "  then {}\n\n1.  {}\n    {}\n\n",
        d.written, d.written, d.justification
    ));
    out
}

#[test]
#[ignore = "elaborates and verifies thousands of claims; run on its own"]
fn a_decision_method_answers_as_its_oracle() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let clean = Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap();
    let g = Grammar::load(&corpus(&clean).expect("the corpus reads").records)
        .expect("the grammar loads");
    let seed = env_number("ORACLE_SEED").unwrap_or(SEED);
    let count = env_number("ORACLE_COUNT").unwrap_or(COUNT);
    let only = std::env::var("ORACLE_ONLY").ok();
    let methods: Vec<Method> = methods()
        .into_iter()
        .filter(|m| only.as_ref().is_none_or(|o| m.name.contains(o.as_str())))
        .collect();

    // Each claim a theorem of its own, so that one refused stops no other,
    // in a file for each method.
    let mut random = Random::new(seed);
    let mut asked = Vec::new();
    let mut tree = Overlay::new(&clean);
    for (m, method) in methods.iter().enumerate() {
        let file = format!("tests/oracle/{}.proof", method.name);
        let mut text = format!("{}\n", method.imports);
        for i in 0..count {
            let drawn = (method.draw)(&mut random, &g);
            let name = format!("{}-{i}", method.name);
            let start = text.lines().count() + 1;
            text.push_str(&theorem(&name, &drawn));
            asked.push(Asked {
                method: m,
                file: file.clone(),
                theorem: name,
                drawn,
                lines: (start, text.lines().count() + 1),
            });
        }
        tree.write(&file, text.into_bytes());
    }
    let tree = Memory::copy(&tree, &["corpus", "proofs", "tests"]).unwrap();

    // What the checker says of each, by the lines of its theorem.
    let checked = parley::checker::run(&tree).printed;
    let reported = |a: &Asked| -> Vec<String> {
        checked
            .lines()
            .filter_map(|l| {
                let at = l.strip_prefix(a.file.as_str())?.strip_prefix(':')?;
                let n: usize = at.split_whitespace().next()?.parse().ok()?;
                (a.lines.0..a.lines.1).contains(&n).then(|| l.to_string())
            })
            .collect()
    };

    // Each built, against set.mm read once.
    let read = library(root, None)
        .expect(
            "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
        )
        .shared();
    let built = in_order(
        &asked,
        || (Library::new(Arc::clone(&read)), None::<Loaded>),
        |(lib, loaded): &mut (Library, Option<Loaded>), a| {
            let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let loaded = loaded.get_or_insert_with(|| {
                    Loaded::new(&tree).expect("the tree with the claims reads")
                });
                loaded
                    .elaborate(&a.qualified(), lib, Options::default())
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

    // What was built, verified together as the gate verifies a tree, and
    // one by one where that is not green, to say which. An answer not yet
    // given is a file built and waiting for the verifier.
    let mut answers: Vec<Option<Answer>> = Vec::new();
    let mut verifying = Overlay::new(&tree);
    let mut files: Vec<(usize, String)> = Vec::new();
    for (i, (a, result)) in asked.iter().zip(&built).enumerate() {
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
                    let path = path_of(&a.qualified());
                    verifying.write(&path, text.clone().into_bytes());
                    files.push((i, path));
                    None
                } else {
                    Some(Answer::Assumed(assumed.join(" | ")))
                }
            }
        };
        answers.push(answer);
    }
    let verifying = Memory::copy(&verifying, &["corpus", "proofs", "tests"]).unwrap();
    let libraries = Libraries::read_verifying_often(
        &where_set_mm(None, root)
            .expect("set.mm is found: say where it is with SET_MM"),
    )
    .expect("set.mm reads");
    let closure = |path: &str| -> Vec<String> {
        let text = verifying.read_text(path).expect("a built file reads");
        included(&verifying, path, &text)
    };
    let mut every: BTreeSet<String> = BTreeSet::new();
    for (_, path) in &files {
        every.extend(closure(path));
    }
    let every: Vec<String> = every.into_iter().collect();
    let together = verify::run(&verifying, &every, Some(&libraries));
    let verdicts: Vec<(bool, String)> = if together.green() {
        files.iter().map(|_| (true, String::new())).collect()
    } else {
        in_order_on(
            VERIFYING,
            &files,
            || (),
            |_, (_, path)| {
                let said = verify::run(&verifying, &closure(path), Some(&libraries));
                (said.green(), said.printed.trim().replace('\n', " | "))
            },
        )
    };
    for ((i, _), (verified, said)) in files.iter().zip(verdicts) {
        answers[*i] = Some(Answer::Built { verified, said });
    }

    // Each answer against its verdict.
    let mut faults = Vec::new();
    let mut tally = vec![[0usize; 3]; methods.len()];
    for (a, answer) in asked.iter().zip(answers) {
        let answer = answer.expect("every claim answered");
        let method = &methods[a.method];
        // The checker decides what the build would refuse, and says it in
        // the same words, so either tool's refusal is an answer.
        let right = match (&a.drawn.verdict, &answer) {
            (Verdict::Holds(true), Answer::Built { verified, .. }) => *verified,
            (Verdict::Holds(false), Answer::Refused(said) | Answer::Checker(said)) => {
                said.contains(method.false_said)
            }
            (Verdict::Refused(any), Answer::Refused(said) | Answer::Checker(said)) => {
                any.iter().any(|why| said.contains(why))
            }
            _ => false,
        };
        tally[a.method][match a.drawn.verdict {
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
                "{} ({seed}): {}\n    drawn:  {}\n    oracle: {:?}\n    tools:  {got}",
                a.theorem, a.drawn.written, a.drawn.shown, a.drawn.verdict
            ));
        }
    }
    for (method, [t, f, r]) in methods.iter().zip(&tally) {
        println!(
            "{}: {count} claims from seed {seed}: {t} true, {f} false, {r} refused by the document",
            method.name
        );
    }
    println!("{} faults", faults.len());
    assert!(faults.is_empty(), "{}", faults.join("\n"));
}
