//! The elaborator reports things rather than assuming them.
//!
//! The checker reads the text; the elaborator builds a proof from it, and
//! where it cannot it may take the step as stated instead — the right answer
//! for a method it does not expand, and the wrong one for a defect somebody
//! has to fix. Each case takes the corpus, makes one edit, and requires that
//! elaborating one theorem fails with a message naming where. A case that
//! elaborates cleanly is the failure this is looking for: the defect was
//! swallowed.
//!
//! The corpus is read into memory once and each case edits it through an
//! overlay of its own. set.mm is read once for all of them. A theorem must
//! elaborate before the edit, or its case tests nothing, and that is asked
//! once per theorem.
//!
//! A defect the checker reports never reaches the elaborator: the build
//! refuses what the checker refuses, with the checker's own problem, and
//! those cases are in `planted_check.rs`. What is here is what only the
//! build can see.

use std::path::Path;

use indexmap::IndexMap;
use parley::elab::elaborate::Options;
use parley::elab::Library;
use parley::source::{Disk, Memory, Overlay, Source};
use parley::tools::build::{elaborate_one, library};

struct Case {
    name: &'static str,
    theorem: &'static str,
    file: &'static str,
    old: &'static str,
    new: &'static str,
    expect: &'static str,
    /// Where the message points, named by the text of that line rather than
    /// its number, so that a line added above it moves the case with it.
    at: Option<At>,
}

/// A line of a file, by text the line holds and no other line of the file
/// does, read after the case's edit.
struct At {
    file: &'static str,
    holding: &'static str,
}

impl Case {
    /// The case, its message pointing at the line of `file` holding
    /// `holding`.
    fn at(self, file: &'static str, holding: &'static str) -> Case {
        Case {
            at: Some(At { file, holding }),
            ..self
        }
    }

    /// What the message must contain: `path:line  message` where the case
    /// names a line, its message alone where it does not; or why the line
    /// it names cannot be found.
    fn wanted(&self, tree: &dyn Source) -> Result<String, String> {
        let Some(at) = &self.at else {
            return Ok(self.expect.to_string());
        };
        let text = tree
            .read_text(at.file)
            .map_err(|e| format!("{} does not read: {e}", at.file))?;
        let holding: Vec<usize> = text
            .lines()
            .enumerate()
            .filter(|(_, line)| line.contains(at.holding))
            .map(|(i, _)| i + 1)
            .collect();
        match holding.as_slice() {
            [line] => Ok(format!("{}:{line}  {}", at.file, self.expect)),
            _ => Err(format!(
                "{} lines of {} hold {:?}, where one must",
                holding.len(),
                at.file,
                at.holding
            )),
        }
    }
}

fn case(
    name: &'static str,
    theorem: &'static str,
    file: &'static str,
    old: &'static str,
    new: &'static str,
    expect: &'static str,
) -> Case {
    Case {
        name,
        theorem,
        file,
        old,
        new,
        expect,
        at: None,
    }
}

/// The corpus as it stands, with the files already elaborated, which a
/// theorem citing another reads for the order of what it pushes.
fn clean() -> Memory {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap()
}

/// What elaborating says, or None where it says nothing and builds.
fn run(tree: &dyn Source, theorem: &str, library: &Library) -> Option<String> {
    match elaborate_one(tree, theorem, library, Options::default()) {
        Ok(_) => None,
        Err(problem) => Some(problem.to_string()),
    }
}

#[test]
fn the_elaborator_reports_every_planted_defect() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let library = library(root, None).expect(
        "set.mm is found: say where it is with SET_MM, or leave a copy at the root",
    );
    let clean = clean();
    let planted = cases();
    let mut healthy: IndexMap<&str, Option<String>> = IndexMap::new();
    let mut said = Vec::new();
    let mut missed = 0;
    for case in &planted {
        let before = healthy
            .entry(case.theorem)
            .or_insert_with(|| run(&clean, case.theorem, &library));
        if let Some(why) = before {
            said.push(format!(
                "  SETUP FAILED  {}\n      {} does not elaborate before the edit: {why}",
                case.name, case.theorem
            ));
            missed += 1;
            continue;
        }
        let mut tree = Overlay::new(&clean);
        let text = tree.read_text(case.file).unwrap();
        if !text.contains(case.old) {
            said.push(format!(
                "  SETUP FAILED  {}\n      anchor not found in {}",
                case.name, case.file
            ));
            missed += 1;
            continue;
        }
        let edited = text.replacen(case.old, case.new, 1);
        tree.write(case.file, edited.into_bytes());
        let wanted = match case.wanted(&tree) {
            Ok(wanted) => wanted,
            Err(why) => {
                said.push(format!("  SETUP FAILED  {}\n      {why}", case.name));
                missed += 1;
                continue;
            }
        };
        match run(&tree, case.theorem, &library) {
            None => {
                said.push(format!(
                    "  NOT CAUGHT    {}\n      it elaborated: the defect was taken as stated",
                    case.name
                ));
                missed += 1;
            }
            Some(got) if got.contains(&wanted) => {
                said.push(format!("  caught        {}", case.name));
            }
            Some(got) => {
                let got: String = got.chars().take(160).collect();
                said.push(format!(
                    "  NOT CAUGHT    {}\n      expected {wanted:?}\n      got      {got:?}",
                    case.name
                ));
                missed += 1;
            }
        }
    }
    println!("{}", said.join("\n"));
    println!(
        "\n{} caught, {missed} missed, of {} planted defects",
        planted.len() - missed,
        planted.len()
    );
    assert_eq!(missed, 0, "{}", said.join("\n"));
}

fn cases() -> Vec<Case> {
    vec![
        // A gap in the database rather than in the text, reported at the line
        // that wrote the notation.
        case(
            "take away a target the corpus writes",
            "proofs/wiedijk/cantor/cantor",
            "corpus/db/notation.records",
            "  target      _1 cpw",
            "  metamath    cpw-without-a-target",
            "notation 'powerset' has no target field",
        ),
        // A database defect rather than a text one, and on an item rather than
        // a notation: the target names a lemma that proves the other `then`
        // group, so the step's own group has nothing behind it. The checker
        // reads no set.mm, so the page it accepts is a gap in the build.
        case(
            "name the wrong clause in a definition target",
            "proofs/wiedijk/triangle-inequality/abs-bounds",
            "corpus/stdlib/numbers.records",
            "  target      absid, absnid\n",
            "  target      absid, absid\n",
            "the build cannot yet prove this, which the checker accepts: no clause of mun:abs gives what step 2.6 claims",
        )
        .at("proofs/wiedijk/triangle-inequality.proof", "2.6.  |x| = −x"),
        // Each part of what the claim asks of the witness is one of the
        // target's lemmas, and a part none of them reaches is the target
        // failing, not something to take as stated.
        case(
            "leave out the lemma saying the supremum is least",
            "proofs/wiedijk/intermediate-value/intermediate-value",
            "corpus/stdlib/calculus.records",
            "  target      suprcl, suprub, suprleub with c := sup S",
            "  target      suprcl, suprub with c := sup S",
            "axi:stdlib/calculus/completeness targets suprcl, suprub, and none of them reaches what step 8 obtains",
        ),
        // A target is where the claim lands, and a variable bound to the wrong
        // name makes it land somewhere else. That is reported, not assumed.
        case(
            "bind a target variable to the wrong name",
            "proofs/wiedijk/subsets/subsets-count",
            "corpus/stdlib/counting.records",
            "  target      hashdifsnp1 with V := X, N := a, Y := k",
            "  target      hashdifsnp1 with V := X, N := a, Y := X",
            "no clause of mun:card-remove reaches what step 1.2.2 claims",
        ),
        // A definition read with no pair for its subject is about the proof's
        // letter of the same name (`SYNTAX.md`). odd-square has an n, so
        // `mun:odd` with no pair is read of n, whose witness no line names;
        // the claim is that n² is odd.
        case(
            "leave out the value a definition is concluded of",
            "proofs/wiedijk/sqrt2-irrational/odd-square",
            "proofs/wiedijk/sqrt2-irrational.proof",
            "    mun:odd n := n², from 5",
            "    mun:odd, from 5",
            "with 2 · j + 1 = n",
        ),
        // A target naming a lemma the library as built does not hold, as
        // one added to corpus/proved/ before a whole build has written it,
        // is said where the item is cited, and the build goes on.
        case(
            "a target naming a lemma the library does not hold",
            "tests/stdlib/sums/sum-empty-range",
            "corpus/stdlib/sums.records",
            "  target      gfsum0\n",
            "  target      gfsumnone\n",
            "mun:stdlib/sums/sum-empty-range targets gfsumnone, which neither set.mm nor proved.mm as built holds",
        ),
    ]
}
