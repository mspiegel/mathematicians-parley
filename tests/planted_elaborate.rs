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
//! The nets run with the search offered every fact in scope, so that the rule
//! checked once a proof is built is all that stands between an uncited line
//! and the proof: the cases above always catch those sooner, through the
//! search finding nothing.

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
    /// An import line the edit needs, put at the head of the file: an edit
    /// citing an item the file does not import cites it by name.
    import: Option<&'static str>,
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
        import: None,
        old,
        new,
        expect,
        at: None,
    }
}

/// A case whose edit cites an item the file does not import, with the
/// import line that brings it in.
fn case_importing(
    name: &'static str,
    theorem: &'static str,
    file: &'static str,
    import: &'static str,
    old: &'static str,
    new: &'static str,
    expect: &'static str,
) -> Case {
    Case {
        import: Some(import),
        ..case(name, theorem, file, old, new, expect)
    }
}

/// The corpus as it stands, with the files already elaborated, which a
/// theorem citing another reads for the order of what it pushes.
fn clean() -> Memory {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    Memory::copy(&Disk::new(root), &["corpus", "proofs", "tests"]).unwrap()
}

/// What elaborating says, or None where it says nothing and builds.
fn run(
    tree: &dyn Source,
    theorem: &str,
    library: &Library,
    net: bool,
) -> Option<String> {
    let options = Options {
        whole_scope_offered: net,
        ..Options::default()
    };
    match elaborate_one(tree, theorem, library, options) {
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
    let mut planted: Vec<(Case, bool)> =
        cases().into_iter().map(|c| (c, false)).collect();
    planted.extend(nets().into_iter().map(|c| (c, true)));
    let mut healthy: IndexMap<(&str, bool), Option<String>> = IndexMap::new();
    let mut said = Vec::new();
    let mut missed = 0;
    for (case, net) in &planted {
        let before = healthy
            .entry((case.theorem, *net))
            .or_insert_with(|| run(&clean, case.theorem, &library, *net));
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
        let edited = match case.import {
            Some(line) => format!("{line}\n{edited}"),
            None => edited,
        };
        tree.write(case.file, edited.into_bytes());
        let wanted = match case.wanted(&tree) {
            Ok(wanted) => wanted,
            Err(why) => {
                said.push(format!("  SETUP FAILED  {}\n      {why}", case.name));
                missed += 1;
                continue;
            }
        };
        match run(&tree, case.theorem, &library, *net) {
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
        // Two equations each multiplied by a term is two steps: the proof
        // multiplies each law of sines in a step of its own and joins them by
        // a calculation, and one `algebra` step citing both is refused.
        case(
            "one algebra step multiplying two cited equations",
            "proofs/pythagoras/similar-triangles",
            "proofs/pythagoras.proof",
            "    calculation\n      |PQ|·|P′R′|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)       9\n                            = |P′Q′|·|PR|·sin(∠PQR)       10",
            "    algebra, from 5, 8\n    requires |PQ| ∈ ℝ: mun:distance-real P := P, Q := Q\n    requires |PR| ∈ ℝ: mun:distance-real P := P, Q := R\n    requires |P′Q′| ∈ ℝ: mun:distance-real P := P′, Q := Q′\n    requires |P′R′| ∈ ℝ: mun:distance-real P := P′, Q := R′\n    requires ∠PQR ∈ ℝ: mun:triangle-angle-real, from H7\n    requires sin(∠PQR) ∈ ℝ: mun:sin-real a := ∠PQR\n    requires ∠QRP ∈ ℝ: mun:triangle-angle-real, from H7\n    requires sin(∠QRP) ∈ ℝ: mun:sin-real a := ∠QRP",
            "at most one equation multiplied by a term",
        ),
        // A formula that does not lex is a defect with a position, and not a
        // route declining: taken for one, the step would be assumed and the
        // build would go green.
        case(
            "a requires line that does not lex",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "          requires a ∈ ℝ: from H1\n          requires 1 − a ≠ 0: algebra, from H2\n          requires k + 1 ∈ ℕ₀",
            "          requires a ¿ ℝ: from H1\n          requires 1 − a ≠ 0: algebra, from H2\n          requires k + 1 ∈ ℕ₀",
            "",
        )
        .at(
            "proofs/geometric-series.proof",
            "1.14. (1 − a^(k + 1))/(1 − a) + a^(k + 1)",
        ),
        // `substitute` walks its equation both ways and each sentence of the
        // line it names, trying the next where one declines. A name the proof
        // never introduced is not one of those: it is a defect.
        case(
            "substitute a name the proof never introduced",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "          substitute a^(0 + 1) = a (line 1.6)",
            "          substitute a^(0 + 1) = z (line 1.6)",
            "no kernel name for 'z'",
        ),
        // A gap in the database rather than in the text, reported at the line
        // that wrote the notation.
        case(
            "take away a target the corpus writes",
            "proofs/cantor/cantor",
            "corpus/db/notation.records",
            "  target      _1 cpw",
            "  metamath    cpw-without-a-target",
            "notation 'powerset' has no target field",
        ),
        // A database defect rather than a text one, and on an item rather than
        // a notation: the target names a lemma that proves the other `then`
        // group, so the step's own group has nothing behind it.
        case(
            "name the wrong clause in a definition target",
            "proofs/triangle-inequality/abs-bounds",
            "corpus/stdlib/numbers.records",
            "  target      absid, absnid\n",
            "  target      absid, absid\n",
            "no clause of mun:abs gives what step 2.5 claims",
        )
        .at("proofs/triangle-inequality.proof", "2.5.  |x| = −x"),
        // The same report reached from the other side: the target is right and
        // the step claims something the definition does not say. It is a
        // defect, and not a route declining, which anything above would be
        // free to take as stated.
        case(
            "claim of a definition what it does not say",
            "proofs/triangle-inequality/abs-bounds",
            "proofs/triangle-inequality.proof",
            "    2.5.  |x| = −x",
            "    2.5.  |x| = x",
            "no clause of mun:abs gives what step 2.5 claims",
        )
        .at("proofs/triangle-inequality.proof", "2.5.  |x| = x"),
        // A `requires` line has a claim and a reason, and the reason is what
        // proves it. Here H5 does not say `C ≠ A`, and no line above this one
        // does; taking it from the theorem's own hypothesis and turning it
        // with `necom` would verify, and leave the line the page named unused.
        case(
            "name a line that does not state the side condition",
            "proofs/isosceles/isosceles",
            "proofs/isosceles.proof",
            "    requires B, C, A form a triangle: mun:triangle-rotate P := A, Q := B, R := C, from H4\n    requires C ≠ A: mun:triangle\n",
            "    requires C ≠ A: mun:triangle, from H5\n    requires B, C, A form a triangle: mun:triangle-rotate P := A, Q := B, R := C, from H4\n",
            "mun:triangle, from H5 does not reach",
        ),
        // The same, where the scope already holds the claim for another reason:
        // the hypothesis says A, B, C form a triangle, so `A ≠ C` is held before
        // the line is read, and H5 does not say it.
        case(
            "name a line that does not state a claim the scope already holds",
            "proofs/isosceles/isosceles",
            "proofs/isosceles.proof",
            "    requires A ≠ C: mun:triangle, from H4\n",
            "    requires A ≠ C: mun:triangle, from H5\n",
            "mun:triangle, from H5 does not reach",
        ),
        // A requires line below that cites an item asks for that item's
        // hypotheses, and only those: mun:sum-real asks 0 ∈ ℤ and m ∈ ℤ of
        // the range, and nothing asks 1 ∈ ℤ of an `algebra` step whose atoms
        // are x, y and the sum.
        case(
            "a requires line above an item's line that the item does not ask for",
            "proofs/binomial/binomial-step",
            "proofs/binomial.proof",
            "    requires y ∈ ℝ: from H2\n    requires 0 ∈ ℤ: arithmetic\n    requires m ∈ ℕ₀: from H3\n    requires Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k ∈ ℝ: mun:sum-real a := 0, b := m\n",
            "    requires y ∈ ℝ: from H2\n    requires 1 ∈ ℤ: arithmetic\n    requires 0 ∈ ℤ: arithmetic\n    requires m ∈ ℕ₀: from H3\n    requires Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k ∈ ℝ: mun:sum-real a := 0, b := m\n",
            "the requires line of step 1 says 1 ∈ ℤ, and the step neither uses nor asks for it",
        ),
        // A step's proof rests only on what it names (`GOALS.md` decision 9).
        // Without its requires line, `algebra` wants k ∈ ℂ, and the scope holds
        // k ∈ ℤ from line 1, which step 3 does not cite. Offered that, the step
        // would elaborate and verify; it is not offered, so nothing says k ∈ ℂ.
        case(
            "lean on a line the step does not name",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n    requires k ∈ ℝ: from 1\n",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n",
            "nothing says k ∈ ℂ, which this step needs",
        )
        .at("proofs/sqrt2-irrational.proof", "3.  (2k + 1)² = 4k² + 4k + 1"),
        // A requires line rests only on its reason. Line 2 does not say k is an
        // integer, and `mun:int-real` asks it; the scope has it from line 1,
        // which the line does not cite, so the item it names reaches nothing.
        // The import puts the requires line at 31, where it is reported.
        case_importing(
            "give a requires line a reason that is not where its proof comes from",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "import mundane theorem stdlib/numbers/int-real",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n    requires k ∈ ℝ: from 1\n",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n    requires k ∈ ℝ: mun:int-real, from 2\n",
            "the requires line k ∈ ℝ of step 3, read as a step citing what it cites: no clause of mun:int-real reaches",
        )
        .at(
            "proofs/sqrt2-irrational.proof",
            "requires k ∈ ℝ: mun:int-real, from 2",
        ),
        // Everything a step names does work. 2 is a numeral, not an atom, so
        // `algebra` asks nothing about its being real, and the kernel has it
        // from the library; the line is true, well formed, and does nothing.
        case(
            "write a requires line nothing asks for",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "          algebra\n          requires k ∈ ℝ: from K\n",
            "          algebra\n          requires 2 ∈ ℝ: arithmetic\n          requires k ∈ ℝ: from K\n",
            "says 2 ∈ ℝ, and the step neither uses nor asks for it",
        ),
        // The certificate combines lines 2 and 3; line 1 says a + b is at
        // least 0 or below it, which the step does not combine, and is cited
        // for nothing.
        case(
            "cite a line a method step does not combine",
            "proofs/triangle-inequality/triangle-inequality",
            "proofs/triangle-inequality.proof",
            "    4.2.  a + b ≤ |a| + |b|\n          inequalities, from 2, 3\n",
            "    4.2.  a + b ≤ |a| + |b|\n          inequalities, from 1, 2, 3\n",
            "step 4.2 cites 1 and uses nothing it says",
        ),
        // Each atom a method combines is real, and the step says so. The
        // kernel's `ltne` never needs p ∈ ℝ here, and line 4, which the step
        // cites, says only p > 1, so nothing else would see the line gone:
        // only what the method asks for does.
        case(
            "leave out the membership of an atom the method combines",
            "proofs/infinitely-many-primes/prime-above",
            "proofs/infinitely-many-primes.proof",
            "          inequalities, from 4, contradicting 5.6\n          requires p ∈ ℝ: from 3\n",
            "          inequalities, from 4, contradicting 5.6\n",
            "step 5.7 combines p, and nothing it writes or cites says it is a number",
        ),
        // `decide_field` refuses a claim that is not an identity, before
        // anything falls back to stating the step.
        case(
            "claim an algebra step the cited lines do not give",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "    1.14. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a)",
            "    1.14. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1",
            "is not an identity",
        ),
        // A side condition is searched for among what the step names, not among
        // everything in scope. Without 1.2.5 the step still needs T finite,
        // and the scope holds |T| = 2^k: offered it, which route the search took
        // would decide whether a correct page was reported, so it is not
        // offered at all.
        case(
            "settle a side condition from a line the step does not cite",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "n := 2^k, from 1.2.3, 1.2.5, 1.2.6",
            "n := 2^k, from 1.2.3, 1.2.6",
            "no clause of mun:card-disjoint-union reaches what step 1.2.8 claims",
        ),
        // Nothing is taken as stated: a theorem the database gives no target
        // for builds nothing, and a step citing it stops the build where it
        // stands. `card-remove` loses its target.
        case(
            "cite a theorem the database gives no target for",
            "proofs/subsets/subsets-count",
            "corpus/stdlib/counting.records",
            "  then        |X ∖ {a}| = k\n  metamath    hashdifsnp1\n  target      hashdifsnp1 with V := X, N := a, Y := k\n",
            "  then        |X ∖ {a}| ≤ k\n  metamath    hashdifsnp1\n",
            "step 1.2.2 cites mun:stdlib/counting/card-remove, which the database gives no target for, and nothing is taken as stated",
        ),
        // A requires line its method cannot prove stops the build at that
        // line. Without the line saying sin(∠PQR) > 0 above it, nothing gives
        // `inequalities` an order to show sin(∠PQR) ≠ 0 from.
        case(
            "a requires line its method cannot prove",
            "proofs/pythagoras/similar-triangles",
            "proofs/pythagoras.proof",
            "    requires sin(∠PQR) > 0: mun:sine-positive P := P, Q := Q, R := R, from H7\n",
            "",
            "the requires line sin(∠PQR) ≠ 0 of step 12, read as a step citing what it cites:",
        ),
        // A definition with no target is read off a line the step cites that
        // already says the claim; stating the claim instead would take whatever
        // the step claimed, and only a later step using it could notice.
        case(
            "unfold a definition with no target into what it does not say",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "10. For all s ∈ S, s ≤ c.",
            "10. For all s ∈ S, s < c.",
            "mun:stdlib/calculus/upper-bound has no target, and nothing step 10 cites says",
        ),
        // `elcncf2` is read in the page's words, which is a reading and not a
        // licence: continuity with δ where ε belongs, or with δ ≥ 0 where the
        // definition says δ > 0, is not what it says.
        case(
            "unfold continuity into what it does not say",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "|f(x) − f(c′)| < ε for all x",
            "|f(x) − f(c′)| < δ for all x",
            "no method owns this step: elcncf2 does not say",
        )
        .at("proofs/intermediate-value.proof", "15. For all c′ ∈ [a, b]"),
        case(
            "unfold continuity with a weaker bound than it gives",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "there exists δ > 0 such that",
            "there exists δ ≥ 0 such that",
            "elcncf2 does not say",
        ),
        // The least upper bound is the supremum, which is a number only of a
        // set bounded above, and line 7 is what says S is. Without it cited
        // nothing supplies the hypothesis naming a bound, and the step says
        // which.
        case(
            "obtain the least upper bound without the line bounding the set",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "obtain c: axi:completeness S := S, from 5, 2, 7",
            "obtain c: axi:completeness S := S, from 5, 2",
            "step 8 cites axi:stdlib/calculus/completeness, which asks for there is u ∈ ℝ with u is an upper bound of S",
        )
        .at(
            "proofs/intermediate-value.proof",
            "8.  c ∈ ℝ. c is a least upper bound of S.",
        ),
        // Each part of what the claim asks of the witness is one of the
        // target's lemmas, and a part none of them reaches is the target
        // failing, not something to take as stated.
        case(
            "leave out the lemma saying the supremum is least",
            "proofs/intermediate-value/intermediate-value",
            "corpus/stdlib/calculus.records",
            "  target      suprcl, suprub, suprleub with c := sup S",
            "  target      suprcl, suprub with c := sup S",
            "axi:stdlib/calculus/completeness targets suprcl, suprub, and none of them reaches what step 8 obtains",
        ),
        // `arithmetic` works a closed claim out before proving it, and takes
        // nothing as stated: a false one is reported, whether it holds a number
        // past one digit or digits alone.
        case(
            "claim a false numeral fact with a number past one digit",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "requires 10^0 − 1 = 3·0: arithmetic",
            "requires 10^0 − 1 = 3·1: arithmetic",
            "claims 10^0 − 1 = 3·1, which is false",
        ),
        case(
            "claim a false numeral fact of digits",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "requires 9 = 3·3: arithmetic",
            "requires 9 = 3·4: arithmetic",
            "claims 9 = 3·4, which is false",
        ),
        // True, and past what the method shows, an order between two sides
        // that are not numerals until worked out: a theorem stating it is
        // what the page cites, and saying so is the report, and the fact is
        // not stated.
        case(
            "ask arithmetic for a true fact it cannot show",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "10 − 1 = 9\n          mun:ten-minus-one",
            "10 − 1 ≤ 9\n          arithmetic",
            "step 1.5 claims 10 − 1 ≤ 9, which is true, and arithmetic cannot show it yet",
        ),
        // What has no exact value is refused before anything is computed or
        // stated: a division by zero, a number too large to work out, which
        // would run for as long as memory lasts, and a power that is not a
        // rational.
        case(
            "divide by zero in a numeral fact",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "          requires 10 ∈ ℝ: arithmetic\n\n    1.9.",
            "          requires 10 ∈ ℝ: arithmetic\n          requires 3/0 ∈ ℝ: arithmetic\n\n    1.9.",
            "which divides by zero",
        ),
        case(
            "state a numeral too large to work out",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "          requires 10 ∈ ℝ: arithmetic\n\n    1.9.",
            "          requires 10 ∈ ℝ: arithmetic\n          requires 9^(9^9) ∈ ℕ: arithmetic\n\n    1.9.",
            "which is too large to work out",
        ),
        case(
            "raise a numeral to a power that is not whole",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "          requires 10 ∈ ℝ: arithmetic\n\n    1.9.",
            "          requires 10 ∈ ℝ: arithmetic\n          requires 4^(1/2) ∈ ℕ: arithmetic\n\n    1.9.",
            "which is not a rational number",
        ),
        // Named where it is used, `arithmetic` works the fact out first, as it
        // does a step of its own: a false one is reported, never rewritten by.
        case(
            "substitute by a false fact of numerals",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "substitute 0 + 1 = 1 (arithmetic)",
            "substitute 0 + 1 = 2 (arithmetic)",
            "step 1.4 substitutes 0 + 1 = 2, which is false",
        ),
        case(
            "a chain link of numerals that is false",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "= 1(1 + 1)/2            arithmetic",
            "= 1(1 + 1)/3            arithmetic",
            "a link of step 1.2 claims 1 = 1(1 + 1)/3, which is false",
        ),
        // `membership` builds from what the line cites and the lines above it:
        // ε > 0 does not say ε is a real number, no line above says it once
        // this line comes first, and the scope's copy of the line that does is
        // not the requires line's to use unnamed.
        case(
            "membership from a line that says nothing of the atom",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "          requires ε ∈ ℝ: from K3\n          requires ε/2 > 0: inequalities, from A1\n          requires ε/2 ∈ ℝ: membership, from K3\n",
            "          requires ε/2 ∈ ℝ: membership, from A1\n          requires ε ∈ ℝ: from K3\n          requires ε/2 > 0: inequalities, from A1\n",
            "rests on K3, which it does not name",
        ),
        // g(x) is real because of what g is, and a step that uses what a
        // define says cites it (`SYNTAX.md`). Without the define g stays a
        // name, and nothing the step cites says g(x) is real.
        case(
            "membership of a defined function's value without citing its define",
            "proofs/mean-value/mean-value",
            "proofs/mean-value.proof",
            "    membership, from D1\n",
            "    membership\n",
            "is not built from what step 6 cites",
        ),
        // Line 4 says s(x) ∈ ℕ₀ of every x ∈ ℚ and is read at the step's
        // member; line 2 says something else of every pair of naturals, and
        // nothing read at a member of anything gives s(x) ∈ ℕ₀.
        case(
            "a requires line citing a line said of every member that does not say the fact",
            "proofs/rationals-countable/rationals-countable",
            "proofs/rationals-countable.proof",
            "requires s(x) ∈ ℕ₀: from 4",
            "requires s(x) ∈ ℕ₀: from 2",
            "does not reach",
        ),
        // G(a, 0) is the rule at a and 0 only where a is in G's first
        // domain, and nothing the step names says a is real.
        case(
            "read a function of two at a value nothing puts in its domain",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "                    = 1                     1.2\n          requires a ∈ ℝ: from H1\n",
            "                    = 1                     1.2\n",
            "cannot settle a ∈ ℝ",
        ),
        // a ∈ S because S is the points of [a, b] where f is below zero; the
        // item speaks of a set written by its condition, and without the
        // define S is only a name.
        case(
            "membership in a defined set without citing its define",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "u := a, from D1, 1, H6",
            "u := a, from 1, H6",
            "no cited line is what rabid unfolds",
        ),
        // A sum's terms are built for each index in its range, and from 0 the
        // first of them divides by T(0), which nothing says is not zero.
        case(
            "membership of a sum whose first term divides by zero",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: membership, from D1\n                  requires ε ∈ ℝ: from K3\n                  requires n ∈ ℝ: from K4\n                  requires n + 1 ≠ 0: inequalities, from K4\n",
            "                  requires Σ(k = 0 to n) 1/T(k) ∈ ℝ: membership, from D1\n                  requires ε ∈ ℝ: from K3\n                  requires n ∈ ℝ: from K4\n                  requires n + 1 ≠ 0: inequalities, from K4\n",
            "the requires line Σ(k = 0 to n) 1/T(k) ∈ ℝ of step 3.2.5, read as a step citing what it cites:",
        ),
        // Said of every member, a term's divisor must not be zero for each: k ∈ ℤ
        // gives no k ≠ 0.
        case(
            "membership said of every integer where a divisor may be zero",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: membership",
            "requires for all k ∈ ℤ, 1/T(k) ∈ ℝ: membership",
            "the requires line for all k ∈ ℤ, 1/T(k) ∈ ℝ of step 5, read as a step citing what it cites:",
        ),
        // A membership line says what the table in `rules` says it does and
        // nothing more: k ∈ ℤ gives no k ≠ 0, and n ∈ ℝ gives no n ∈ ℤ, since
        // the table goes one way.
        case(
            "a membership read for a bound it does not give",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "    let k ∈ ℕ                                                         (K1)",
            "    let k ∈ ℤ                                                         (K1)",
            "does not reach",
        ),
        case(
            "a membership read into a smaller number system",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "    let n ∈ ℕ                                                         (K2)",
            "    let n ∈ ℝ                                                         (K2)",
            "does not reach",
        ),
        // A link whose terms have a letter may name `arithmetic` where only a
        // piece of numerals alone changes, and that piece is worked out like
        // any closed fact: 2/1 is not 3.
        case(
            "a chain link whose closed piece is false",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "= 2 − 2/(n + 1)                      arithmetic",
            "= 3 − 2/(n + 1)                      arithmetic",
            "which is false",
        ),
        // `fsumdvds` asks that 3 divide each term, for k in the range, and line 1
        // says it for all k ∈ ℕ₀. Without line 1 cited nothing says it.
        case(
            "sum what no cited line says each term of is divisible",
            "proofs/divisibility-by-three/divisibility-by-three",
            "proofs/divisibility-by-three.proof",
            "mun:sum-divisible m := 3, from H1, 1",
            "mun:sum-divisible m := 3, from H1",
            "no clause of mun:sum-divisible reaches what step 2 claims",
        ),
        // A link of a calculation is what the line it cites says, and a line
        // saying something else is not taken for it: its proof would be of the
        // wrong statement, and only the verifier would notice.
        case(
            "cite a line for a link it does not say",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "= k(k + 1)/2 + (k + 1)         1.5",
            "= k(k + 1)/2 + (k + 1)         1.4",
            "1.4 does not say",
        ),
        // What says f is continuous is H5, and so is what says its domain and
        // codomain lie in ℂ, which `elcncf2` asks. Without it cited the step
        // has neither.
        case(
            "unfold continuity without the line saying f is continuous",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "    def:continuous-on, from H5",
            "    def:continuous-on",
            "no method owns this step: no cited line is what elcncf2 unfolds",
        )
        .at("proofs/intermediate-value.proof", "15. For all c′ ∈ [a, b]"),
        // The item asks |X| = k + 1, which C2 says. Without C2 cited, the
        // equation is in scope and not in hand, and the hypothesis must go
        // unanswered rather than be answered by a line the step does not name.
        case(
            "answer a side condition by an equation the step does not cite",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "obtain a: mun:card-nonempty, from K2, C2",
            "obtain a: mun:card-nonempty, from K2",
            "step 1.2.1 cites mun:stdlib/counting/card-nonempty, which asks for |X| = k + 1",
        )
        .at("proofs/subsets.proof", "1.2.1.  a ∈ X"),
        // `elrnmpt1s` reads its map at a term only a cited line supplies. With
        // the line gone nothing says where the map is read, and the body must
        // not be read at the lemma's own variable instead.
        case(
            "put something in an image without the line saying where it comes from",
            "proofs/subsets/powerset-split",
            "proofs/subsets.proof",
            "s := V ∖ {a},\n                    from 1.3.2",
            "s := V ∖ {a}",
            "no clause of mun:added-element-in-image reaches what step 1.3.3 claims",
        ),
        // A target is where the claim lands, and a variable bound to the wrong
        // name makes it land somewhere else. That is reported, not assumed.
        case(
            "bind a target variable to the wrong name",
            "proofs/subsets/subsets-count",
            "corpus/stdlib/counting.records",
            "  target      hashdifsnp1 with V := X, N := a, Y := k",
            "  target      hashdifsnp1 with V := X, N := a, Y := X",
            "no clause of mun:card-remove reaches what step 1.2.2 claims",
        ),
        // `algebra` reads a finite sum as linear where the step's sums are:
        // Σ(a(k)t + b(k))² is t²Σa(k)² + 2tΣa(k)b(k) + Σb(k)², and with
        // 3t in place of 2t the claim is no identity and is refused.
        case(
            "expand a sum linearly with a wrong coefficient",
            "proofs/cauchy-schwarz/cauchy-schwarz",
            "proofs/cauchy-schwarz.proof",
            "    1.3.  Σ(k = 1 to n) (a(k)·t + b(k))² = t²·(Σ(k = 1 to n) a(k)²) + 2t·",
            "    1.3.  Σ(k = 1 to n) (a(k)·t + b(k))² = t²·(Σ(k = 1 to n) a(k)²) + 3t·",
            "is not an identity",
        ),
        // A function's type gives a value only at a point of its domain, and a
        // requires line rests only on what it names, so a line citing the
        // type alone is reported.
        case(
            "cite a function's type for a value without the point's domain",
            "proofs/cauchy-schwarz/cauchy-schwarz",
            "proofs/cauchy-schwarz.proof",
            "requires a(k) ∈ ℝ: from H2, K4",
            "requires a(k) ∈ ℝ: from H2",
            "from H2 does not reach",
        ),
        // A closed exponent's membership of ℕ₀ is placed through the digit it
        // comes to (`by_value`), and (0 − 1) − 0 comes to −1, which is no
        // digit and not in ℕ₀. The term's membership is refused, so the lemma
        // is, and the step is reported rather than the value looked up.
        case(
            "a closed exponent that is not a whole number",
            "proofs/binomial/binomial",
            "proofs/binomial.proof",
            "    1.1.  Σ(k = 0 to 0) C(0, k)·x^(0 − k)·y^k = C(0, 0)·x^(0 − 0)·y^0\n",
            "    1.1.  Σ(k = 0 to 0) C(0, k)·x^((0 − 1) − k)·y^k = C(0, 0)·x^((0 − 1) − 0)·y^0\n",
            "no clause of mun:sum-single reaches what step 1.1 claims",
        ),
        // A definition concluded of a value names that value: line 5 says what
        // n² is, and the step says n² is odd only by writing n := n². The pair
        // is found by its name, and it is not optional (`SYNTAX.md`).
        case(
            "leave out the value a definition is concluded of",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "    mun:odd n := n², from 5",
            "    mun:odd, from 5",
            "is about n, and the step gives n no value",
        ),
        // A link reads its cited equation from either side, and nothing on the
        // page says which: line 2 says |CB| = |BC|, which is neither way round
        // the link's |CA| = |CB|.
        case(
            "cite an equation that says the link neither way round",
            "proofs/isosceles/isosceles",
            "proofs/isosceles.proof",
            "           = |CB|       H5\n",
            "           = |CB|       2\n",
            "2 does not say |CA| = |CB|",
        ),
        // A lemma's conclusion is carried to the claim through the standard
        // form, which reads eldifsn's u =/= a as the page's u ≠ a, down through
        // the ↔ and the "and" it sits in. It reads nothing else: a claim of
        // u = a in its place is still not what eldifsn says.
        case(
            "claim what a lemma says with one relation changed",
            "tests/stdlib/sets/remove-member",
            "tests/stdlib/sets.proof",
            "then u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u ≠ a\n",
            "then u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n\n1.  u ∈ Y ∖ {a} ↔ u ∈ Y and u = a\n",
            "no clause of mun:sets-remove-member reaches what step 1 claims",
        ),
        // A step citing a define by cases takes the case from a line it cites.
        // Here the only line cited says x ∈ A, which is h's domain and no case.
        case(
            "cite a define by cases from a line that does not say the case",
            "proofs/schroeder-bernstein/schroeder-bernstein",
            "proofs/schroeder-bernstein.proof",
            "                  D2, from 8.2.1\n",
            "                  D2, from 8.2.2\n",
            "no line the step cites says which case",
        ),
        // An obtain from part-builder claims what K's condition says of the set
        // the cited line puts in K: K18 gives Y = aH, and Z = aH is another
        // claim.
        case(
            "obtain from part-builder a claim the condition does not give",
            "proofs/lagrange/lagrange",
            "proofs/lagrange.proof",
            "    14.1. a ∈ G. Y = aH.\n",
            "    14.1. a ∈ G. Z = aH.\n",
            "nothing step 14.1 cites says",
        )
        .at("proofs/lagrange.proof", "14.1. a ∈ G. Z = aH."),
        // An obtain from a definition reads its left side off a line it cites,
        // through a define's name where the line uses one: C9 says b ∈ R, and R
        // is f[C]. K7 says only that b is in B.
        case(
            "obtain from a definition citing no line that says its left side",
            "proofs/schroeder-bernstein/schroeder-bernstein",
            "proofs/schroeder-bernstein.proof",
            "obtain x: mun:image u := b, Y := C, from D1, C9",
            "obtain x: mun:image u := b, Y := C, from D1, K7",
            "nothing step 8.2.1 cites says",
        ),
        // A part of A is asked of M's argument, and the line named must say it:
        // A1 says X ⊆ Y, which is not that Y is a part of A.
        case(
            "a requires line for a part naming a line that does not say it",
            "proofs/schroeder-bernstein/fixed-part",
            "proofs/schroeder-bernstein.proof",
            "          requires Y ⊆ A: from K4\n",
            "          requires Y ⊆ A: from A1\n",
            "from A1 does not reach",
        ),
        // g ∈ gH is shown by the member of H that g is g times, and the line
        // saying g·e = g is what names it.
        case(
            "a coset member with no line naming what it is the element times",
            "proofs/lagrange/lagrange",
            "proofs/lagrange.proof",
            "mun:coset u := g, from K3, 4.1, 4.2",
            "mun:coset u := g, from K3, 4.1",
            "no cited line names a witness",
        )
        .at("proofs/lagrange.proof", "4.3.  g ∈ gH"),
        // `inequalities` takes two terms differing only from a line it cites,
        // and not from a requires line above: 0 ≤ r alone gives no 0 < r.
        case(
            "rest an inequalities line on r ≠ 0 above it instead of citing it",
            "proofs/bezout/least-combination-divides",
            "proofs/bezout.proof",
            "          requires 0 < r: inequalities, from 1, S\n",
            "          requires r ≠ 0: from S\n          requires 0 < r: inequalities, from 1\n",
            "0 < r does not follow from what step 3.1 cites",
        ),
        // An angle's membership left out of an `algebra` step: the search for
        // it goes only as deep as any side condition's, so the step is
        // reported at once rather than after minutes of looking.
        case(
            "leave out an atom's membership that only a deep search could find",
            "proofs/pythagoras/similar-triangles",
            "proofs/pythagoras.proof",
            "    requires ∠QPR ∈ ℝ: mun:triangle-angle-real, from H7\n",
            "",
            "nothing it writes or cites says it is a number",
        ),
        // f(x) ∈ ℝ is H4's to say, and a step that needs it names H4: a
        // function's type is cited for its values, outside a sum's terms.
        case(
            "a function's value from a type the step does not name",
            "proofs/mean-value/mean-value",
            "proofs/mean-value.proof",
            "    requires f(x) ∈ ℝ: from H4\n",
            "",
            "is not built from what step 8 cites",
        ),
    ]
}

fn nets() -> Vec<Case> {
    vec![
        // Step 1.2.8 needs T finite and no longer cites 1.2.5, which says
        // |T| = 2^k. Offered the whole scope, the search finds T finite through
        // that line, and with R1 taken away the step would elaborate and
        // verify: nothing else here objects, since the step cites an item and
        // the method checks do not apply.
        case(
            "settle a side condition from a line the step does not cite, with nothing to stop the search",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "n := 2^k, from 1.2.3, 1.2.5, 1.2.6",
            "n := 2^k, from 1.2.3, 1.2.6",
            "step 1.2.8 rests on 1.2.5, which it does not name",
        ),
        // The requires line's reason cites line 2, and `mun:int-real` asks k
        // an integer, which line 1 says. With R2 taken away the step would
        // elaborate. The import puts the line one lower.
        case_importing(
            "give a requires line a reason that is not where its proof comes from, with nothing to stop the search",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "import mundane theorem stdlib/numbers/int-real",
            "    requires k ∈ ℝ: from 1\n\n4.",
            "    requires k ∈ ℝ: mun:int-real, from 2\n\n4.",
            "the requires line rests on 1, which it does not name",
        )
        .at(
            "proofs/sqrt2-irrational.proof",
            "requires k ∈ ℝ: mun:int-real, from 2",
        ),
    ]
}
