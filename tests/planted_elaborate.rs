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
    old: &'static str,
    new: &'static str,
    expect: &'static str,
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
        tree.write(case.file, text.replacen(case.old, case.new, 1).into_bytes());
        match run(&tree, case.theorem, &library, *net) {
            None => {
                said.push(format!(
                    "  NOT CAUGHT    {}\n      it elaborated: the defect was taken as stated",
                    case.name
                ));
                missed += 1;
            }
            Some(got) if got.contains(case.expect) => {
                said.push(format!("  caught        {}", case.name));
            }
            Some(got) => {
                let got: String = got.chars().take(160).collect();
                said.push(format!(
                    "  NOT CAUGHT    {}\n      expected {:?}\n      got      {got:?}",
                    case.name, case.expect
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
        // A formula that does not lex is a defect with a position, and not a
        // route declining: taken for one, the step would be assumed and the
        // build would go green.
        case(
            "a requires line that does not lex",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "                  requires a ∈ ℝ: from H1\n                  requires a^(k + 1) ∈ ℝ",
            "                  requires a ¿ ℝ: from H1\n                  requires a^(k + 1) ∈ ℝ",
            "proofs/geometric-series.proof:89",
        ),
        // `substitute` walks its equation both ways and each sentence of the
        // line it names, trying the next where one declines. A name the proof
        // never introduced is not one of those: it is a defect.
        case(
            "substitute a name the proof never introduced",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "          substitute a^(0 + 1) = a (line 2.6)",
            "          substitute a^(0 + 1) = z (line 2.6)",
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
            "proofs/triangle-inequality.proof:36  no clause of def:stdlib/numbers/abs gives what step 2.5 claims",
        ),
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
            "proofs/triangle-inequality.proof:36  no clause of def:stdlib/numbers/abs gives what step 2.5 claims",
        ),
        // A `requires` line has a claim and a reason, and the reason is what
        // proves it. Here line 5 does not say `C ≠ A` and line 6 does; taking
        // it from the theorem's own hypothesis and turning it with `necom`
        // would verify, and leave the line the page named unused.
        case(
            "name a line that does not state the side condition",
            "proofs/isosceles/isosceles",
            "proofs/isosceles.proof",
            "    requires C ≠ A: def:stdlib/geometry/triangle, from 6",
            "    requires C ≠ A: def:stdlib/geometry/triangle, from 5",
            "def:stdlib/geometry/triangle, from 5 does not reach",
        ),
        // The same, where the scope already holds the claim for another reason:
        // the hypothesis says A, B, C form a triangle, so `A ≠ B` is held before
        // the line is read, and line 6 does not say it.
        case(
            "name a line that does not state a claim the scope already holds",
            "proofs/isosceles/isosceles",
            "proofs/isosceles.proof",
            "    requires A ≠ B: def:stdlib/geometry/triangle, from 5",
            "    requires A ≠ B: def:stdlib/geometry/triangle, from 6",
            "def:stdlib/geometry/triangle, from 6 does not reach",
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
            "proofs/sqrt2-irrational.proof:17  nothing says m e. CC, which this step needs",
        ),
        // A requires line rests only on its reason. Line 2 does not say k is an
        // integer, and `thm:stdlib/numbers/int-real` asks it; the scope has it
        // from line 1, which the line does not cite, so the item it names
        // reaches nothing.
        case(
            "give a requires line a reason that is not where its proof comes from",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n    requires k ∈ ℝ: from 1\n",
            "3.  (2k + 1)² = 4k² + 4k + 1\n    algebra\n    requires k ∈ ℝ: thm:stdlib/numbers/int-real, from 2\n",
            "proofs/sqrt2-irrational.proof:17  thm:stdlib/numbers/int-real targets zre, and none of them reaches m e. RR",
        ),
        // Everything a step names does work. 2 is a numeral, not an atom, so
        // `algebra` asks nothing about its being real, and the kernel has it
        // from the library; the line is true, well formed, and does nothing.
        case(
            "write a requires line nothing asks for",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "                  requires 2 ≠ 0: arithmetic\n",
            "                  requires 2 ≠ 0: arithmetic\n                  requires 2 ∈ ℝ: arithmetic\n",
            "says 2 ∈ ℝ, and the step neither uses nor asks for it",
        ),
        // The certificate combines lines 3 and 4; line 1 says a + b ∈ ℝ, which
        // the step writes as its atoms instead, and is cited for nothing.
        case(
            "cite a line a method step does not combine",
            "proofs/triangle-inequality/triangle-inequality",
            "proofs/triangle-inequality.proof",
            "    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 3, 4\n",
            "    5.2.  a + b ≤ |a| + |b|\n          inequalities, from 1, 3, 4\n",
            "step 5.2 cites 1 and uses nothing it says",
        ),
        // Each atom a method combines is real, and the step says so. The
        // kernel's `ltne` never needs d ∈ ℝ here, so nothing else would see the
        // line gone: only what the method asks for does.
        case(
            "leave out the membership of an atom the method combines",
            "proofs/sqrt2-irrational/lowest-terms",
            "proofs/sqrt2-irrational.proof",
            "    3.7.  d ≠ 1\n          inequalities, from 3.1\n          requires d ∈ ℝ: from 3.1\n",
            "    3.7.  d ≠ 1\n          inequalities, from 3.1\n",
            "step 3.7 combines d, and nothing it writes or cites says it is a number",
        ),
        // `decide_field` refuses a claim that is not an identity, before
        // anything falls back to stating the step.
        case(
            "claim an algebra step the cited lines do not give",
            "proofs/geometric-series/geometric-sum",
            "proofs/geometric-series.proof",
            "    2.10.6. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a)",
            "    2.10.6. (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1",
            "is not an identity",
        ),
        // A side condition is searched for among what the step names, not among
        // everything in scope. Without 1.2.1.5 the step still needs T finite,
        // and the scope holds |T| = 2^k: offered it, which route the search took
        // would decide whether a correct page was reported, so it is not
        // offered at all.
        case(
            "settle a side condition from a line the step does not cite",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "n := 2^k, from 1.2.1.3, 1.2.1.5, 1.2.1.6",
            "n := 2^k, from 1.2.1.3, 1.2.1.6",
            "no clause of thm:stdlib/counting/card-disjoint-union reaches what step 1.2.1.8 claims",
        ),
        // An item taken as stated is stated as the item says it. Stating the
        // step's claim under the item's hypotheses instead would assume whatever
        // the step claimed, and the kernel accepts whatever is assumed. No step
        // in the corpus cites an item taken as stated for a claim it could get
        // wrong, so one is made: `card-remove` loses its target and says less
        // than step 1.2.1.2 claims of it.
        case(
            "claim what an item taken as stated does not state",
            "proofs/subsets/subsets-count",
            "corpus/stdlib/counting.records",
            "  then        |X ∖ {a}| = k\n  metamath    hashdifsnp1\n  target      hashdifsnp1 with V := X, N := a, Y := k\n",
            "  then        |X ∖ {a}| ≤ k\n  metamath    hashdifsnp1\n",
            "thm:stdlib/counting/card-remove is taken as stated and states",
        ),
        // A definition with no target is stated as the definition says it and
        // the claim read off one side. Stating the claim under the cited lines
        // would take whatever the step claimed, and only a later step using it
        // could notice.
        case(
            "unfold a definition taken as stated into what it does not say",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "10. For all s ∈ S, s ≤ c.",
            "10. For all s ∈ S, s < c.",
            "def:stdlib/calculus/upper-bound is taken as stated and states",
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
            "proofs/intermediate-value.proof:79  no method owns this step: elcncf2 does not say",
        ),
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
        // nothing names a bound, and the step says which.
        case(
            "obtain the least upper bound without the line bounding the set",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2, 7",
            "obtain c: thm:stdlib/calculus/completeness S := S, from 5, 2",
            "proofs/intermediate-value.proof:53  no cited line names a witness for E. x e. RR",
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
            "thm:stdlib/calculus/completeness targets suprcl, suprub, and none of them reaches what step 8 obtains",
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
        // True, and past what the method shows while it reads digits alone: a
        // theorem stating it is what the page cites, and saying so is the
        // report, and the fact is not stated.
        case(
            "ask arithmetic for a true fact it cannot show",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "10 − 1 = 9\n                  thm:stdlib/numbers/ten-minus-one",
            "10 − 1 = 9\n                  arithmetic",
            "step 1.3.4 claims 10 − 1 = 9, which is true, and arithmetic cannot show it yet",
        ),
        // What has no exact value is refused before anything is computed or
        // stated: a division by zero, a number too large to work out, which
        // would run for as long as memory lasts, and a power that is not a
        // rational.
        case(
            "divide by zero in a numeral fact",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.",
            "                  requires 10 ∈ ℝ: arithmetic\n                  requires 3/0 ∈ ℝ: arithmetic\n\n          1.3.8.",
            "which divides by zero",
        ),
        case(
            "state a numeral too large to work out",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.",
            "                  requires 10 ∈ ℝ: arithmetic\n                  requires 9^(9^9) ∈ ℕ: arithmetic\n\n          1.3.8.",
            "which is too large to work out",
        ),
        case(
            "raise a numeral to a power that is not whole",
            "proofs/divisibility-by-three/ten-power-congruent",
            "proofs/divisibility-by-three.proof",
            "                  requires 10 ∈ ℝ: arithmetic\n\n          1.3.8.",
            "                  requires 10 ∈ ℝ: arithmetic\n                  requires 4^(1/2) ∈ ℕ: arithmetic\n\n          1.3.8.",
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
            "step 2.4 substitutes 0 + 1 = 2, which is false",
        ),
        case(
            "a chain link of numerals that is false",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "= 1(1 + 1)/2            arithmetic",
            "= 1(1 + 1)/3            arithmetic",
            "a link of step 1.2 claims 1 = 1(1 + 1)/3, which is false",
        ),
        // `membership` builds from what the line cites: ε > 0 does not say ε is
        // a real number, and the scope's copy of the line that does is not
        // the requires line's to use unnamed.
        case(
            "membership from a line that says nothing of the atom",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "requires ε/2 ∈ ℝ: membership, from K3",
            "requires ε/2 ∈ ℝ: membership, from A1",
            "rests on K3, which it does not name",
        ),
        // A sum's terms are built for each index in its range, and from 0 the
        // first of them divides by T(0), which nothing says is not zero.
        case(
            "membership of a sum whose first term divides by zero",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: membership\n                  requires ε ∈ ℝ: from K3\n                  requires n ∈ ℝ: from K4\n                  requires n + 1 ≠ 0: inequalities, from K4\n                  requires N ∈ ℝ: from 3.2",
            "                  requires Σ(k = 0 to n) 1/T(k) ∈ ℝ: membership\n                  requires ε ∈ ℝ: from K3\n                  requires n ∈ ℝ: from K4\n                  requires n + 1 ≠ 0: inequalities, from K4\n                  requires N ∈ ℝ: from 3.2",
            "is not built from what the requires line cites",
        ),
        // Said of every member, a term's divisor must not be zero for each: k ∈ ℤ
        // gives no k ≠ 0.
        case(
            "membership said of every integer where a divisor may be zero",
            "proofs/triangular-reciprocals/triangular-reciprocals",
            "proofs/triangular-reciprocals.proof",
            "requires for all k ∈ ℕ, 1/T(k) ∈ ℝ: membership",
            "requires for all k ∈ ℤ, 1/T(k) ∈ ℝ: membership",
            "is not built from what the requires line cites",
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
            "thm:stdlib/sums/sum-divisible m := 3, from H1, 1",
            "thm:stdlib/sums/sum-divisible m := 3, from H1",
            "no clause of thm:stdlib/sums/sum-divisible reaches what step 2 claims",
        ),
        // A link of a calculation is what the line it cites says, and a line
        // saying something else is not taken for it: its proof would be of the
        // wrong statement, and only the verifier would notice.
        case(
            "cite a line for a link it does not say",
            "proofs/sum-formula/sum-formula",
            "proofs/sum-formula.proof",
            "= k(k + 1)/2 + (k + 1)         1.3.3",
            "= k(k + 1)/2 + (k + 1)         1.3.2",
            "1.3.2 does not say",
        ),
        // What says f is continuous is H5, and so is what says its domain and
        // codomain lie in ℂ, which `elcncf2` asks. Without it cited the step
        // has neither.
        case(
            "unfold continuity without the line saying f is continuous",
            "proofs/intermediate-value/intermediate-value",
            "proofs/intermediate-value.proof",
            "    def:stdlib/calculus/continuous-on, from H5",
            "    def:stdlib/calculus/continuous-on",
            "proofs/intermediate-value.proof:79  no method owns this step: no cited line is what elcncf2 unfolds",
        ),
        // An item's target asks a side condition the page never writes, and
        // `rewritten` answers it through the equation the step cites: `0 < |X|`
        // is `0 < k + 1` by C2. Without C2 cited, the equation is in scope and
        // not in hand, and the side condition must go unanswered.
        case(
            "answer a side condition by an equation the step does not cite",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "obtain a: thm:stdlib/counting/card-nonempty, from K2, C2",
            "obtain a: thm:stdlib/counting/card-nonempty, from K2",
            "thm:stdlib/counting/card-nonempty targets hashgt0elex, and none of them reaches",
        ),
        // `elrnmpt1s` reads its map at a term only a cited line supplies. With
        // the line gone nothing says where the map is read, and the body must
        // not be read at the lemma's own variable instead.
        case(
            "put something in an image without the line saying where it comes from",
            "proofs/subsets/powerset-split",
            "proofs/subsets.proof",
            "s := V ∖ {a},\n                    from 1.3.2",
            "s := V ∖ {a}",
            "no clause of thm:stdlib/functions/added-element-in-image reaches what step 1.3.3 claims",
        ),
        // A target is where the claim lands, and a variable bound to the wrong
        // name makes it land somewhere else. That is reported, not assumed.
        case(
            "bind a target variable to the wrong name",
            "proofs/subsets/subsets-count",
            "corpus/stdlib/counting.records",
            "  target      hashdifsnp1 with V := X, N := a, Y := k",
            "  target      hashdifsnp1 with V := X, N := a, Y := X",
            "no clause of thm:stdlib/counting/card-remove reaches what step 1.2.1.2 claims",
        ),
        // `sumeq2dv` forbids the sum's index in the scope, and the induction
        // hypothesis names it, so the lemma is proved one frame out. The line it
        // reads term by term is proved in the inner frame, and handed across it
        // would be a proof of another statement, which only the verifier would
        // refuse. An outer frame is offered only the lines it holds, and the
        // step is reported.
        case(
            "rewrite a sum term by term under a hypothesis naming its index",
            "proofs/binomial/binomial",
            "proofs/binomial.proof",
            "          1.8.4.  (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y) = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n                  thm:binomial-step m := m, from H1, H2, K\n\n          1.8.5.  (x + y)^(m + 1) = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n                  calculation\n                    (x + y)^(m + 1) = (x + y)^m·(x + y)                                          1.8.2\n                                    = (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y)              1.8.3\n                                    = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k          1.8.4\n",
            "          1.8.4.  m ∈ ℤ\n                  thm:stdlib/numbers/nat0-int, from K\n\n          1.8.5.  For all k ∈ {0, …, m}, k + 0 = k.\n                  fix\n                  let k ∈ {0, …, m}                                   (J)\n\n                  1.8.5.1.  k ∈ ℤ\n                            thm:stdlib/sums/range-integer a := 0, b := m, from J\n                            requires 0 ∈ ℤ: arithmetic\n                            requires m ∈ ℤ: from 1.8.4\n\n                  1.8.5.2.  k ∈ ℝ\n                            thm:stdlib/numbers/int-real, from 1.8.5.1\n\n                  1.8.5.3.  k + 0 = k\n                            algebra\n                            requires k ∈ ℝ: from 1.8.5.2\n\n          1.8.6.  Σ(k = 0 to m) (k + 0) = Σ(k = 0 to m) k\n                  thm:stdlib/sums/sum-termwise a := 0, b := m, from 1.8.5\n                  requires 0 ∈ ℤ: arithmetic\n                  requires m ∈ ℤ: from 1.8.4\n\n          1.8.7.  (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y) = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n                  thm:binomial-step m := m, from H1, H2, K\n\n          1.8.8.  (x + y)^(m + 1) = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k\n                  calculation\n                    (x + y)^(m + 1) = (x + y)^m·(x + y)                                          1.8.2\n                                    = (Σ(k = 0 to m) C(m, k)·x^(m − k)·y^k)·(x + y)              1.8.3\n                                    = Σ(k = 0 to m + 1) C(m + 1, k)·x^((m + 1) − k)·y^k          1.8.7\n",
            "no clause of thm:stdlib/sums/sum-termwise reaches what step 1.8.6 claims",
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
            "no clause of thm:stdlib/sums/sum-single reaches what step 1.1 claims",
        ),
        // A definition concluded of a value names that value: line 5 says what
        // n² is, and the step says n² is odd only by writing n := n². The pair
        // is found by its name, and it is not optional (`SYNTAX.md`).
        case(
            "leave out the value a definition is concluded of",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "    def:stdlib/divisibility/odd n := n², from 5",
            "    def:stdlib/divisibility/odd, from 5",
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
            "no clause of thm:stdlib/sets/remove-member reaches what step 1 claims",
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
            "    15.1. a ∈ G. Y = aH.\n",
            "    15.1. a ∈ G. Z = aH.\n",
            "proofs/lagrange.proof:311  nothing step 15.1 cites says",
        ),
        // An obtain from a definition reads its left side off a line it cites,
        // through a define's name where the line uses one: C9 says b ∈ R, and R
        // is f[C]. K7 says only that b is in B.
        case(
            "obtain from a definition citing no line that says its left side",
            "proofs/schroeder-bernstein/schroeder-bernstein",
            "proofs/schroeder-bernstein.proof",
            "obtain x: def:stdlib/functions/image u := b, Y := C, from C9",
            "obtain x: def:stdlib/functions/image u := b, Y := C, from K7",
            "nothing step 8.2.1 cites says",
        ),
        // A part of A is asked of M's argument, and the line named must say it:
        // line 3 says every member of D is one, which is not C.
        case(
            "a requires line for a part naming a line that does not say it",
            "proofs/schroeder-bernstein/fixed-part",
            "proofs/schroeder-bernstein.proof",
            "    def:stdlib/sets/part-builder u := A ∖ M(C), from 10, 13\n    requires C ⊆ A: from 4\n",
            "    def:stdlib/sets/part-builder u := A ∖ M(C), from 10, 13\n    requires C ⊆ A: from 3\n",
            "from 3 does not reach",
        ),
        // g ∈ gH is shown by the member of H that g is g times, and the line
        // saying g·e = g is what names it.
        case(
            "a coset member with no line naming what it is the element times",
            "proofs/lagrange/lagrange",
            "proofs/lagrange.proof",
            "def:stdlib/groups/coset u := g, from K3, 5.1, 5.2",
            "def:stdlib/groups/coset u := g, from K3, 5.1",
            "proofs/lagrange.proof:62  no cited line names a witness",
        ),
    ]
}

fn nets() -> Vec<Case> {
    vec![
        // Step 1.2.1.8 needs T finite and no longer cites 1.2.1.5, which says
        // |T| = 2^k. Offered the whole scope, the search finds T finite through
        // that line, and with R1 taken away the step would elaborate and
        // verify: nothing else here objects, since the step cites an item and
        // the method checks do not apply.
        case(
            "settle a side condition from a line the step does not cite, with nothing to stop the search",
            "proofs/subsets/subsets-count",
            "proofs/subsets.proof",
            "n := 2^k, from 1.2.1.3, 1.2.1.5, 1.2.1.6",
            "n := 2^k, from 1.2.1.3, 1.2.1.6",
            "step 1.2.1.8 rests on 1.2.1.5, which it does not name",
        ),
        // The requires line's reason cites line 2, and
        // `thm:stdlib/numbers/int-real` asks k an integer, which line 1 says.
        // With R2 taken away the step would elaborate.
        case(
            "give a requires line a reason that is not where its proof comes from, with nothing to stop the search",
            "proofs/sqrt2-irrational/odd-square",
            "proofs/sqrt2-irrational.proof",
            "    requires k ∈ ℝ: from 1\n\n4.",
            "    requires k ∈ ℝ: thm:stdlib/numbers/int-real, from 2\n\n4.",
            "proofs/sqrt2-irrational.proof:19  the requires line rests on 1, which it does not name",
        ),
    ]
}
