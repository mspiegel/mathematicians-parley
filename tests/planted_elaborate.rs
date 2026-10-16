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
        // An order of two roots asks each root be real, and the message names
        // that membership, not the one in ℂ an equation would ask.
        case(
            "an order whose atoms no line says are real",
            "tests/elaborator/an-atom-not-said-real/an-order-of-two-roots",
            "tests/elaborator/an-atom-not-said-real.proof",
            "    requires √A ∈ ℝ: from 1\n    requires √B ∈ ℝ: from 2\n",
            "",
            "nothing says √B ∈ ℝ, which this step needs",
        ),
        // A chain's congruence of numerals is worked out like any closed
        // fact: 10 is not 2 more than a multiple of 3.
        case(
            "a congruence link of numerals that does not hold",
            "proofs/wiedijk/divisibility-by-three/ten-power-congruent",
            "proofs/wiedijk/divisibility-by-three.proof",
            "                       ≡ 1 (mod 3)        arithmetic",
            "                       ≡ 2 (mod 3)        arithmetic",
            "which is false",
        ),
        // Two equations each multiplied by a term is two steps: the proof
        // multiplies each law of sines in a step of its own and joins them by
        // a calculation, and one `algebra` step citing both is refused.
        case(
            "one algebra step multiplying two cited equations",
            "proofs/wiedijk/pythagoras/similar-triangles",
            "proofs/wiedijk/pythagoras.proof",
            "    calculation\n      |PQ|·|P′R′|·sin(∠PQR) = |PR|·|P′R′|·sin(∠QRP)       9\n                            = |P′Q′|·|PR|·sin(∠PQR)       10",
            "    algebra, from 5, 8\n    requires |PQ| ∈ ℝ: mun:distance-real P := P, Q := Q\n    requires |PR| ∈ ℝ: mun:distance-real P := P, Q := R\n    requires |P′Q′| ∈ ℝ: mun:distance-real P := P′, Q := Q′\n    requires |P′R′| ∈ ℝ: mun:distance-real P := P′, Q := R′\n    requires ∠PQR ∈ ℝ: mun:triangle-angle-real, from H7\n    requires sin(∠PQR) ∈ ℝ: mun:sin-real a := ∠PQR\n    requires ∠QRP ∈ ℝ: mun:triangle-angle-real, from H7\n    requires sin(∠QRP) ∈ ℝ: mun:sin-real a := ∠QRP",
            "at most one equation multiplied by a term",
        ),
        // A formula that does not lex is a defect with a position, the line
        // it is written on, and not a route declining: taken for one, the
        // step would be assumed and the build would go green.
        case(
            "a requires line that does not lex",
            "proofs/wiedijk/geometric-series/geometric-sum",
            "proofs/wiedijk/geometric-series.proof",
            "          requires 1 − a ≠ 0: algebra, from H2\n          requires a^(k + 1) ∈ ℝ",
            "          requires 1 − a ¿ 0: algebra, from H2\n          requires a^(k + 1) ∈ ℝ",
            "",
        )
        .at("proofs/wiedijk/geometric-series.proof", "requires 1 − a ¿ 0"),
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
        // Dropping the + 0 asks that what is left be a number, and q(x) ∈ ℂ is
        // a function's value, which the step says in a requires line: without
        // it nothing does.
        case(
            "drop a 0 from a term no line says is a number",
            "proofs/wiedijk/factor/factor",
            "proofs/wiedijk/factor.proof",
            "          substitute p(a) = 0 (H3) into line 2.1\n          requires q(x) ∈ ℂ: mun:polynomial-value p := q, from 1\n",
            "          substitute p(a) = 0 (H3) into line 2.1\n",
            "drops an identity element from what the substitution makes, and nothing says (x − a) · q(x) is a number",
        ),
        // The certificate combines lines 2 and 3; line 1 says a + b is at
        // least 0 or below it, which the step does not combine, and is cited
        // for nothing.
        case(
            "cite a line a method step does not combine",
            "proofs/wiedijk/triangle-inequality/triangle-inequality",
            "proofs/wiedijk/triangle-inequality.proof",
            "    4.2.  a + b ≤ |a| + |b|\n          inequalities, from 2, 3\n",
            "    4.2.  a + b ≤ |a| + |b|\n          inequalities, from 1, 2, 3\n",
            "step 4.2 cites 1 and uses nothing it says",
        ),
        // Each atom a method combines is real, and the step says so where
        // the atom is not a letter, a numeral or built from them by the
        // operations a membership said once covers: 2^p is a power to a
        // letter. The kernel's `ltne` never needs 2^p ∈ ℝ here, and line 4.8,
        // which the step cites, says only 2^p − 1 > 1, so nothing else would
        // see the line gone: only what the method asks for does.
        case(
            "leave out the membership of an atom the method combines",
            "proofs/wiedijk/perfect-numbers/euclid-perfect",
            "proofs/wiedijk/perfect-numbers.proof",
            "            2^p − 1 ≠ 1      weakening\n          requires 2^p ∈ ℝ: membership, from H1\n",
            "            2^p − 1 ≠ 1      weakening\n",
            "nothing says 2^p ∈ ℝ, which this step needs",
        )
        .at("proofs/wiedijk/perfect-numbers.proof", "2^p − 1 ≠ 1      weakening"),
        // A divisor nothing says is not zero is named as the page writes
        // it: set.mm's =/= is said back as the page's ≠.
        case(
            "divide by a term no line says is not zero",
            "proofs/wiedijk/mean-value/mean-value",
            "proofs/wiedijk/mean-value.proof",
            "    algebra, from 29\n    requires b − a ≠ 0: weakening, from 1\n",
            "    algebra, from 29\n",
            "nothing says b − a ≠ 0, which this step needs to divide by it",
        ),
        // A requires line its method cannot prove stops the build at that
        // line. Citing nothing, it leaves `inequalities` no order to show
        // sin(∠PQR) ≠ 0 from: the order is step 12's, and only step 13 cites it.
        case(
            "a requires line its method cannot prove",
            "proofs/wiedijk/pythagoras/similar-triangles",
            "proofs/wiedijk/pythagoras.proof",
            "    requires sin(∠PQR) ≠ 0: from 13\n",
            "    requires sin(∠PQR) ≠ 0: inequalities\n",
            "the requires line sin(∠PQR) ≠ 0 of step 14, read as a step citing what it cites:",
        ),
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
        // `membership` builds from what the line cites and the lines above it:
        // f(a) is real because a is in f's domain [a, b], which line 2 says
        // and no introducing line says once. H3 says a < b, nothing of where
        // a lies, and line 2 in scope is not the requires line's to use
        // unnamed, so the quotient is not built.
        case(
            "membership from a line that says nothing of the atom",
            "proofs/wiedijk/mean-value/mean-value",
            "proofs/wiedijk/mean-value.proof",
            "    membership, from D1, D2\n    requires f(x) ∈ ℝ: from H4\n    requires b − a ≠ 0: weakening, from 1\n    requires (f(a) − f(b))/(b − a) ∈ ℝ: membership, from H1, H2, H4, 2, 3\n",
            "    membership, from D1, D2\n    requires f(x) ∈ ℝ: from H4\n    requires b − a ≠ 0: weakening, from 1\n    requires (f(a) − f(b))/(b − a) ∈ ℝ: membership, from H1, H2, H3, H4, 3\n",
            "the requires line (f(a) − f(b))/(b − a) ∈ ℝ of step 9, read as a step citing what it cites: (f(a) − f(b))/(b − a) ∈ ℝ is not built",
        ),
        // g(x) is real because of what g is, and a step that uses what a
        // define says cites it (`SYNTAX.md`). Without the define g stays a
        // name, and nothing the step cites says g(x) is real.
        case(
            "membership of a defined function's value without citing its define",
            "proofs/wiedijk/mean-value/mean-value",
            "proofs/wiedijk/mean-value.proof",
            "    membership, from D1\n",
            "    membership\n",
            "is not built from what step 7 cites",
        ),
        // Line 4 says s(x) ∈ ℕ₀ of every x ∈ ℚ and is read at the step's
        // member; line 2 says something else of every pair of naturals, and
        // nothing read at a member of anything gives s(x) ∈ ℕ₀.
        case(
            "a requires line citing a line said of every member that does not say the fact",
            "proofs/wiedijk/rationals-countable/rationals-countable",
            "proofs/wiedijk/rationals-countable.proof",
            "requires s(x) ∈ ℕ₀: from 4",
            "requires s(x) ∈ ℕ₀: from 2",
            "does not reach",
        ),
        // A sum's terms are said real at every point by step 2, of k ∈ ℕ, and
        // from 0 the first of them divides by T(0), which step 2 does not
        // speak of.
        case(
            "membership of a sum whose first term divides by zero",
            "proofs/wiedijk/triangular-reciprocals/triangular-reciprocals",
            "proofs/wiedijk/triangular-reciprocals.proof",
            "                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: mun:sum-real a := 1, b := n, from 2\n                  requires n + 1 ≠ 0: weakening, from 6.2.5\n\n          6.2.10.",
            "                  requires Σ(k = 1 to n) 1/T(k) ∈ ℝ: mun:sum-real a := 1, b := n, from 2\n                  requires Σ(k = 0 to n) 1/T(k) ∈ ℝ: mun:sum-real a := 0, b := n, from 2\n                  requires n + 1 ≠ 0: weakening, from 6.2.5\n\n          6.2.10.",
            "the requires line of step 6.2.9 cites 2, and mun:sum-real asks for nothing it says",
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
        // A function's type gives a value only at a point of its domain, and a
        // requires line rests only on what it names, so a line citing the
        // type alone is reported.
        case(
            "cite a function's type for a value without the point's domain",
            "proofs/wiedijk/cauchy-schwarz/cauchy-schwarz",
            "proofs/wiedijk/cauchy-schwarz.proof",
            "requires a(k) ∈ ℝ: from H2, K4",
            "requires a(k) ∈ ℝ: from H2",
            "from H2 does not reach",
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
        // A part of A is asked of M's argument, and the line named must say it:
        // A1 says X ⊆ Y, which is not that Y is a part of A.
        case(
            "a requires line for a part naming a line that does not say it",
            "proofs/wiedijk/schroeder-bernstein/fixed-part",
            "proofs/wiedijk/schroeder-bernstein.proof",
            "          requires Y ⊆ A: from K4\n",
            "          requires Y ⊆ A: from A1\n",
            "from A1 does not reach",
        ),
        // f(x) ∈ ℝ is H4's to say, and a step that needs it names H4: a
        // function's type is cited for its values, outside a sum's terms.
        case(
            "a function's value from a type the step does not name",
            "proofs/wiedijk/mean-value/mean-value",
            "proofs/wiedijk/mean-value.proof",
            "    requires f(x) ∈ ℝ: from H4\n",
            "",
            "is not built from what step 9 cites",
        ),
        // k's membership is said once, by K, and every step has it without
        // naming K. A step citing K for it cites a line it uses nothing of.
        case(
            "cite a let line only for the membership it says once",
            "proofs/wiedijk/sum-formula/sum-formula",
            "proofs/wiedijk/sum-formula.proof",
            "    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra\n",
            "    1.6.  k(k + 1)/2 + (k + 1) = (k + 1)((k + 1) + 1)/2\n          algebra, from K\n",
            "step 1.6 cites K and uses nothing it says",
        ),
        // What one case shows is no line of the next, which the build says
        // before the kernel would refuse what it makes.
        case(
            "cite a step of an earlier case",
            "tests/elaborator/textbook-exercise-shapes-two/a-contradiction-ending-in-cases",
            "tests/elaborator/textbook-exercise-shapes-two.proof",
            "                  inequalities, from C2\n",
            "                  inequalities, from 1.1.1\n",
            "step 1.1.2 cites line 1.1.1, which is in another part of the block",
        ),
        // 2·√a is a number once √a is, so it is √a whose membership is owed.
        case(
            "leave out the line saying a root is real from a bound on its multiple",
            "tests/elaborator/textbook-exercise-shapes-two/a-root-in-a-bound",
            "tests/elaborator/textbook-exercise-shapes-two.proof",
            "    inequalities, from H3, 1\n",
            "    inequalities, from H3\n",
            "nothing says √a ∈ ℝ, which this step needs",
        ),
        // A requires line's `from` names the lines it rests on, as a step's
        // does: d(k) ∈ ℝ rests on H2, d's type, with k's membership said once.
        case(
            "a requires line from a function's type naming the let of its point",
            "proofs/wiedijk/divisibility-by-three/divisibility-by-three",
            "proofs/wiedijk/divisibility-by-three.proof",
            "          algebra\n          requires d(k) ∈ ℝ: from H2\n",
            "          algebra\n          requires d(k) ∈ ℝ: from H2, K\n",
            "from H2, K cites K and uses nothing it says, for d(k) ∈ ℝ",
        ),
        // A power to a letter is no membership said once, though 10 and k
        // are: the step writes 10^k ∈ ℝ where it combines it, and an atom
        // whose membership is neither said once nor on the page is reported.
        case(
            "leave out the membership of a power to a letter the method combines",
            "proofs/wiedijk/divisibility-by-three/divisibility-by-three",
            "proofs/wiedijk/divisibility-by-three.proof",
            "          requires d(k) ∈ ℝ: from H2\n          requires 10^k ∈ ℝ: mun:power-real a := 10, m := k\n",
            "          requires d(k) ∈ ℝ: from H2\n",
            "step 1.4 combines 10^k, and nothing it writes or cites says it is a number",
        ),
        // What an obtain claims is the "there is" it obtains from: d > 2 is
        // not what the supposition gives, and the line is the page's claim,
        // never the existence's body in its place.
        case(
            "an obtain claiming more than the line it obtains from",
            "proofs/wiedijk/sqrt2-irrational/lowest-terms",
            "proofs/wiedijk/sqrt2-irrational.proof",
            "    3.1.  d ∈ ℤ. d > 1. d divides p. d divides q.",
            "    3.1.  d ∈ ℤ. d > 2. d divides p. d divides q.",
            "step 3.1 claims",
        ),
        case(
            "an obtain claiming more than the item it obtains from",
            "proofs/wiedijk/bezout/bezout",
            "proofs/wiedijk/bezout.proof",
            "4.  d ∈ S. For all s ∈ S, d ≤ s.",
            "4.  d ∈ S. For all s ∈ S, d < s.",
            "step 4 claims",
        ),
        case(
            "an obtain whose membership is not the one its there is gives",
            "proofs/wiedijk/harmonic/harmonic",
            "proofs/wiedijk/harmonic.proof",
            "    2.2.  B ∈ ℝ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.",
            "    2.2.  B ∈ ℚ. For all m ∈ ℕ, Σ(k = 1 to m) 1/k ≤ B.",
            "step 2.2 claims B ∈ ℚ",
        ),
        case(
            "an obtain from a line that says no there is",
            "proofs/wiedijk/pythagorean-triples/pythagorean-triples",
            "proofs/wiedijk/pythagorean-triples.proof",
            "          obtain k, m, n from D2",
            "          obtain k, m, n from H1",
            "step 1.2 obtains k, m, n from",
        ),
        // Dropping the 1 a substitution makes asks that what is left be a
        // number, and b(0) is one only by the line saying so.
        case(
            "drop an identity element a substitution makes from a value no line says is a number",
            "tests/elaborator/an-identity-a-substitution-makes/an-identity-a-substitution-makes-at-a-value",
            "tests/elaborator/an-identity-a-substitution-makes.proof",
            "    substitute 1^k = 1 (H3)\n    requires b(0) ∈ ℝ: from H1\n",
            "    substitute 1^k = 1 (H3)\n",
            "step 1 drops an identity element from what the substitution makes, and nothing says b(0) is a number; a requires line says it",
        ),
        case(
            "a link dropping an identity element from what no line says is a number",
            "tests/elaborator/an-identity-a-link-drops/an-identity-a-link-drops",
            "tests/elaborator/an-identity-a-link-drops.proof",
            "    requires C(N, k) ∈ ℕ₀: mun:binomial-nat0\n",
            "",
            "a link of step 1 drops an identity element from C(N, k), which nothing the step names says is a number; a requires line of the step says it",
        ),
        // A divisor that nothing says is not zero is named as the page
        // writes it.
        case(
            "leave out that a power to a letter is not zero",
            "tests/elaborator/a-power-said-not-zero/a-power-said-not-zero",
            "tests/elaborator/a-power-said-not-zero.proof",
            "    requires 2^n ≠ 0: weakening, from H3\n",
            "",
            "nothing says 2^n ≠ 0, which this step needs to divide by it",
        )
        .at("tests/elaborator/a-power-said-not-zero.proof", "−1/2^n > −ε"),
        // A number the step needs is named in ℝ or ℂ, either of which says
        // it: a root's record gives √A ∈ ℝ and never √A ∈ ℂ.
        case(
            "leave out that a root an order cites through an equation is real",
            "tests/elaborator/a-root-said-real/a-root-said-real",
            "tests/elaborator/a-root-said-real.proof",
            "    requires √A ∈ ℝ: mun:sqrt x := A, from H2\n",
            "",
            "nothing says √A ∈ ℝ, which this step needs",
        )
        .at("tests/elaborator/a-root-said-real.proof", "transitivity, from 1, 2"),
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
        // A quotient is a number once its divisor is not zero, and that is
        // what is named where it is missing.
        case(
            "leave out that a quotient's divisor is not zero",
            "tests/elaborator/a-quotient-divisor-said-not-zero/a-quotient-divisor-said-not-zero",
            "tests/elaborator/a-quotient-divisor-said-not-zero.proof",
            "    requires 2·d ≠ 0: from 1\n",
            "",
            "nothing says d ≠ 0, which this step needs to divide by it",
        )
        .at("tests/elaborator/a-quotient-divisor-said-not-zero.proof", "0 − ε/(2·d) < 0        multiplying"),
        // The build reads a justification only in a form the grammar gives
        // it, and refuses one in none in the checker's words.
        case(
            "a line number after into without the word line",
            "tests/elaborator/induction-under-a-condition/walk-parity-by-induction",
            "tests/elaborator/induction-under-a-condition.proof",
            "(line 1.2.7) into line 1.2.6",
            "(line 1.2.7) into 1.2.6",
            "a line number after `into` carries the word \"line\": `into line 1.2.6`",
        ),
        // The build reads a file the checker may have refused, so an item
        // the file does not import is reported where it is cited.
        case(
            "cite an item the file does not import",
            "proofs/wiedijk/harmonic/harmonic-block",
            "proofs/wiedijk/harmonic.proof",
            "import mundane theorem    stdlib/sums/sum-real\n",
            "",
            "mun:sum-real is neither imported nor a theorem of this file",
        ),
    ]
}
