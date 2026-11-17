//! Part 1 of 6 of the planted cases, in the order they are run.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
        // A step's proof rests only on what it names (`GOALS.md` decision 9).
        // Without its requires line, the calculation combines s(n), and the
        // scope holds s(n) ∈ ℝ from line 2, which step 3.23 does not cite. A
        // value of a defined sequence is not a membership said once, so only
        // a line can give it.
        case(
            "lean on a line the step does not name",
            vec![edit(
                "proofs/wiedijk/liouville-number.proof",
                Some("                                  = 2/2^A − 2/2^(A + (j + 1))               algebra, from 3.19\n          requires s(n) ∈ ℝ: from 2\n".to_string()),
                "                                  = 2/2^A − 2/2^(A + (j + 1))               algebra, from 3.19\n".to_string(),
            )],
            "proofs/wiedijk/liouville-number.proof:202  nothing says s(n) ∈ ℝ or ∈ ℂ, which this step needs",
        ),
        // A line marked impossible is reached by its reasons from the lines
        // they cite (`SYNTAX.md`, contradiction); `arithmetic` as its reason
        // cites nothing and proves only what is true, and the step is told
        // so rather than only that its claim is false.
        case(
            "give a line marked impossible arithmetic as its reason",
            vec![edit(
                "proofs/wiedijk/impossible-by-arithmetic.proof",
                None,
                "theorem impossible-by-arithmetic\n  let a ∈ ℝ                                                           (H1)\n  assume a > 0                                                        (H2)\n  then a ≠ 0\n\n1.  a ≠ 0\n    contradiction\n    suppose a = 0                                                     (S)\n\n    1.1.  0 > 0\n          substitute a = 0 (S) into H2\n\n    1.2.  0 > 0, which is impossible\n          arithmetic\n".to_string(),
            )],
            "proofs/wiedijk/impossible-by-arithmetic.proof:14  step 1.2 is marked impossible and gives arithmetic as its reason, which proves only what is true; a line marked impossible is reached by its reasons from the lines they cite",
        ),
        // A row's atoms are real numbers (`METHODS.md`, Rows), and a point
        // is none, which no line can say: the step is told it treats the
        // point as a number, not that nothing says it is one.
        case(
            "turn a disequality of points round in an inequalities row",
            vec![edit(
                "proofs/wiedijk/point-row.proof",
                None,
                "theorem point-row\n  let A be a point                                                    (H1)\n  let C be a point                                                    (H2)\n  assume C ≠ A                                                        (H3)\n  then A ≠ C\n\n1.  A ≠ C\n    inequalities\n      C ≠ A            H3\n      A ≠ C            restate\n".to_string(),
            )],
            "proofs/wiedijk/point-row.proof:10  this step treats A as a number, and it is a point",
        ),
        // A requires line's reason shows its fact as a step's reason shows
        // its claim, so a method that does not decide the fact is refused
        // there as it is for a step: `algebra` decides equations, and a
        // membership is `membership`'s.
        case(
            "give a requires line's membership a method that does not decide it",
            vec![edit(
                "proofs/setmm/square-root-positive.proof",
                Some("inequalities, from S\n          requires √a ∈ ℝ: from 1".to_string()),
                "inequalities, from S\n          requires √a ∈ ℝ: algebra".to_string(),
            )],
            "the requires line √a ∈ ℝ of step 2.1 names algebra, which does not decide what it says",
        ),
        // A letter of a range not starting at 1 or 0 is said once to be an
        // integer, and its being no zero is not: a divisor's `≠ 0` is written
        // where the page does not say once it is a positive integer.
        case(
            "leave out a divisor's ≠ 0 built from a letter said once",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("          requires k ≠ 0: weakening, from 10.2\n".to_string()),
                String::new(),
            )],
            "1/k ∈ ℝ is not built from what step 10.3 cites: nothing says k ≠ 0, which it needs to divide by it",
        ),
        // Where the proof has no letter of the subject's name in scope, the
        // pair is the only thing that says what the definition is about:
        // even-leg has no d, and its step claims an impossible fold.
        case(
            "leave out a definition's subject where the proof has no such letter",
            vec![edit(
                "proofs/wiedijk/pythagorean-triples.proof",
                Some("def:divides d := 4, n := 2, from 2.2.9".to_string()),
                "def:divides n := 2, from 2.2.9".to_string(),
            )],
            "def:divides is about d, and the step gives d no value and the proof has no d; write it, as d := t",
        ),
        // A step citing a theorem of its own file reads the defines that
        // theorem is stated over, those above it, and no other: D2 is
        // written below `above`, so `below` claims R(k) = k + 1 of a theorem
        // that says nothing of R, and does not cite D2.
        case(
            "read a define written below the theorem of the file a step cites",
            vec![edit(
                "proofs/wiedijk/stated-over.proof",
                None,
                "define S(k) := k + 1, for k ∈ ℕ                                      (D1)\n       reads one more than k\n\ntheorem above\n  let k ∈ ℕ                                                           (H1)\n  then S(k) = k + 1\n\n1.  S(k) = k + 1\n    D1\n\ndefine R(k) := k + 1, for k ∈ ℕ                                      (D2)\n       reads also one more than k\n\ntheorem below\n  let k ∈ ℕ                                                           (H1)\n  then R(k) = k + 1\n\n1.  R(k) = k + 1\n    thm:above\n".to_string(),
            )],
            "proofs/wiedijk/stated-over.proof:19  step 1 claims something that thm:above does not conclude",
        ),
        // abs asks that x be real, at x := ⌊A + 1/2⌋ − A. A line saying the
        // floor is an integer would make the difference a number, as what
        // − builds from a part a line states is; citing neither that line
        // nor the difference's own, the step has nothing to build it from.
        case(
            "a hypothesis about a term whose parts no line the step names states",
            vec![edit(
                "tests/elaborator/floor-in-a-bound.proof",
                Some("    def:abs x := ⌊A + 1/2⌋ − A, from H2, 2\n".to_string()),
                "    def:abs x := ⌊A + 1/2⌋ − A, from H2\n".to_string(),
            )],
            "step 3 cites def:abs, which asks for ⌊A + 1 / 2⌋ − A ∈ ℝ, and what it cites does not supply it",
        ),
        // A sum of squares of reals is not shown to be a natural number by
        // the let's reason. The checker does not judge a let's kind against
        // its reason; it reports what the planted kind makes surplus below.
        case(
            "a let saying a kind of number its reason does not show",
            vec![edit(
                "proofs/wiedijk/cauchy-schwarz.proof",
                Some("    let A = Σ(k = 1 to n) a(k)², a real number                        (D1)".to_string()),
                "    let A = Σ(k = 1 to n) a(k)², a natural number                     (D1)".to_string(),
            )],
            "the requires line of step 5.10 says A > 0, which the step's other lines already say",
        ),
        // A false divisibility of numerals, on a requires line: the checker
        // works it out as `arithmetic` does (`check_arithmetic_holds`).
        case(
            "a divisibility of numerals that does not hold",
            vec![edit(
                "proofs/wiedijk/divisibility-by-three.proof",
                Some("                       ≡ 1 (mod 3)        arithmetic\n".to_string()),
                "                       ≡ 1 (mod 3)        arithmetic\n          requires 3 divides 10 − 2: arithmetic\n".to_string(),
            )],
            "the requires line 3 divides 10 − 2 of step 1.3 is arithmetic, which is false",
        ),
        // An odd number is an integer, so arithmetic finds a half not odd
        // though it does not say whether 2 divides it.
        case(
            "say a half is odd",
            vec![edit(
                "tests/elaborator/a-half-odd.proof",
                None,
                "theorem a-half-odd\n  then 1/2 is odd\n\n1.  1/2 is odd\n    arithmetic\n".to_string(),
            )],
            "step 1 claims 1/2 is odd, which is false",
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
        // A membership step builds a typed value from the type it cites,
        // never one merely in scope: H1 types d, and with 16.22 left out the
        // line names nothing saying d(n) is a number.
        case(
            "a membership of a typed value citing nothing",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("                    requires d(n) ∈ ℝ: membership, from 16.21\n\n           16.24.4.".to_string()),
                "                    requires d(n) ∈ ℝ: membership\n\n           16.24.4.".to_string(),
            )],
            "d(n) ∈ ℝ is not built from what step 16.24.3 cites: nothing says d(n) ∈ ℝ, which it needs",
        ),
        // Every atom an inequalities step combines is a real number by a
        // line it names: L(p) is, by line 5.2.3, which lines 5.2.1 and
        // 5.2.4 do not say.
        case(
            "an inequalities step combining an atom it names nothing real of",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    5.7.  L(p) ≤ L(p + g)\n          inequalities, from 5.2, 5.4, 5.5\n".to_string()),
                "    5.7.  L(p) ≤ L(p + g)\n          inequalities, from 5.2, 5.5\n".to_string(),
            )],
            "nothing says L(p) ∈ ℝ, which this step needs",
        ),
        // An inequalities step's rows: the cited line written out, then the
        // row above with the manipulation each reason names, the last the
        // claim.
        case(
            "an inequality row with no reason",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      2·A < A + B          algebra\n".to_string()),
                "      2·A < A + B          because\n".to_string(),
            )],
            "a row gives no reason",
        ),
        case(
            "an inequality row that is no single relation",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      x = y                restate\n".to_string()),
                "      x = y and y = x      restate\n".to_string(),
            )],
            "a row of step 1 is no single relation of =, ≠, <, ≤, > or ≥",
        ),
        // `symmetry` is kept back for later: a row turning a relation round
        // says `restate`.
        case(
            "turn an inequality row round with symmetry",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      x = y                restate\n".to_string()),
                "      x = y                symmetry\n".to_string(),
            )],
            "`symmetry` is kept back for later; a row turning a relation round is `restate`",
        ),
        case(
            "inequality rows starting from no cited line",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      A < B                H3\n".to_string()),
                "      A < B                H2\n".to_string(),
            )],
            "the first row of step 1 is not a line the step cites, written out with its label as its reason",
        ),
        case(
            "an inequality row that is not the manipulation it names",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      2·A < A + B          algebra\n".to_string()),
                "      3·A < A + B          algebra\n".to_string(),
            )],
            "a row of step 1 is not the row above with a side written as the same number another way",
        ),
        case(
            "inequality rows ending other than on the claim",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      0 < x                H2\n      0 ≠ x                weakening\n      x ≠ 0                restate\n".to_string()),
                "      0 < x                H2\n      0 ≤ x                weakening\n".to_string(),
            )],
            "the last row of step 1 is not its claim",
        ),
        // A join takes what the lines write, and nothing else a line says
        // (`SYNTAX.md`, What a cited line says): not a chain's other
        // equations, a range's bound or what a membership implies. A
        // define it cites reads a name as what it names, and one whose name
        // no sentence needs read is a line the join does not use.
        case(
            "restate citing a define no sentence needs read",
            vec![edit(
                "tests/elaborator/reading-defines.proof",
                Some("theorem a-define-read-in-a-case-split\n".to_string()),
                "theorem an-unneeded-define-in-a-join\n  let a ∈ ℝ    (H1)\n  assume a + 1 > 0    (H2)\n  then a + 1 > 0\n\nlet e = a + 1, a real number    (D1)\n    membership\n    reads one more than a\n\n1.  a + 1 > 0\n    restate D1, H2\n\ntheorem a-define-read-in-a-case-split\n".to_string(),
            )],
            "step 1 restates D1, and claims nothing it says",
        ),
        case(
            "restate an equation of a chain its neighbours do not write",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-substituted\n".to_string()),
                "theorem a-chain-pair-joined\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b = c    (H4)\n  then a = c\n\n1.  a = c\n    restate H4\n\ntheorem a-chain-pair-substituted\n".to_string(),
            )],
            "step 1 restates H4 and claims a = c, which no line it restates says",
        ),
        case(
            "restate a bound a range line says without writing it",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-range-bound-joined\n  let n ∈ ℤ    (H1)\n  let k ∈ {1, …, n}    (H2)\n  then k ≤ n\n\n1.  k ≤ n\n    restate H2\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H2 and claims k ≤ n, which no line it restates says",
        ),
        case(
            "restate a bound a membership implies",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-membership-bound-joined\n  let k ∈ ℕ    (H1)\n  then k ≥ 1\n\n1.  k ≥ 1\n    restate H1\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H1 and claims k ≥ 1, which no line it restates says",
        ),
        case(
            "restate the members a subset line says without writing them",
            vec![edit(
                "tests/elaborator/reading-memberships.proof",
                Some("theorem a-range-bound-in-a-requires-line\n".to_string()),
                "theorem a-subset-joined-as-its-members\n  let X ⊆ ℤ    (H1)\n  then for all x ∈ X, x ∈ ℤ\n\n1.  For all x ∈ X, x ∈ ℤ.\n    restate H1\n\ntheorem a-range-bound-in-a-requires-line\n".to_string(),
            )],
            "step 1 restates H1 and claims",
        ),
        // A calculation claims its first term by the chain's relation to
        // its last: a chain with a `>` link claims `>`.
        case(
            "a calculation claiming a weaker relation than its chain gives",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-weaker-calculation-claim\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b    (H4)\n  assume b > c    (H5)\n  then a ≥ c\n\n1.  a ≥ c\n    calculation\n      a = b    H4\n        > c    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a ≥ c, and its chain gives a > c",
        ),
        case(
            "a calculation claiming other than its chain's ends",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-calculation-claiming-other-ends\n  let a ∈ ℝ    (H1)\n  let b ∈ ℝ    (H2)\n  let c ∈ ℝ    (H3)\n  assume a = b    (H4)\n  assume b > c    (H5)\n  then a > b\n\n1.  a > b\n    calculation\n      a = b    H4\n        > c    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a > b, and its chain gives a > c",
        ),
        case(
            "a calculation claiming a congruence modulo another number",
            vec![edit(
                "tests/elaborator/reading-equations.proof",
                Some("theorem a-chain-pair-in-a-calculation-link\n".to_string()),
                "theorem a-congruence-claimed-modulo-another\n  let a ∈ ℤ    (H1)\n  let b ∈ ℤ    (H2)\n  let c ∈ ℤ    (H3)\n  assume a = b    (H4)\n  assume b ≡ c (mod 3)    (H5)\n  then a ≡ c (mod 6)\n\n1.  a ≡ c (mod 6)\n    calculation\n      a = b    H4\n        ≡ c (mod 3)    H5\n\ntheorem a-chain-pair-in-a-calculation-link\n".to_string(),
            )],
            "step 1 claims a ≡ c (mod 6), and its chain gives a ≡ c (mod 3)",
        ),
        // A line saying several relations gives a chain the one that makes
        // a chain to the claim, and one saying two that both do gives the
        // chain nothing.
        case(
            "chain a line two of whose relations both reach the claim",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume 0 < a and a ≤ b    (H4)\n".to_string()),
                "  assume a < b and a ≤ b    (H4)\n".to_string(),
            )],
            "step 1 cites lines by transitivity that say several relations, and more than one choice of them reaches the claim",
        ),
        // A requires line naming a manipulation is its one line with it: q >
        // 0 weakened is q ≠ 0, and no weakening of it is q ≠ 1.
        case(
            "a requires line naming a manipulation its line does not take",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("    requires q ≠ 0: weakening, from H3\n".to_string()),
                "    requires q ≠ 1: weakening, from H3\n".to_string(),
            )],
            "the requires line q ≠ 1 of step 1 is not H3 with its relation weakened",
        ),
        // In rows, turning a relation round is a restate row of its own: the
        // first row is the cited line as written, each row keeps its sides
        // where its manipulation leaves them, and the last row is the claim
        // as written. A row that turns as well as manipulates is told which.
        case(
            "write the first row as the line it cites turned round",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      A < B                H3\n".to_string()),
                "      B > A                H3\n".to_string(),
            )],
            "the first row of step 1 is the line it cites turned round; write the line as it is written, and turn it with a restate row",
        ),
        case(
            "turn a row round as well as multiplying it",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      −x > 0               multiplying by −1\n      0 < −x               restate\n".to_string()),
                "      0 < −x               multiplying by −1\n".to_string(),
            )],
            "a row of step 1 is the row above with both sides multiplied by −1, a numeral other than 0, turned round; turning it round is a restate row of its own",
        ),
        case(
            "end the rows on the claim turned round",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("      0 ≠ x                weakening\n      x ≠ 0                restate\n".to_string()),
                "      0 ≠ x                weakening\n".to_string(),
            )],
            "the last row of step 1 is its claim turned round; end with a restate row that writes the claim as it is written",
        ),
        case(
            "turn a requires line round as well as weakening it",
            vec![edit(
                "tests/elaborator/inequality-rows.proof",
                Some("    requires 0 ≠ q: weakening, from H3\n".to_string()),
                "    requires q ≠ 0: weakening, from H3\n".to_string(),
            )],
            "the requires line q ≠ 0 of step 2 is H3 with its relation weakened, turned round; a requires line names one manipulation, so write it as the manipulation leaves it: 0 ≠ q",
        ),
        // A requires line by a manipulation takes an atom's membership from
        // a requires line above it; with none it is told so, and with one
        // below it is told to move that one above.
        case(
            "leave out the membership a requires-line weakening needs",
            vec![edit(
                "tests/elaborator/a-requires-weakening-with-its-membership.proof",
                Some("    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string()),
                "    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string(),
            )],
            "nothing says √(x + 1) ∈ ℝ, which this step needs; a requires line by weakening takes a membership from a requires line above it",
        ),
        case(
            "write the membership a requires-line weakening needs below it",
            vec![edit(
                "tests/elaborator/a-requires-weakening-with-its-membership.proof",
                Some("    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n    requires √(x + 1) + √x ≠ 0: weakening, from 8\n".to_string()),
                "    requires √(x + 1) + √x ≠ 0: weakening, from 8\n    requires √(x + 1) ∈ ℝ: from 2\n    requires √x ∈ ℝ: from 3\n".to_string(),
            )],
            "nothing above says √(x + 1) ∈ ℝ, which this step needs; the requires line √(x + 1) ∈ ℝ below says it, and a requires line takes only what the lines above it state: move it above",
        ),
        // A transitivity step chains relations, each line's right side the
        // next one's left, and claims the ends by the chain's relation;
        // antisymmetry takes an order and its converse to an equation.
        case(
            "transitivity citing a line that is no relation",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("    transitivity, from H4, H5\n".to_string()),
                "    transitivity, from H1, H5\n".to_string(),
            )],
            "step 1 cites H1 by transitivity, and H1 states no relation of =, <, ≤, > or ≥",
        ),
        case(
            "transitivity chaining orders going both ways",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume b ≥ a    (H5)\n".to_string()),
                "  assume b ≤ a    (H5)\n".to_string(),
            )],
            "step 1 chains orders going up and going down, which say nothing of its ends",
        ),
        case(
            "transitivity over lines that do not meet",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume b < c    (H5)\n".to_string()),
                "  assume c < c + 1    (H5)\n".to_string(),
            )],
            "the lines step 1 chains do not meet: H4 ends at b, and H5 starts from c",
        ),
        case(
            "transitivity claiming other than the chain's ends",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("1.  a < c\n    transitivity, from H4, H5\n".to_string()),
                "1.  a ≤ c\n    transitivity, from H4, H5\n".to_string(),
            )],
            "step 1 claims a ≤ c, and the chain it cites gives a < c",
        ),
        case(
            "antisymmetry of a strict order",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("  assume a ≥ b    (H4)\n".to_string()),
                "  assume a > b    (H4)\n".to_string(),
            )],
            "step 1 cites by antisymmetry what is not two lines a ≤ b and b ≤ a, an order and its converse",
        ),
        case(
            "antisymmetry claiming other than the equation of its sides",
            vec![edit(
                "tests/elaborator/transitivity.proof",
                Some("1.  b = a\n    antisymmetry".to_string()),
                "1.  b = b\n    antisymmetry".to_string(),
            )],
            "step 1 claims b = b, and its lines give a = b",
        ),
        // An induction over ℕ starts at 1 and writes it, runs over ℕ or ℕ₀,
        // and has a base part and a step part.
        case(
            "an induction starting where its set does not",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("    induction on k starting at 1\n".to_string()),
                "    induction on k starting at 2\n".to_string(),
            )],
            "an induction over ℕ starts at 1, and the text says 2",
        ),
        case(
            "an induction over a set no induction runs over",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("1.  For all k ∈ ℕ, S(k) = k(k + 1)/2.\n".to_string()),
                "1.  For all k ∈ ℤ, S(k) = k(k + 1)/2.\n".to_string(),
            )],
            "step 1 is an induction over ℤ, and an induction runs over ℕ from 1 or ℕ₀ from 0",
        ),
        case(
            "an induction on a letter the theorem already introduces",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("(H1)\n  then ".to_string()),
                "(H1)\n  let k ∈ ℕ (H2)\n  then ".to_string(),
            )],
            "step 1 is an induction on k, and k is a letter already introduced here; an induction runs over a letter of its own",
        ),
        case(
            "an induction with no base part",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("    induction on k starting at 1\n\n    base\n".to_string()),
                "    induction on k starting at 1\n\n    step\n".to_string(),
            )],
            "step 1 is an induction with no base part",
        ),
        // A proof block's let line takes a "for all" off its claim, and an
        // assume line an "if": step 2's claim has neither once it is cut down.
        case(
            "a proof block fixing a name its claim says nothing of every such",
            vec![edit(
                "proofs/wiedijk/rationals-countable.proof",
                Some("2.  For all m, n ∈ ℕ, if f(m) = f(n) then m = n.".to_string()),
                "2.  If f(m) = f(n) then m = n.".to_string(),
            )],
            "step 2 opens a proof block with a let line, and its claim says nothing of every such name",
        ),
        case(
            "a proof block assuming where its claim supposes nothing",
            vec![edit(
                "proofs/wiedijk/rationals-countable.proof",
                Some("2.  For all m, n ∈ ℕ, if f(m) = f(n) then m = n.".to_string()),
                "2.  For all m, n ∈ ℕ, m = n.".to_string(),
            )],
            "step 2 opens a proof block with an assume line, and its claim supposes nothing there",
        ),
        // A requires line of a closure step says a membership of a term the
        // step combines: step 17 combines no power of 3.
        case(
            "a requires line of an inequalities step about a term it never combines",
            vec![edit(
                "proofs/wiedijk/harmonic.proof",
                Some("    requires Σ(k = 2^j + 1 to 2^(j + 1)) 1/k ∈ ℝ: mun:sum-real a := 2^j + 1, b := 2^(j + 1)\n\n18.".to_string()),
                "    requires Σ(k = 2^j + 1 to 2^(j + 1)) 1/k ∈ ℝ: mun:sum-real a := 2^j + 1, b := 2^(j + 1)\n    requires 3^j ∈ ℝ: membership\n\n18.".to_string(),
            )],
            "says 3^j ∈ ℝ, and the step neither uses nor asks for it",
        ),
        // A library function an item applies is no letter of the item's:
        // lowest-terms-parts says denom(x) ∈ ℕ, which is not numer(x) ∈ ℕ.
        case(
            "a requires line narrowing what a record says of a library function",
            vec![edit(
                "proofs/wiedijk/rationals-countable.proof",
                Some("    membership, from D3\n    requires numer(x) ∈ ℤ: mun:lowest-terms-parts\n".to_string()),
                "    membership, from D3\n    requires numer(x) ∈ ℕ: mun:lowest-terms-parts\n".to_string(),
            )],
            "the requires line of step 6 needs something that mun:lowest-terms-parts does not conclude",
        ),
        // A calculation's row citing a define is what the define makes its
        // name: D1 makes G(a, 0) the sum to 0, and G(a, 1) the sum to 1.
        case(
            "a calculation row citing a define for what it does not make",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("            G(a, 0) = ".to_string()),
                "            G(a, 1) = ".to_string(),
            )],
            "a^j is not what D1 makes it",
        ),
        // What a line says at the values may be an implication, whose
        // condition a line the step cites meets: line 13 asks that U(k) be
        // an upper bound of S, which line 10 says at k and 15.1 does not.
        case(
            "instantiate an implication whose condition no cited line meets",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("instantiate u := U(k) in line 13, from 10".to_string()),
                "instantiate u := U(k) in line 13, from 15.1".to_string(),
            )],
            "instantiating at that term wants U(k) is an upper bound of S, which step 15.2 does not supply",
        ),
        // An instantiation claims what its line says at the values: H2 says
        // 0 ≤ d(n) for every n, and so 0 ≤ d(k + 1), not 0 ≥ d(k + 1).
        case(
            "instantiate a line for what it does not say there",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    3.3.  0 ≤ d(k + 1) and d(k + 1) ≤ 9\n          instantiate n := k + 1 in H2, from 3.2\n".to_string()),
                "    3.3.  0 ≥ d(k + 1) and d(k + 1) ≤ 9\n          instantiate n := k + 1 in H2, from 3.2\n".to_string(),
            )],
            "H2 at those terms says 0 ≤ d(k + 1) and d(k + 1) ≤ 9, and the step claims 0 ≥ d(k + 1) and d(k + 1) ≤ 9",
        ),
        // A requires line of `from` alone rests on the lines it names: f(b)
        // is real by f's type H4 and b's place in its domain, and with H4
        // left out nothing it names types f, the type in scope being no
        // line it names.
        case(
            "a from line that leaves out the type its value needs",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some("    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 22\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n".to_string()),
                "    requires f′(c) ∈ ℝ: mun:derivative-real x := c, from H6, 22\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from 3\n".to_string(),
            )],
            "from 3 does not reach f(b) ∈ ℝ, which this line claims it supplies",
        ),
        // A define gives its function on its domain and nothing more: the
        // type p : X → ℝ is a step citing `function-into`, and a requires
        // line naming the define and the values' line in its place is not
        // read as that step.
        case(
            "a function's type from its define and its values, in place of the step proving it",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("mun:sum-termwise a := 0, b := m + 1, t := p, from 17\n    requires p : {0, …, m + 1} → ℝ: from 4\n".to_string()),
                "mun:sum-termwise a := 0, b := m + 1, t := p, from 17\n    requires p : {0, …, m + 1} → ℝ: from D2, 3\n".to_string(),
            )],
            "from D2, 3 does not reach p : {0, …, m + 1} → ℝ, which this line claims it supplies",
        ),
        // A claim the method named does not decide, a membership said by
        // `inequalities`: no closure step is taken without examining it.
        case(
            "rest a claim on a method that does not decide it",
            vec![edit(
                "proofs/hammack/mersenne-prime-exponent.proof",
                Some("    1.13. j ≤ q\n          inequalities, from 1.3\n".to_string()),
                "    1.13. j ∈ ℤ\n          inequalities, from 1.3\n".to_string(),
            )],
            "step 1.13 names inequalities, which does not decide what it claims",
        ),
        // A link of numerals alone naming arithmetic, worked out whole.
        case(
            "a chain link of numerals that is false",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("= 1(1 + 1)/2            arithmetic".to_string()),
                "= 1(1 + 1)/3            arithmetic".to_string(),
            )],
            "a link of step 1.1 names arithmetic for 1 = 1(1 + 1)/3, which is false",
        ),
        // Two pairs are compared coordinate by coordinate (`METHODS.md`,
        // Pairs): equal pairs said to differ are false by arithmetic, a
        // difference by algebra rescales one a step cites, and inspection
        // finds a pair among listed ones by its coordinates.
        // A value runs to the comma that opens the next naming or the
        // `from` list (`GRAMMAR.md`, Justifications), so a naming written
        // without its `:=` is read as more of the value before it, and the
        // message names what was taken into it: here a chain of equations,
        // which stands inside the value's formula.
        case(
            "a naming written without its :=",
            vec![edit(
                "tests/elaborator/a-value-with-a-comma.proof",
                Some("Q := x = 1, from H5, H6".to_string()),
                "Q = x = 1, from H5, H6".to_string(),
            )],
            "a value step 1 gives: the chain of equations Q = x = 1 stands inside another formula, and a chain is a whole sentence",
        ),
        case(
            "claim by arithmetic that a pair differs from itself",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some("  then (1, 1) ≠ (2, 3)\n\n1.  (1, 1) ≠ (2, 3)".to_string()),
                "  then (1, 1) ≠ (1, 1)\n\n1.  (1, 1) ≠ (1, 1)".to_string(),
            )],
            "step 1 claims (1, 1) ≠ (1, 1), which is false",
        ),
        case(
            "claim by algebra that two pairs differ, citing nothing",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some("    algebra, from H5".to_string()),
                "    algebra".to_string(),
            )],
            "(a, b) ≠ (c, d) is not a rescaling of any disequality step 1 cites",
        ),
        case(
            "claim by inspection that a listed pair is not in its list",
            vec![edit(
                "tests/elaborator/pairs-compared.proof",
                Some(
                    "  then (1, 2) ∉ {(3, 4), (1, 5)}\n\n1.  (1, 2) ∉ {(3, 4), (1, 5)}"
                        .to_string(),
                ),
                "  then (1, 5) ∉ {(3, 4), (1, 5)}\n\n1.  (1, 5) ∉ {(3, 4), (1, 5)}"
                    .to_string(),
            )],
            "step 1 claims (1, 5) ∉ {(3, 4), (1, 5)}, which inspection of what it cites shows false",
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
                "proofs/wiedijk/konigsberg.proof",
                Some("6.  |{x ∈ V : deg(x) is odd}| = 4".to_string()),
                "6.  |{x ∈ V : deg(x) is odd}| = 3".to_string(),
            )],
            "step 6 claims |{x ∈ V : deg(x) is odd}| = 3, which inspection of what it cites shows false",
        ),
        // A line of "or"s read from a membership has an equation for each
        // element of the set and for nothing else, and a range is read as
        // a list only up to its cap.
        case(
            "a line of ors by inspection that leaves out an element of the range",
            vec![
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("  then k = 4 or k = 0 or 2 = k or k = 1 or k = 1 + 2\n".to_string()),
                    "  then k = 4 or k = 0 or 2 = k or k = 1 + 2\n".to_string(),
                ),
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("1.  k = 4 or k = 0 or 2 = k or k = 1 or k = 1 + 2\n".to_string()),
                    "1.  k = 4 or k = 0 or 2 = k or k = 1 + 2\n".to_string(),
                ),
            ],
            "and the claim leaves out 1, an element of the set the cited membership names",
        ),
        case(
            "a line of ors by inspection that names something the range does not list",
            vec![
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("  then x = 1 or x = 2\n".to_string()),
                    "  then x = 1 or x = 2 or x = 3\n".to_string(),
                ),
                edit(
                    "tests/elaborator/inspection-cases-of-a-range.proof",
                    Some("1.  x = 1 or x = 2\n".to_string()),
                    "1.  x = 1 or x = 2 or x = 3\n".to_string(),
                ),
            ],
            "and 3 is not an element of the set the cited membership names",
        ),
        case(
            "a line of ors by inspection from a range past the cap",
            vec![edit(
                "tests/elaborator/inspection-cases-of-a-range.proof",
                Some("  let x ∈ {1, …, 2}".to_string()),
                "  let x ∈ {1, …, 100}".to_string(),
            )],
            "and inspection lists a range of at most 64 numerals, and the one from 1 to 100 holds 100",
        ),
        // One equation is a line of one, read against a listed set as a
        // line of "or"s is: from x ∈ {3, 4} it leaves out 4.
        case(
            "one equation by inspection from a set of two",
            vec![edit(
                "tests/elaborator/inspection-cases-of-a-range.proof",
                Some("  let x ∈ {3}".to_string()),
                "  let x ∈ {3, 4}".to_string(),
            )],
            "and the claim leaves out 4, an element of the set the cited membership names",
        ),
        // `substitute` walks its equation both ways and each sentence of the
        // line it names, trying the next where one declines. A name the proof
        // never introduced is not one of those: it is a defect.
        case(
            "substitute a name the proof never introduced",
            vec![edit(
                "proofs/wiedijk/pythagorean-triples.proof",
                Some("                  substitute c = 2r (line 2.2.7) into line 2.2.3".to_string()),
                "                  substitute c = z (line 2.2.7) into line 2.2.3".to_string(),
            )],
            "step 2.2.8 takes c = z from 2.2.7, which does not say it",
        ),
        // A step claims of a definition something it does not say.
        case(
            "claim of a definition what it does not say",
            vec![edit(
                "proofs/wiedijk/triangle-inequality.proof",
                Some("    2.6.  |x| = −x".to_string()),
                "    2.6.  |x| = x".to_string(),
            )],
            "step 2.6 claims something that def:abs does not conclude",
        ),
        // A base may be written without an identity element its instance
        // has, and nothing else: G(a, 0) = 1 is no instance of
        // G(a, 0) = (1 − a^(0 + 1))/(1 − a) however its elements are read.
        case(
            "end an induction's base on what is not its instance",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("    1.2.  G(a, 0) = (1 − a)/(1 − a)\n          calculation\n            G(a, 0) = 1                    1.1\n                    = (1 − a)/(1 − a)      algebra\n          requires 1 − a ≠ 0: algebra, from H2\n\n".to_string()),
                "".to_string(),
            )],
            "step 1.1 ends the base part of step 1, which owes G(a, 0) = (1 − a^(0 + 1)) / (1 − a)",
        ),
        // A conclusion is matched with an identity element dropped where the
        // instance has one, and with nothing else changed: the shifted sum
        // starts at 0 + 1, which is 1 and not 2.
        case(
            "claim a lemma's conclusion with more than an identity element dropped",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("= Σ(k = 1 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string()),
                "= Σ(k = 2 to m + 1) C(m, k − 1)·x^(m − (k − 1))·y^((k − 1) + 1)        mun:sum-shift".to_string(),
            )],
            "step 26 claims something that mun:sum-shift does not conclude",
        ),
        // A substitution's line may leave out the + 0 it makes, and nothing
        // else: the product written the other way round is a reordering, which
        // no identity law gives.
        case(
            "a substitution that reorders where it drops a 0",
            vec![edit(
                "proofs/wiedijk/factor.proof",
                Some("    2.1.  p(x) = (x − a)·q(x)\n".to_string()),
                "    2.1.  p(x) = q(x)·(x − a)\n".to_string(),
            )],
            "step 2.1 claims p(x) = q(x) · (x − a), which putting one side of p(a) = 0 for the other does not make",
        ),
        // 0 is an identity on the right of a difference and not on its left:
        // C(m, 0 − 1) is not C(m, −1) by any identity law.
        case(
            "drop a 0 from the side of a difference where it is no identity",
            vec![edit(
                "proofs/wiedijk/binomial.proof",
                Some("= C(m, 0 − 1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string()),
                "= C(m, −1)·x^(m + 1)·y^0 + Σ(k = 1 to m + 1)".to_string(),
            )],
            "step 23 claims something that mun:sum-first does not conclude",
        ),
        // A `requires` line has a claim and a reason, and the reason is what
        // proves it. Here H6 does not say `C ≠ B`, and the step no longer
        // cites H5, which does.
        case(
            "name a line that does not state the side condition",
            vec![
                edit(
                    "proofs/euclid/thales.proof",
                    Some("import theorem            stdlib/geometry/angle-sum\n".to_string()),
                    "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string(),
                ),
                edit(
                    "proofs/euclid/thales.proof",
                    Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()),
                    "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C, from H6\n".to_string(),
                ),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
        ),
        // The same, where the step already holds the claim for another reason:
        // it cites H5, which says A, B, C form a triangle, so `C ≠ B` is held
        // before the line is read, and H6 does not say it.
        case(
            "name a line that does not state a claim the scope already holds",
            vec![
                edit(
                    "proofs/euclid/thales.proof",
                    Some("import theorem            stdlib/geometry/angle-sum\n".to_string()),
                    "import theorem            stdlib/geometry/angle-sum\nimport definition         stdlib/geometry/triangle\n".to_string(),
                ),
                edit(
                    "proofs/euclid/thales.proof",
                    Some("    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n".to_string()),
                    "    mun:angle-along-segment P := A, Q := B, R := C, S := M, from H5, H6, 1\n    requires C ≠ B: def:triangle P := A, Q := B, R := C, from H6\n".to_string(),
                ),
            ],
            "the requires line of step 7 needs something that def:triangle does not conclude",
        ),
        // A requires line below that cites an item asks for that item's
        // hypotheses, and only those: mun:sum-real asks nothing of x^m, and
        // nothing asks x^m ∈ ℝ of a substitution that drops the 0 before the
        // sum. A power to a letter is written where it is needed, so the line
        // is not one the step is spared; it is one nothing needs.
        case(
            "a requires line above an item's line that the item does not ask for",
            vec![
                edit(
                    "proofs/wiedijk/binomial.proof",
                    Some("import mundane theorem    stdlib/numbers/exponent-step\n".to_string()),
                    "import mundane theorem    stdlib/numbers/exponent-step\nimport mundane theorem    stdlib/numbers/power-real\n".to_string(),
                ),
                edit(
                    "proofs/wiedijk/binomial.proof",
                    Some("    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23\n    requires Σ(k = 1 to m + 1)".to_string()),
                    "    substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23\n    requires x^m ∈ ℝ: mun:power-real a := x, m := m, from H1\n    requires Σ(k = 1 to m + 1)".to_string(),
                ),
            ],
            "the requires line of step 24 cites H1, and mun:power-real asks for nothing it says",
        ),
        // A requires line rests only on its reason. Line 2 does not say ⌊A⌋
        // is an integer, and `mun:int-real` asks it; the scope has it from
        // line 1, which the line does not cite, so the item it names reaches
        // nothing.
        case(
            "give a requires line a reason that is not where its proof comes from",
            vec![
                edit(
                    "proofs/setmm/floor-add-integer.proof",
                    Some("import mundane theorem    stdlib/numbers/floor-integer\n".to_string()),
                    "import mundane theorem    stdlib/numbers/floor-integer\nimport mundane theorem    stdlib/numbers/int-real\n".to_string(),
                ),
                edit(
                    "proofs/setmm/floor-add-integer.proof",
                    Some("      ⌊A⌋ + N ≤ A + N          adding N\n    requires ⌊A⌋ ∈ ℝ: from 1\n".to_string()),
                    "      ⌊A⌋ + N ≤ A + N          adding N\n    requires ⌊A⌋ ∈ ℝ: mun:int-real, from 2\n".to_string(),
                ),
            ],
            "the requires line of step 4 cites mun:int-real, which asks for ⌊A⌋ ∈ ℤ, and what it cites does not supply it",
        ),
        // Everything a step names does work. A numeral's membership is said
        // once (`SYNTAX.md`), so the line is true, well formed, and does
        // nothing.
        case(
            "write a requires line nothing asks for",
            vec![edit(
                "proofs/wiedijk/sum-formula.proof",
                Some("= (k + 1)((k + 1) + 1)/2       algebra\n".to_string()),
                "= (k + 1)((k + 1) + 1)/2       algebra\n          requires 2 ∈ ℝ: arithmetic\n".to_string(),
            )],
            "the requires line of step 1.3 says 2 ∈ ℝ, which the page says once",
        ),
        // A distance between two points is real, said once where the points
        // are introduced (`READERS.md`), so a line writing it does nothing.
        case(
            "write a distance's membership",
            vec![edit(
                "proofs/wiedijk/pythagoras.proof",
                Some("    algebra, from 4, 7, 8\n".to_string()),
                "    algebra, from 4, 7, 8\n    requires |AC| ∈ ℝ: membership\n".to_string(),
            )],
            "the requires line of step 9 says |AC| ∈ ℝ, which the page says once",
        ),
        // A chain of equations is a whole sentence (`SYNTAX.md`), never a
        // part of another formula.
        case(
            "a chain of equations inside another formula",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y = z                                                    (H4)\n  then y + 1 = z + 1".to_string()),
                "  assume if x = 1 then x = y = z                                      (H4)\n  then y + 1 = z + 1".to_string(),
            )],
            "the chain of equations x = y = z stands inside another formula, and a chain is a whole sentence",
        ),
        // `join` infers nothing: a chain is the equations between its
        // neighbouring terms, and from x = y and x = z the neighbour y = z
        // is a deduction.
        case(
            "join a chain from equations that are not its links",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y                                                        (H5)\n  assume y = z                                                        (H6)\n  assume z = w                                                        (H7)".to_string()),
                "  assume x = y                                                        (H5)\n  assume x = z                                                        (H6)\n  assume z = w                                                        (H7)".to_string(),
            )],
            "step 1 joins H5, H6, H7 and claims y = z, which no line it joins says",
        ),
        // Only a chain supplies the equation between terms that are not
        // neighbours: two sentences saying x = y and y = z supply those two.
        case(
            "take a pair from two sentences that are not a chain",
            vec![edit(
                "tests/elaborator/chains.proof",
                Some("  assume x = y = z. x + 1 = 5.                                        (H4)".to_string()),
                "  assume x = y. y = z. x + 1 = 5.                                     (H4)".to_string(),
            )],
            "step 1 takes x = z from H4, which does not say it",
        ),
        // A claim of numerals said to be impossible, given to `inequalities`:
        // a claim arithmetic can work out is arithmetic's, and is refused
        // there.
        case(
            "say a true claim is impossible",
            vec![edit(
                "proofs/wiedijk/reals-uncountable.proof",
                Some("    2.2.  10 divides 1, which is impossible\n          substitute\n            10 divides (t + 1) − t      2.1\n            10 divides 1                algebra\n".to_string()),
                "    2.2.  10 divides 1\n          substitute\n            10 divides (t + 1) − t      2.1\n            10 divides 1                algebra\n\n    2.3.  1 ≤ 10, which is impossible\n          inequalities\n".to_string(),
            )],
            "step 2.3 says 1 ≤ 10 is impossible, and it holds",
        ),
        // A claim holding a square root said to be impossible is worked out
        // by `real arithmetic`, which finds this one true.
        case(
            "say a true claim with a root is impossible",
            vec![edit(
                "tests/elaborator/an-impossible-line-by-algebra.proof",
                Some("    1.1.  √2 − 1 = 0, which is impossible\n".to_string()),
                "    1.1.  (√2)² = 2, which is impossible\n".to_string(),
            )],
            "step 1.1 says (√2)² = 2 is impossible, and it holds",
        ),
        // A claim of `algebra` that is not an identity, and one asking a
        // power past what algebra may multiply out: the checker decides
        // algebra (`check_algebra_holds`).
        case(
            "claim an algebra step the cited lines do not give",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("= (1 − a^(k + 1)·a)/(1 − a)                  algebra".to_string()),
                "= (1 − a^(k + 1)·a)/(1 − a) + 1              algebra".to_string(),
            )],
            "(1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a) + 1 is not an identity, nor does it follow from what step 1.5 cites",
        ),
        // A bound the cited lines do not give: q ≥ j says j ≤ q, never
        // j < q (`check_inequalities_holds`).
        case(
            "claim an inequalities step the cited lines do not give",
            vec![edit(
                "proofs/hammack/mersenne-prime-exponent.proof",
                Some("    1.13. j ≤ q\n          inequalities, from 1.3\n".to_string()),
                "    1.13. j < q\n          inequalities, from 1.3\n".to_string(),
            )],
            "j < q does not follow from what step 1.13 cites",
        ),
        case(
            "ask algebra to multiply out a power past its cost",
            vec![edit(
                "proofs/wiedijk/geometric-series.proof",
                Some("= (1 − a^(k + 1)·a)/(1 − a)                  algebra".to_string()),
                "= (1 − a^(k + 1)·a)/(1 − a) + (a + 1)^30 − (a + 1)^30    algebra".to_string(),
            )],
            "(a + 1)^30 is a power algebra does not multiply out",
        ),
        // A side condition is supplied by what the step names, not by
        // everything in scope: the scope holds |T| = 2^k, and with 1.2.5 no
        // longer cited nothing the step names says it.
        case(
            "settle a side condition from a line the step does not cite",
            vec![edit(
                "proofs/wiedijk/subsets.proof",
                Some("n := 2^k, from 1.8, 1.10, 1.11".to_string()),
                "n := 2^k, from 1.8, 1.11".to_string(),
            )],
            "step 1.13 cites mun:card-disjoint-union, which asks for |T| = 2^k, and what it cites does not supply it",
        ),
        // `card-remove` loses its metamath-proof, and the edit to its record
        // changes what it concludes, so the step citing it claims what it
        // does not.
        case(
            "cite a theorem the database gives no metamath-proof for",
            vec![edit(
                "corpus/stdlib/counting.records",
                Some("  then        |X ∖ {a}| = k\n  metamath-proof hashdifsnp1 with V := X, N := a, Y := k\n".to_string()),
                "  then        |X ∖ {a}| ≤ k\n  metamath-proof not yet implemented\n".to_string(),
            )],
            "step 1.7 claims something that mun:card-remove does not conclude",
        ),
        // A definition with no metamath-proof concludes only what its record
        // says, and a step claiming something else of it is refused.
        case(
            "unfold a definition with no metamath-proof into what it does not say",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("10. For all s ∈ S, s ≤ c.".to_string()),
                "10. For all s ∈ S, s < c.".to_string(),
            )],
            "step 10 claims something that def:upper-bound does not conclude",
        ),
        // Continuity unfolds into what its definition says: with δ where ε
        // belongs, or with δ ≥ 0 where the definition says δ > 0, it is not
        // what the definition concludes.
        case(
            "unfold continuity into what it does not say",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("|f(x) − f(c′)| < ε for all x".to_string()),
                "|f(x) − f(c′)| < δ for all x".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
        case(
            "unfold continuity with a weaker bound than it gives",
            vec![edit(
                "proofs/wiedijk/intermediate-value.proof",
                Some("there exists δ > 0 such that".to_string()),
                "there exists δ ≥ 0 such that".to_string(),
            )],
            "step 15 claims something that def:continuous-on does not conclude",
        ),
    ]
}
