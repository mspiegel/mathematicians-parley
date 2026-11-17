//! The planted cases about a proof's shape: numbering and labels, blocks, cases and induction parts, where lines stand and what a citation may reach.

use super::*;

pub(super) fn cases() -> Vec<Case> {
    vec![
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
        // A line fills every hypothesis it says, so it is cited once.
        case(
            "cite one line twice in a step's list",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("thm:divides-gcd a := p, b := q, from 2.1\n".to_string()),
                "thm:divides-gcd a := p, b := q, from 2.1, 2.1\n".to_string(),
            )],
            "step 2.2 cites 2.1 more than once",
        ),
        case(
            "cite one line twice in a requires line's list",
            vec![edit(
                "proofs/wiedijk/mean-value.proof",
                Some(
                    "    requires b − a ≠ 0: weakening, from 1\n    requires f(a) ∈ ℝ: from H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n\n22."
                        .to_string(),
                ),
                "    requires b − a ≠ 0: weakening, from 1\n    requires f(a) ∈ ℝ: from H4, H4, 2\n    requires f(b) ∈ ℝ: from H4, 3\n\n22."
                    .to_string(),
            )],
            "cites H4 more than once",
        ),
        // Labels come first and then lines, each in order.
        case(
            "cite a list out of order",
            vec![edit(
                "proofs/wiedijk/sqrt2-irrational.proof",
                Some("Q := n is odd, from 1, 2\n".to_string()),
                "Q := n is odd, from 2, 1\n".to_string(),
            )],
            "cites 2, 1 out of order",
        ),
        case(
            "cite a line before a label",
            vec![edit(
                "proofs/wiedijk/bezout.proof",
                Some("algebra, from H9, H10, 1\n".to_string()),
                "algebra, from 1, H9, H10\n".to_string(),
            )],
            "from H9, H10, 1",
        ),
        case(
            "cite a line inside a block that has closed",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.1.1".to_string()),
            ],
            "inside a block that has closed",
        ),
        // A define written in one case is no define of the next.
        case(
            "cite a define written in an earlier case",
            vec![edit(
                "tests/elaborator/textbook-exercise-shapes-two.proof",
                Some("    assume x = 2                                                      (C2)\n\n    1.5.  2 > 0\n          arithmetic\n\n    1.6.  x > 0\n          transitivity, from C2, 1.5\n".to_string()),
                "    assume x = 2                                                      (C2)\n\n    1.5.  y = x\n          D1\n\n    1.6.  2 > 0\n          arithmetic\n\n    1.7.  x > 0\n          transitivity, from C2, 1.6\n".to_string(),
            )],
            "step 1.5 cites D1, which is not in scope here",
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
                Some("2.  a < 2·√a\n".to_string()),
                "2a. a < 2·√a\n".to_string(),
            )],
            "`2a.` is no step number",
        ),
        // A case with no steps says it is the claim; one that does not is
        // reported where it is, not where the step after it lands.
        case(
            "a last case with no steps that does not say it is the claim",
            vec![edit(
                "proofs/euclid/hinge.proof",
                Some("assume B and C are on opposite sides of line AG, which is the claim (C2)".to_string()),
                "assume B and C are on opposite sides of line AG (C2)".to_string(),
            )],
            "this case of step 23 has no steps, and its assumption does not say it is the claim; write its steps, or end the line `, which is the claim`",
        ),
        case(
            "cite a line that comes after the step",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("    16.2.  c < b\n           inequalities, from 12, 16.1".to_string()), "    16.2.  c < b\n           inequalities, from 12, 16.3".to_string()),
            ],
            "step 16.2 cites line 16.3, which comes after it",
        ),
        case(
            "cite a line that does not exist",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    2.5.  p is even\n          thm:even-square n := p, from 2.4".to_string()), "    2.5.  p is even\n          thm:even-square n := p, from 2.99".to_string()),
            ],
            "does not exist",
        ),
        case(
            "cite the assumption of another case",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    2.9.  x < |x|\n          transitivity, from C2, 2.8, 2.6".to_string()), "    2.9.  x < |x|\n          transitivity, from C2, 2.8, 2.6, C1".to_string()),
            ],
            "not in scope",
        ),
        case(
            "number a step under a parent that does not exist",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.9.4.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()),
            ],
            "does not exist",
        ),
        case(
            "use a part marker the method does not declare",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    case\n    assume x ≥ 0".to_string()), "    base\n    assume x ≥ 0".to_string()),
            ],
            "is not one of the parts",
        ),
        case(
            "a block whose method takes none",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("11. (m + 1) − (m + 1) = 0\n    algebra\n".to_string()), "11. (m + 1) − (m + 1) = 0\n    algebra\n\n    11.1.  m = m\n           algebra\n".to_string()),
            ],
            "takes no block",
        ),
        // An induction's step part assumes its own claim's statement, and
        // names that claim by the induction's number (`SYNTAX.md`).
        case(
            "an induction hypothesis naming another step",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 2 is true for k".to_string()),
            ],
            "the induction hypothesis names step 2, and the induction is step 1",
        ),
        // It is for the letter the claim binds, and no other.
        case(
            "an induction hypothesis for another letter",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("assume step 1 is true for k".to_string()), "assume step 1 is true for j".to_string()),
            ],
            "the induction hypothesis is for j, and step 1 is said for all k",
        ),
        // The hypothesis is the claim's words where they stand; written out
        // again, the step part does not say it is the induction hypothesis.
        case(
            "a step part that writes its hypothesis out",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    assume step 1 is true for k, the induction hypothesis             (IH)".to_string()), "    assume S(k) = k(k + 1)/2                                          (IH)".to_string()),
            ],
            "the step part of step 1 does not open with `let k ∈ ℕ` and `assume step 1 is true for k, the induction hypothesis`, those two lines in that order and no other",
        ),
        case(
            "a step part that assumes something besides its hypothesis",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    assume step 1 is true for k, the induction hypothesis             (IH)".to_string()), "    assume step 1 is true for k, the induction hypothesis             (IH)\n    assume k = k                                                      (A1)".to_string()),
            ],
            "the step part of step 1 does not open with `let k ∈ ℕ` and `assume step 1 is true for k, the induction hypothesis`, those two lines in that order and no other",
        ),
        case(
            "split into one case",
            vec![edit(
                "proofs/zz/one-case.proof",
                None,
                "theorem one-case\n  let a ∈ ℝ                                                           (H1)\n  assume a = 0                                                        (H2)\n  then a = 0\n\n1.  a = 0\n    cases, from H2\n\n    case\n    assume a = 0                                                      (C1)\n\n    1.1.  a = 0\n          restate C1\n".to_string(),
            )],
            "step 1 takes one case, and a case split takes two or more; prove the one case as a plain step",
        ),
        case(
            "a theorem introducing a property",
            vec![edit(
                "proofs/zz/let-property.proof",
                None,
                "theorem let-property\n  let A be a set                                                      (H1)\n  let P be a property of the elements of A                            (H2)\n  then A = A\n\n1.  A = A\n    algebra\n".to_string(),
            )],
            "`let P be a property of the elements of A` introduces a property, which only a library item may",
        ),
        case(
            "a proof block claiming two sentences",
            vec![edit(
                "proofs/zz/proof-two.proof",
                None,
                "theorem proof-two\n  let a ∈ ℝ                                                           (H1)\n  then if a = 0 then a = 0\n\n1.  If a = 0 then a = 0. If a = 0 then a = 0.\n    proof\n    assume a = 0                                                      (K1)\n\n    1.1.  a = 0\n          restate K1\n\n2.  If a = 0 then a = 0.\n    restate 1\n".to_string(),
            )],
            "step 1 opens a proof block and claims 2 sentences; the block proves one, and each other sentence is a step of its own",
        ),
        // Each part of a block ends on what it owes (`SYNTAX.md`): the base
        // on the claim's statement at the start, the step on it at k + 1, a
        // case on the block's claim, a proof block on its claim with what
        // its openers took off it. Each of these stops one line short.
        case(
            "an induction's base that stops short of the claim's first instance",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.1.  S(1) = 1(1 + 1)/2\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     mun:sum-single a := 1\n                 = 1(1 + 1)/2            arithmetic".to_string()), "    1.1.  S(1) = 1\n          calculation\n            S(1) = Σ(j = 1 to 1) j       D1\n                 = 1                     mun:sum-single a := 1".to_string()),
            ],
            "step 1.1 ends the base part of step 1, which owes",
        ),
        case(
            "an induction's step that stops short of the next instance",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.3.  S(k + 1) = (k + 1)((k + 1) + 1)/2\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.2\n                     = k(k + 1)/2 + (k + 1)         substitute IH\n                     = (k + 1)((k + 1) + 1)/2       algebra".to_string()), "    1.3.  S(k + 1) = k(k + 1)/2 + (k + 1)\n          calculation\n            S(k + 1) = S(k) + (k + 1)               1.2\n                     = k(k + 1)/2 + (k + 1)         substitute IH".to_string()),
            ],
            "step 1.3 ends the step part of step 1, which owes",
        ),
        case(
            "a case that stops short of the block's claim",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    2.5.  x ≤ |x|. −x ≤ |x|.\n          join 2.2, 2.4\n\n    case\n    assume x < 0".to_string()), "    case\n    assume x < 0".to_string()),
            ],
            "step 2.4 ends case 1 of step 2, which owes",
        ),
        case(
            "a proof block that stops short of its claim",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("    4.6.  L(k) ∈ ℝ. U(k) ∈ ℝ. L(k) ≤ U(k).\n          join 4.2, 4.3, 4.5".to_string()), "    4.6.  L(k) ∈ ℝ. U(k) ∈ ℝ.\n          join 4.2, 4.3".to_string()),
            ],
            "step 4.6 ends the proof block of step 4, which owes",
        ),
        case(
            "a contradiction whose block does not suppose anything",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    contradiction\n    suppose √2 ∈ ℚ                                                    (S)".to_string()), "    contradiction".to_string()),
            ],
            "does not open with `suppose`",
        ),
        case(
            "a theorem that cites itself",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("          thm:odd-square, from S".to_string()), "          thm:even-square, from S".to_string()),
            ],
            "theorem even-square cites itself",
        ),
        case(
            "two theorems of one file that cite each other",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    def:odd n := n², from 2".to_string()), "    thm:even-square n := n², from 2".to_string()),
            ],
            "closes a cycle of citations: even-square → odd-square → even-square",
        ),
        case(
            "two theorems of one name in one file",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("theorem even-square\n".to_string()), "theorem odd-square\n".to_string()),
            ],
            "theorem odd-square is already proved",
        ),
        case(
            "a theorem field said twice",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("  note        Let B be".to_string()), "  note        twice.\n  note        Let B be".to_string()),
            ],
            "says note twice",
        ),
        case(
            "open a block under a calculation",
            vec![edit(
                "proofs/zz/calculation-block.proof",
                None,
                "theorem calculation-block\n  let a ∈ ℝ                                                           (H1)\n  assume a = 1                                                        (H2)\n  then a = 1\n\n1.  a = 1\n    calculation\n      a = 1          H2\n    assume a = a                                                      (A1)\n\n    1.1.  a = 1\n          restate H2\n".to_string(),
            )],
            "step 1 is a calculation, which writes its chain and opens no block of steps",
        ),
        case(
            "note a step that opens no block",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("1.  B ⊆ A\n    mun:set-builder-subset, from D1".to_string()), "1.  B ⊆ A\n    mun:set-builder-subset, from D1\n    note this is where B becomes a part".to_string()),
            ],
            "opens no block",
        ),
        case(
            "note a case part after its assumption",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("          note V is a subset without a, with a put back\n          assume a ∈ V                                                (C1)".to_string()), "          assume a ∈ V                                                (C1)\n          note V is a subset without a, with a put back".to_string()),
            ],
            "directly under its marker",
        ),
        case(
            "note a case part twice",
            vec![
                edit("proofs/wiedijk/subsets.proof", Some("          note V is a subset without a, with a put back\n".to_string()), "          note V is a subset without a, with a put back\n          note V holds a\n".to_string()),
            ],
            "already carries a note",
        ),
        case(
            "add a member to a part of a set from outside the rest",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("    let a ∈ X ∖ Y                                                     (K2)\n".to_string()),
                "    let a ∈ X                                                         (K2)\n".to_string(),
            )],
            "the step part of step 1 does not open with `let Y ⊆ X`, `assume step 1 is true for Y, the induction hypothesis` and `let a ∈ X ∖ Y`, a the member the step adds, those three lines in that order and no other",
        ),
        case(
            "end an induction over the parts of a set short of Y ∪ {a}",
            vec![edit(
                "tests/elaborator/induction-over-a-set.proof",
                Some("\n    1.5.  ∏(y ∈ Y ∪ {a}) 1 = 1\n          transitivity, from 1.4, IH\n".to_string()),
                String::new(),
            )],
            "step 1.4 ends the step part of step 1, which owes ∏(y ∈ Y ∪ {a}) 1 = 1",
        ),
        case(
            "say a case is the claim when it is not",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("assume f(c) = 0, which is the claim".to_string()), "assume f(c) = 1, which is the claim".to_string()),
            ],
            "case C2 says it is the claim of step 16, and it is not",
        ),
        case(
            "say a case with steps is the claim",
            vec![
                edit("proofs/wiedijk/intermediate-value.proof", Some("assume 0 < f(c)                                                   (C3)".to_string()), "assume 0 < f(c), which is the claim                               (C3)".to_string()),
            ],
            "case C3 is the claim and has steps of its own",
        ),
        case(
            "say a line is the claim outside any cases block",
            vec![
                edit("proofs/wiedijk/cantor.proof", Some("    suppose f(x) = B                                                  (S)".to_string()), "    suppose f(x) = B, which is the claim                              (S)".to_string()),
            ],
            "a line saying it is the claim outside any `cases` block",
        ),
        // Every block of binomial-step fixes k under the label J, and J means
        // what the block around the citing step says: here k runs from 1. Read
        // theorem-wide, J was the last block's, from 0, and this edit passed.
        case(
            "a label read as a sibling block's",
            vec![
                edit("proofs/wiedijk/binomial.proof", Some("    20.1.  m − (k − 1) = (m + 1) − k\n           algebra\n".to_string()), "    20.1.  m − (k − 1) = (m + 1) − k\n           algebra\n           requires (m + 1) − k ∈ ℕ₀: mun:range-difference a := 0, n := m + 1, from J\n".to_string()),
            ],
            "the requires line of step 20.1 cites mun:range-difference",
        ),
        // Steps count 1, 2, 3 in the order they are written: a reader meeting 8
        // after 6 looks for a 7 that is not there.
        case(
            "a gap in the numbering",
            vec![
                edit("proofs/wiedijk/infinitely-many-primes.proof", Some("6.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()), "7.  There exists p ∈ ℕ such that p is prime and p > n.".to_string()),
            ],
            "numbers run on without gaps",
        ),
        // The steps are numbered as a reader counts them.
        case(
            "a step number written twice",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("    1.3.  S(k + 1) = (k + 1)((k + 1) + 1)/2".to_string()), "    1.2.  S(k + 1) = (k + 1)((k + 1) + 1)/2".to_string()),
            ],
            "step 1.2 is numbered twice",
        ),
        // A method that opens a block has one, with the parts its record
        // declares, each opening as the record says.
        case(
            "a method that needs a block with none",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("2.  Σ(k = 1 to n) k = n(n + 1)/2\n    calculation\n      Σ(k = 1 to n) k = S(n)              D1\n                      = n(n + 1)/2        instantiate k := n in line 1".to_string()), "2.  Σ(k = 1 to n) k = n(n + 1)/2\n    contradiction".to_string()),
            ],
            "step 2 is justified by contradiction, which needs a block, and has no sub-steps",
        ),
        case(
            "an induction block with no part markers",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    1.1.".to_string()),
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    step\n    let k ∈ ℕ".to_string()), "\n    let k ∈ ℕ".to_string()),
            ],
            "step 1 cites induction, whose block carries the parts",
        ),
        case(
            "a part marker in a block that has no parts",
            vec![
                edit("proofs/wiedijk/sqrt2-irrational.proof", Some("    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()), "    base\n    2.1.  d ∈ ℤ. d > 1. d divides p. d divides q.".to_string()),
            ],
            "under a contradiction block, which declares no parts",
        ),
        case(
            "a proof block that opens with neither let nor assume",
            vec![
                edit("proofs/wiedijk/reals-uncountable.proof", Some("    let k ∈ ℕ₀                                                        (K1)\n".to_string()), String::new()),
            ],
            "is a proof whose block does not open with `let` or `assume`",
        ),
        case(
            "a case that does not open with an assumption",
            vec![
                edit("proofs/wiedijk/triangle-inequality.proof", Some("    case\n    assume x ≥ 0                                                      (C1)\n".to_string()), "    case\n".to_string()),
            ],
            "part of step 2 does not open with a labelled `assume`",
        ),
        case(
            "an induction's base that opens with a let",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("\n    base\n    1.1.".to_string()), "\n    base\n    let j ∈ ℕ                                                         (J)\n\n    1.1.".to_string()),
            ],
            "the base part of step 1 opens with a",
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
        // `join` puts two lines or more together and `restate` says one
        // again (`SYNTAX.md`): each refused with the other's count.
        case(
            "join one line",
            vec![edit(
                "proofs/setmm/divisor-of-power.proof",
                Some("          restate H4".to_string()),
                "          join H4".to_string(),
            )],
            "joins one line; a step citing one line is written `restate H4`",
        ),
        case(
            "restate two lines",
            vec![edit(
                "proofs/setmm/halves-series.proof",
                Some("                  join 3.2.7, 3.2.10".to_string()),
                "                  restate 3.2.7, 3.2.10".to_string(),
            )],
            "restates 3.2.7, 3.2.10; a step putting several lines together is written `join 3.2.7, 3.2.10`",
        ),
        case(
            "an induction whose base part has no steps",
            vec![edit(
                "proofs/setmm/divisor-of-power.proof",
                Some("    base\n    1.1.  K divides M^1\n          restate H4\n".to_string()),
                "    base\n".to_string(),
            )],
            "has no steps, so nothing shows what it owes",
        ),
        case(
            "a requires line whose reason is neither a method, an item, nor a line",
            vec![
                edit("proofs/wiedijk/sum-formula.proof", Some("          requires k ≥ 1: from K".to_string()), "          requires k ≥ 1: because K".to_string()),
            ],
            "which is neither a method, an item, nor a line",
        ),
        case(
            "a theorem with no steps",
            vec![edit("proofs/wiedijk/empty.proof", None, "theorem empty\n  then 1 = 1\n".to_string())],
            "theorem empty has no steps",
        ),
        // A last step that proves one sentence of a conclusion of two is
        // correct as far as it goes, and every other check passes it.
        case(
            "a last step claiming less than the conclusion",
            vec![edit(
                "proofs/wiedijk/short.proof",
                None,
                "theorem short\n  then 1 + 1 = 2. 2 + 2 = 4.\n\n1.  1 + 1 = 2\n    arithmetic\n"
                    .to_string(),
            )],
            "step 1 is the last, and does not claim what short states",
        ),
        // A label outside a file's theorems is one label for every theorem
        // below it, and a define says what its name means.
        case(
            "a label given twice outside the theorems",
            vec![
                edit("proofs/wiedijk/geometric-series.proof", Some("       reads the geometric series: the powers of a, from a^0 up to a^n\n".to_string()), "       reads the geometric series: the powers of a, from a^0 up to a^n\n\ndefine H(n) := n + 1, for n ∈ ℕ                                    (D1)\n       reads one more than n\n".to_string()),
            ],
            "label D1 is already used at line 5",
        ),
        case(
            "a requires line under a join",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 0    (H2)\n  assume x < 2    (H3)\n  then x > 0 and x < 2\n\n1.  x > 0 and x < 2\n    join H2, H3\n    requires x ≠ 0: weakening, from H2\n".to_string(),
            )],
            "step 1 is a join, which asks nothing of the lines it puts together, and carries a requires line",
        ),
        case(
            "a last case with no steps",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  assume x > 2 or x > 1    (H2)\n  then x > 0\n\n1.  x > 0\n    cases, from H2\n\n    case\n    assume x > 2    (C1)\n\n    1.1.  x > 0\n          inequalities, from C1\n\n    case\n    assume x > 1    (C2)\n".to_string(),
            )],
            "this case has no steps, and the theorem ends under it; write its steps, or end its assumption `, which is the claim`",
        ),
        case(
            "a proof block with no steps under its let",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  then for all y ∈ ℝ, y = y\n\n1.  For all y ∈ ℝ, y = y.\n    proof\n    let y ∈ ℝ    (K1)\n".to_string(),
            )],
            "K1 opens a part with no steps, and the theorem ends under it",
        ),
        // A proof block assumes what its claim supposes.
        case(
            "a proof block assuming other than its claim supposes",
            vec![edit(
                "proofs/wiedijk/planted.proof",
                None,
                "theorem planted\n  let x ∈ ℝ    (H1)\n  then if x > 1 then x ≥ 1\n\n1.  If x > 1 then x ≥ 1.\n    proof\n    assume x ≥ 2    (A)\n\n    1.1.  x ≥ 1\n          inequalities, from A\n".to_string(),
            )],
            "step 1 opens a proof block assuming x ≥ 2, and its claim supposes 1 < x",
        ),
        // A step nothing cites, and that ends no part, says something the
        // proof never uses: 0 < 1 is true, and no line goes on from it.
        case(
            "write a step nothing cites",
            vec![edit(
                "proofs/hammack/abs-limit-zero.proof",
                Some("2.  a(n) → 0 as n → ∞\n    def:tends-to L := 0, from 1\n".to_string()),
                "2.  0 < 1\n    arithmetic\n\n3.  a(n) → 0 as n → ∞\n    def:tends-to L := 0, from 1\n".to_string(),
            )],
            "step 2 is cited by nothing, and is not the last step of its part",
        ),
        // A nested block's step numbered as its owner's sibling is read as
        // the enclosing block's, and the numbering is what is named.
        case(
            "number a nested case's step at the outer level",
            vec![edit(
                "proofs/setmm/prime-two-or-odd.proof",
                Some("          2.6.1.  2 ≠ 1\n".to_string()),
                "          2.7.    2 ≠ 1\n".to_string(),
            )],
            "step 2.6 is justified by cases, which needs a block, and has no sub-steps: the step below it is numbered 2.7, so what stands under it is read as part of step 2's block; a step of 2.6's block is numbered 2.6.1",
        ),
        // A theorem proved `by` a method is that method's step, which the
        // page gives no number, whose block holds every step of the proof
        // (`SYNTAX.md`, a theorem proved by a method).
        case(
            "prove a theorem by a method that opens no block",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions".to_string()),
                "  by          algebra".to_string(),
            )],
            "`by` names a method that opens a block: both directions, contradiction, proof, induction or cases; algebra proves a step",
        ),
        case(
            "write by twice",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions\n".to_string()),
                "  by          both directions\n  by          both directions\n".to_string(),
            )],
            "`by` comes once, under `then`, before the proof",
        ),
        case(
            "a step above the first part of a theorem proved by both directions",
            vec![edit(
                "proofs/setmm/subset-of-union-and-difference.proof",
                Some("  by          both directions\n\ndirection\n".to_string()),
                "  by          both directions\n\n1.  A ⊆ A\n    mun:subset-reflexive X := A\n\ndirection\n".to_string(),
            )],
            "step 1 stands outside the theorem's block; under `by` every step is in one of its parts",
        ),
        case(
            "an induction hypothesis naming a step of a theorem proved by induction",
            vec![edit(
                "proofs/wiedijk/liouville-number.proof",
                Some("assume the theorem is true for j, the induction hypothesis            (IH)".to_string()),
                "assume step 1 is true for j, the induction hypothesis                 (IH)".to_string(),
            )],
            "the theorem has no step 1; its induction hypothesis says `assume the theorem is true for j, the induction hypothesis`",
        ),
        case(
            "a theorem proved by contradiction whose block ends on no contradiction",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("    inequalities, from H2, contradicting 1\n".to_string()),
                "    inequalities, from H2\n".to_string(),
            )],
            "step 2 ends a contradiction block and does not say which line it contradicts",
        ),
        case(
            "a theorem proved by contradiction with no steps",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("  by          contradiction\n\nsuppose 3 divides r                                                   (S)\n\n1.  3 ≤ r\n    mun:divides-le e := 3, m := r, from S\n\n2.  not 3 ≤ r\n    inequalities, from H2, contradicting 1\n".to_string()),
                "  by          contradiction\n".to_string(),
            )],
            "the theorem is proved `by contradiction` and its block has no steps",
        ),
        // A part of a block names the method of its own block on a `by` line
        // after its openers: `by proof` or `by contradiction` (`SYNTAX.md`,
        // Blocks).
        case(
            "a part proved by cases",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    by          proof\n    assume P divides Q^(m + 1)".to_string()),
                "    by          cases\n    assume P divides Q^(m + 1)".to_string(),
            )],
            "`by` inside a block names proof or contradiction, whose blocks open with lines; cases opens parts",
        ),
        case(
            "a part that says by twice",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    base\n    by          proof\n".to_string()),
                "    base\n    by          proof\n    by          proof\n".to_string(),
            )],
            "a part says `by` once, after its openers and before its first step",
        ),
        case(
            "a part's by line after its first step",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    3.1.  Q^0 = 1\n          algebra\n".to_string()),
                "    3.1.  Q^0 = 1\n          algebra\n    by          proof\n".to_string(),
            )],
            "`by` in a block comes after its part's openers, before its first step",
        ),
        case(
            "a part's by line with a part marker after it",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    base\n    by          proof\n".to_string()),
                "    base\n    by          proof\n    step\n".to_string(),
            )],
            "has no steps before the next part",
        ),
        case(
            "an induction hypothesis after the part's by line",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    assume step 3 is true for m, the induction hypothesis             (IH)\n    by          proof\n".to_string()),
                "    by          proof\n    assume step 3 is true for m, the induction hypothesis             (IH)\n".to_string(),
            )],
            "the induction hypothesis comes before the part's `by` line",
        ),
        case(
            "a part proved by proof that lets and assumes nothing",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    by          proof\n    assume P divides Q^0                                              (C1)\n".to_string()),
                "    by          proof\n".to_string(),
            )],
            "the base part of step 3 is proved by `proof` and does not open with `let` or `assume` after its `by` line",
        ),
        case(
            "a part proved by proof assuming what it does not owe",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("    assume P divides Q^(m + 1)                                        (C2)".to_string()),
                "    assume P divides Q^m                                              (C2)".to_string(),
            )],
            "the step part of step 3 opens a proof block assuming",
        ),
        case(
            "a part proved by proof ending on what it does not owe",
            vec![edit(
                "proofs/setmm/prime-divides-power.proof",
                Some("          inequalities, contradicting 3.3\n".to_string()),
                "          inequalities\n".to_string(),
            )],
            "step 3.4 ends the base part of step 3, which owes P = Q",
        ),
        case(
            "a part proved by contradiction that assumes",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("suppose a = 0                                                         (S)".to_string()),
                "assume a = 0                                                          (S)".to_string(),
            )],
            "the proof block of the theorem is proved by contradiction and does not open with `suppose` after its `by` line",
        ),
        case(
            "a part proved by contradiction supposing what it does not deny",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("suppose a = 0                                                         (S)".to_string()),
                "suppose a = 1                                                         (S)".to_string(),
            )],
            "the proof block of the theorem supposes something that is neither what it owes negated nor the thing it owes negates",
        ),
        case(
            "a part proved by contradiction ending on no contradiction",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("    restate K2, contradicting 1".to_string()),
                "    restate K2".to_string(),
            )],
            "step 2 ends the proof block of the theorem, proved by contradiction, and does not say which line it contradicts",
        ),
        case(
            "a part proved by contradiction that never uses its supposition",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("    mun:modus-ponens, from K1, S".to_string()),
                "    mun:modus-ponens, from K1".to_string(),
            )],
            "the proof block of the theorem is proved by contradiction and never uses its supposition S",
        ),
        case(
            "a proof block that says by proof",
            vec![edit(
                "proofs/setmm/contrapositive.proof",
                Some("by          contradiction\nsuppose a = 0".to_string()),
                "by          proof\nassume a = 0".to_string(),
            )],
            "the proof block of the theorem says `by proof`; its let and assume lines go on without it",
        ),
        case(
            "a contradiction block that says by",
            vec![edit(
                "proofs/hammack/rational-squares-sum-not-three.proof",
                Some("suppose 3 divides r                                                   (S)\n".to_string()),
                "suppose 3 divides r                                                   (S)\nby          proof\n".to_string(),
            )],
            "the theorem is a contradiction, whose block owes no claim for `by` to prove",
        ),
    ]
}
