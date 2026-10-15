# Held trial proofs

Proofs written in the proof-writing trials of 13 and 14 October 2026 that
are not yet in the corpus, because each runs into a fault of the tools.
The rest of the trials' proofs are in `proofs/setmm/` and `proofs/hammack/`.

Each file is the writer's proof with its imports set to the collections'
paths, and nothing else changed. It is named `.proof.held` so that no tool
reads it: the tools read every `.proof` file under the root. A proof joins
the corpus by moving it to `proofs/<collection>/<name>.proof` in the commit
that fixes the fault it shows, which the tools' tests then hold.

The fault given is the first each showed, at a327a21: the checker's or the
build's message, or the test that broke. The trial is the git worktree it
was written in, under `.claude/worktrees/`.

## The checker refuses it

| Proof | Trial | Fault |
|---|---|---|
| setmm/a-over-n-limit | wf_780145c1-124-5 | step 5 cites def:tends-to, which asks that every term A / n is in ℝ, and it is no number by what the page says once |
| setmm/binomial-coefficients-sum | wf_986a075e-80b-4 | a link of step 1.3 drops an identity element from 1^m, which nothing the step names says is a number |
| setmm/constant-sequence-limit | wf_780145c1-124-5 | the requires line of step 2.1.2 cites K2, and x(n) ∈ ℝ needs nothing it says |
| setmm/group-inverses | wf_780145c1-124-1 | step 2.3 cites D2, and thm:group-inverse-by-right asks for nothing it says |
| setmm/halves-series | wf_986a075e-80b-4 | step 3.1 cites mun:sum-single, which asks that every term 1 / 2^j is in ℝ, and it is no number by what the page says once |
| setmm/limit-add-constant | wf_780145c1-124-5 | the requires line of step 2.3.2 cites K2, and x(n) ∈ ℝ needs nothing it says |
| setmm/limit-constant-multiple | wf_780145c1-124-5 | the requires line of step 5.6.2 cites K2, and x(n) ∈ ℝ needs nothing it says |
| setmm/limit-negative | wf_780145c1-124-5 | the requires line of step 2.3.2 cites K2, and x(n) ∈ ℝ needs nothing it says |
| setmm/limit-unique | wf_780145c1-124-5 | the requires line of step 1.12 cites 1.8, and x(N₁ + N₂) ∈ ℝ needs nothing it says |
| setmm/prime-divisor-in-range | wf_986a075e-80b-5 | step 3 cites 2, and mun:pos-int-nat asks for nothing it says |
| setmm/sine-of-double | wf_780145c1-124-4 | the requires line sin(A) ∈ ℂ of step 4, read as a step citing what it cites: sin(A) ∈ ℂ is not built from what step 4 cites |
| setmm/size-of-difference | wf_986a075e-80b-3 | step 10 cites 8, and mun:card-disjoint-union asks for nothing it says |
| setmm/size-of-union | wf_986a075e-80b-3 | step 11 cites 9, and mun:card-disjoint-union asks for nothing it says |
| hammack/inverse-squares-bounded | wf_829f59af-3f8-1 | step 1.1 cites mun:sum-single, which asks that every term 1 / j² is in ℝ, and it is no number by what the page says once |
| hammack/reciprocal-product-sum | wf_210363c5-087-4 | step 1.1 cites mun:sum-single, which asks that every term 1 / (j · (j + 1)) is in ℝ, and it is no number by what the page says |
| hammack/sum-of-factorial-quotients | wf_829f59af-3f8-1 | step 1.2 cites 1.1, and mun:factorial-nonzero asks for nothing it says |
| hammack/weighted-binomial-sum | wf_829f59af-3f8-1 | step 2 cites 1, and mun:nat-minus-one asks for nothing it says |

## The checker accepts it and the build cannot prove it

| Proof | Trial | Fault |
|---|---|---|
| setmm/parity | wf_187c8c13-16b-4 | step 2 cites 1 and uses nothing it says |
| setmm/two-does-not-divide-odd | wf_2d3af610-0d7-2 | step 2.2 cites 1 and uses nothing it says |
| hammack/divisible-by-nine | wf_829f59af-3f8-1 | the requires line (4^(3m) + 8)·64 ∈ ℤ of step 1.13: the checker reads no citation of stdlib/numbers/int-closure on this line |
| hammack/divisible-by-twenty-four | wf_829f59af-3f8-1 | the requires line (5^(2m) − 1)·25 ∈ ℤ of step 1.11: the checker reads no citation of stdlib/numbers/int-closure on this line |
| hammack/five-power-minus-one | wf_210363c5-087-4 | the requires line (5^(2k) − 1)·25 ∈ ℤ of step 1.13: the checker reads no citation of stdlib/numbers/int-closure on this line |

## A test or the gate breaks on it

A rewrite of `tests/invariance.rs` keeps a proof's meaning, and the tools
then refuse it; or the gate, or `tests/said_back.rs`, fails.

| Proof | Trial | Test | Fault |
|---|---|---|---|
| setmm/floor-basics | wf_187c8c13-16b-1 | a block made a lemma | step 5 cites 2, and thm:integer-at-most-floor-5 asks for nothing it says |
| setmm/floor-is-monotone | wf_2d3af610-0d7-1 | a block made a lemma | step 7 cites 5, and thm:floor-is-monotone-7 asks for nothing it says |
| setmm/floor-quotient-zero | wf_2d3af610-0d7-2 | a block made a lemma | step 7 cites 2, and thm:floor-quotient-zero-7 asks for nothing it says |
| setmm/integer-below-a-real | wf_2d3af610-0d7-1 | a block made a lemma | step 5 cites 4, and thm:integer-below-a-real-5 asks for nothing it says |
| setmm/less-than-an-integer | wf_2d3af610-0d7-1 | a block made a lemma | step 5 cites 4, and thm:less-than-an-integer-5 asks for nothing it says |
| setmm/irrational-plus-rational | wf_f7943927-07d-5 | a block made a lemma | step 1.7 says it contradicts H5, and neither is the other negated |
| setmm/irrational-times-rational | wf_f7943927-07d-5 | a block made a lemma | step 1.5 says it contradicts H6, and neither is the other negated |
| setmm/image-as-a-selection | wf_986a075e-80b-1 | a block made a lemma; letters renamed to the library's | the last step does not say what the theorem states: no renaming says the two are one; step 2 claims something that mun:subset does not conclude |
| setmm/not-both | wf_780145c1-124-3 | a conjunction claim written as sentences | step 1.2.1.2 says it contradicts 1.2.1.1, and neither is the other negated |
| setmm/binomial-basics | wf_187c8c13-16b-4 | a relation turned around | step 2.8 drops an identity element from what the substitution makes, and nothing says 0! is a number |
| setmm/root-gives-factor | wf_b955cf1a-292-1 | a relation turned around; the gate | a link of step 2.4 drops an identity element from (x − a) · q(x); step 1 cites with the pair a := a, and the step is checked and built without it |
| setmm/two-elements | wf_986a075e-80b-3 | a relation turned around | the build: no clause of mun:remove-member reaches what step 1.6 claims |
| setmm/images-of-parts-under-a-one-to-one-map | wf_986a075e-80b-2 | a step citing an item written as a requires line | the build: no clause of mun:iff-from-left reaches what step 1.1.3 claims |
| setmm/implication-and-currying | wf_780145c1-124-3 | a step citing an item written as a requires line | the build: no clause of mun:modus-ponens reaches what step 1.2.3 claims |
| setmm/prime-divides-power | wf_986a075e-80b-5 | a step citing an item written as a requires line | the build: no clause of mun:iff-from-left reaches what step 2.2.5.2 claims |
| setmm/size-positive | wf_986a075e-80b-3 | a step serving only requires lines written as one | the requires line of step 2 says \|A\| ∈ ℝ, which the step's other lines already say |
| setmm/image-of-part | wf_187c8c13-16b-3 | letters renamed to the library's | step 2 claims something that mun:subset does not conclude |
| setmm/factor-by-root | wf_780145c1-124-4 | the gate | step 1 cites with the pair a := a, and the step is checked and built without it |
| setmm/group-cancellation | wf_780145c1-124-2 | said back | line 427, "There is k ∈ H with g·h = g·k", has no page reading to say back |
| hammack/factorial-from-zero | wf_829f59af-3f8-1 | a relation turned around | step 3.7 drops an identity element from what the substitution makes, and nothing says 0! is a number |
| hammack/mobius-one-to-one | wf_210363c5-087-5 | a relation turned around | the build: no clause of mun:remove-member reaches what step 1.1 claims |
| hammack/image-of-intersection | wf_829f59af-3f8-4 | letters renamed to the library's | step 2 claims something that mun:subset does not conclude |

## It imports one of the above

| Proof | Trial | Imports |
|---|---|---|
| setmm/size-without-a-pair | wf_986a075e-80b-3 | setmm/size-of-difference |
| setmm/remainder-facts | wf_187c8c13-16b-1 | setmm/floor-basics |
| setmm/remainder-zero | wf_187c8c13-16b-1 | setmm/floor-basics |
| setmm/remainder-rules | wf_187c8c13-16b-1 | setmm/remainder-facts |
| setmm/remainder-more | wf_187c8c13-16b-1 | setmm/remainder-facts |
