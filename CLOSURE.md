# What the closure methods have to do

Open question 6 in `GOALS.md` asks how much "by algebra" must carry. This
answers it from the corpus rather than from intuition. `tools/check.py` accepts
four methods without examining them, and lists the steps that rest on each. Of
247 steps, 61 do:

| method | steps | share of the 61 |
|---|---|---|
| inequalities | 25 | 41% |
| algebra | 17 | 28% |
| lines | 16 | 26% |
| arithmetic | 3 | 5% |

Each step below was read together with the claims of the lines it cites, since
what a method must do is get from those claims to that claim.

## lines is nearly free, and hides one real inference

Sixteen steps, and they ask for four things:

| what the step does | uses |
|---|---|
| join two lines into one claim of two sentences | 12 |
| drop a double negation | 2 |
| disjunctive syllogism | 1 |
| restate a case assumption unchanged | 1 |

Twelve of the sixteen are bookkeeping. A contradiction block must end with a
step claiming "P and not P", and the two halves are already on separate lines,
so the step exists to put them on one line. It infers nothing.

The two double negations both come from the contradiction rule. A claim of
"not f(x) = B" makes the literal supposition "not not f(x) = B", and a step
removes the doubling. That is where the classical logic sits, as the Cantor
pilot said.

The restatement is step 17.22 of the intermediate value proof, which claims
f(c) = 0 from a case assumption of exactly f(c) = 0. It exists because every
case must end in the block's common claim. It is a structural artifact.

That leaves one genuine inference in sixteen: step 3 of even-square concludes
"n is even" from "n is not odd" and "n is even or n is odd". The √2 pilot
already flagged it, and it is the one step here where a reader has to do
something.

**What this says.** The expansion of `lines` needs conjunction introduction,
double negation elimination, and disjunctive syllogism. It does not need a
propositional decision procedure. A reasonable alternative is to split it:
name the bookkeeping something that says so, and let the one real inference
cite a theorem the way excluded middle already does.

## inequalities carries the most, and needs linear arithmetic

Twenty-five steps, the largest group:

| what the step does | uses |
|---|---|
| move between a relation and the negation of its complement | 8 |
| rearrange by adding or subtracting the same term | 5 |
| substitute an equal term into an order relation | 4 |
| transitivity, including chains mixing ≤ and < | 3 |
| add two inequalities | 2 |
| turn ≤ together with ≠ into < | 2 |
| antisymmetry | 1 |

The first group is the biggest and the dullest: that a < b gives not b ≤ a,
that not p > n gives p ≤ n, that p > 1 gives not p = 1. Eight steps do nothing
else. They exist because the contradiction rule demands the literal negation,
so every proof that reaches a contradiction through an order relation pays for
a rewriting step.

The rearrangements are the substantive part. From x₁ − c < δ the proof wants
both c − δ < x₁ and x₁ < c + δ. That is linear arithmetic over an ordered
field, the work Lean's `linarith` does, and it is not a lookup in a table of
named laws.

Four steps are not about order at all. Steps 2.2, 2.3, 2.6 and 2.7 of the
triangle inequality derive x ≤ |x| from |x| = x, which is reflexivity after a
rewrite. `inequalities` is being asked to substitute an equal term, which is
what `substitute` is for. The boundary between the two is not drawn anywhere.

**What this says.** `inequalities` is a decision procedure for linear
arithmetic over ordered fields, plus the negation laws, plus equality
rewriting. It is the most expensive of the four and the one to specify first.

## algebra needs a field normaliser, and one step exceeds its own boundary

Seventeen steps:

| what the step does | uses |
|---|---|
| ring normalisation, expanding or factoring | 6 |
| field operations with a nonzero side condition | 5 |
| identity and zero laws, as a = a·1 + b·0 | 3 |
| solve among several cited equations | 1 |
| prove a disequality | 1 |
| an exponent law | 1 |

Twelve of the seventeen cite no line at all. They are closed identities the
reader checks on their own, which is why `algebra` is the method most often
written bare.

Four steps carry a nonzero condition as a requires line, which the method's
expansion has to consume: clearing q from (p/q)² = 2, dividing 2q² = 4r² by 2,
and two divisions by 1 − a. So `algebra` takes hypotheses, and the "Not
settled" item in `SYNTAX.md` about whether it does is answered here: it
already does, visibly, in four places.

A fifth division is not paid for. Step 1.4.3 of the sum formula divides by 2
and states no condition, while step 3.10 of the √2 proof divides by 2 and
writes `requires 2 ≠ 0: arithmetic`. The same division is a dull fact in one
proof and invisible in the other. Whichever rule is chosen, these two must
agree.

The heaviest single step is Bezout's step 2, which produces
r = a·(u − q·x₀) + b·(v − q·y₀) from three cited equations at once. That is
substitution among equations followed by normalisation, not normalisation
alone.

Two steps sit outside the stated boundary.

- **Step 1 of the geometric series proves a disequality.** From a ≠ 1 it
  concludes 1 − a ≠ 0. That is not a ring identity, and `algebra` is described
  as applying identities.
- **Step 1.2.1.10 of the subsets proof is an exponent law.** It turns
  2^k + 2^k into 2^(k + 1). `SYNTAX.md` says `algebra` treats a named subterm
  as opaque and "will not turn a^(k + 1)·a into a^(k + 2)", which is the same
  law. The geometric series pilot cites `thm:exponent-step` for exactly this
  and its findings say plainly that exponent laws are theorems, not algebra.
  The two pilots disagree, and the subsets step is the one that is wrong. It
  should cite `thm:exponent-step` and leave `algebra` the step from 2·2^k.

**What this says.** `algebra` is a ring and field normaliser that consumes
nonzero hypotheses and can substitute among several cited equations. Its
stated boundary is right and the corpus breaks it once.

## arithmetic is three steps and one of them is not arithmetic

Three steps: 1 = 2^0, and 1 = 1(1 + 1)/2, both facts about closed numerals as
the rule says. The third is a^(0 + 1) = a, which contains a free variable. The
geometric series pilot justified it as treating the closed exponent as a
numeral computation, but the rule reads "a fact about closed numerals" and this
claim is not one.

Either the rule widens to cover a closed computation inside an otherwise
symbolic claim, or the step cites `thm:exponent-step` at m := 0 and lets
`arithmetic` handle 0 + 1 = 1. The second keeps the rule as written.

## What to do

1. **Fix the subsets exponent step**, which two pilots already disagree about.
   Then settle the two divisions by 2, one of which states a nonzero condition
   and one of which does not.
2. **Specify `inequalities` first.** It is 41% of the burden and the only one
   needing a decision procedure. Its negation laws are separable and dull and
   could be split off.
3. **Draw the boundary between `inequalities` and `substitute`**, which four
   steps currently straddle.
4. **Decide whether `arithmetic` may act inside a symbolic claim**, or narrow
   the one step that assumes it may.
5. **Consider splitting `lines`.** Eleven of its sixteen uses are bookkeeping
   forced by the shape of contradiction and case blocks, not reasoning.
