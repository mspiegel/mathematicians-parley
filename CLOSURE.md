# What the closure methods have to do

Open question 6 in `GOALS.md` asks how much "by algebra" must carry. This
answers it from the corpus rather than from intuition. `parley/check.py` accepts
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

## join, which was called lines, is nearly free and hid three real inferences

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

**What this says, and what was done.** No propositional decision procedure is
needed. The method was split: the three real inferences became cited theorems,
`thm:double-negation` twice and `thm:disjunctive-syllogism` once, joining the
two logical items the database already had. The thirteen remaining uses do one
thing and the method is now called `join`, which says so. `METHODS.md`
specifies it and records the criterion for where the line falls: a move needs a
pointer when it is a choice among logics, not when it is the meaning of a
connective.

The old name is the reason this went unnoticed for ten pilots. `lines` named
its arguments, and a method named for its inputs makes no claim about what it
does, so four unrelated jobs collected under it without anything objecting.

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
| ring normalisation, expanding or factoring | 7 |
| field operations with a nonzero side condition | 5 |
| identity and zero laws, as a = a·1 + b·0 | 3 |
| solve among several cited equations | 1 |
| prove a disequality | 1 |

Twelve of the seventeen cite no line at all. They are closed identities the
reader checks on their own, which is why `algebra` is the method most often
written bare.

Five steps carry a nonzero condition as a requires line, which the method's
expansion has to consume: clearing q from (p/q)² = 2, two divisions by 2, and
two by 1 − a. So `algebra` takes hypotheses, and the "Not settled" item in
`SYNTAX.md` about whether it does is answered here: it already does, visibly,
in five places.

One step still sits outside the stated boundary. Step 1 of the geometric series
concludes 1 − a ≠ 0 from a ≠ 1. That is not a ring identity, and `algebra` is
described as applying identities. Either the description widens to cover
disequalities, or the step cites a theorem.

The heaviest single step is Bezout's step 2, which produces
r = a·(u − q·x₀) + b·(v − q·y₀) from three cited equations at once. That is
substitution among equations followed by normalisation, not normalisation
alone.

**What this says.** `algebra` is a ring and field normaliser that consumes
nonzero hypotheses and can substitute among several cited equations. Its
stated boundary, that a named subterm stays opaque, is right: every claim above
respects it once the exponent law is cited rather than assumed.

## arithmetic is three steps and eighteen requires lines

1 = 2^0, 1 = 1(1 + 1)/2, and 0 + 1 = 1. All three are facts about closed
numerals, which is what the rule says and all it says.

Counting only step justifications undersells it. Eighteen further uses justify
a requires line, which makes it the commonest terminator of a dull fact in the
corpus, and thirteen of those are a numeral's membership of a number system.
That is no accident: requires lines do not nest, so whatever justifies one must
need nothing further, and `arithmetic` is the only method that cites nothing
and requires nothing. `METHODS.md` specifies it.

The third used to be a^(0 + 1) = a, which contains a free variable and is not
a fact about closed numerals. Unpacking it showed why the rule should stay
narrow: the claim needs 0 + 1 = 1, which is arithmetic, and then that a^1 is a,
which is an exponent law. Letting `arithmetic` swallow the whole claim let an
exponent law in by the back door, in the very pilot whose findings say that
exponent laws are theorems. The proof now spends four steps and cites
`thm:exponent-one`.

## What to do

All four closure methods are now specified in `METHODS.md`, which was what
open question 6 in `GOALS.md` asked for. What is left on this list is not about
them:

1. **Specify the nine remaining methods.** The citation form, three of the four
   block methods, and `substitute`, `instantiate`, `obtain` and `exhibit`. None
   is a decision procedure, so each should be shorter than these four were.
   `contradiction` is written, and it is the first with two accepted shapes:
   the supposition is the claim negated, or the claim is the supposition
   negated, and which one it is decides whether the expansion needs the
   classical step.

The membership sweep is done. `READERS.md` settles that membership in a number
system is a written dull fact and merits no exception, and the corpus now
carries 97 such lines across the 42 steps that cite `algebra` or
`inequalities`. Five database items had to be added before any of them could be
written, and three facts needed numbered steps rather than requires lines.

The sweep wrote the lines; it did not check that what they cite covers them.
Doing that found two more gaps, both now closed. `thm:int-closure` stated
`a + b ∈ ℤ` and `a·b ∈ ℤ` but neither `a − b ∈ ℤ` nor `a² ∈ ℤ`, and seven
requires lines across three proofs wanted one of those; the square stands in a
`then` group of its own, since it needs one integer where the rest need two.
And two steps leaned on a numeral's membership without writing it, which is
the thing the sweep exists to prevent.

A requires line names a principle rather than one use of it. `2k² + 2k ∈ ℤ`
cites `thm:int-closure` once where the kernel applies it three times, and the
line a reader wants is the one the corpus writes. So the check applies the
cited item to what the line supplies, and to whatever that then asks for, and
admits nothing else. Writing each application as its own line would have put
four requires lines on one step and made the proof worse for the reader it is
for.

Three earlier items are done. `inequalities` and `algebra` are specified in
`METHODS.md`, the first as linear arithmetic over an ordered field and the
second as equality of rational expressions over a field. Specifying the first
settled its boundary against `substitute`, which needs a line to rewrite and is
syntactic, while `inequalities` uses an equation as one linear fact among
others. Specifying the second settled whether `algebra` may prove a
disequality: it may, but only when the claim is a nonzero multiple of a cited
one, which is the single use in the corpus.

Three earlier items are done. The subsets step now cites the exponent law that
`algebra` was being asked to know; the sum formula now states the nonzero
condition for its division by 2, as the √2 proof already did; and the
geometric series base case no longer hides an exponent law inside
`arithmetic`. The corpus costs five steps and one database item more than it
did, and no longer contradicts its own documents.
