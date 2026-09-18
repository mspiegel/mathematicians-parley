# Pilot: |a + b| ≤ |a| + |b|

The third pilot, written to `SYNTAX.md`. Its purpose is to exercise proof
by cases, the first method after induction to divide its block into named
parts, and a definition whose unfolding branches, since |x| is defined by
cases on the sign of x. The theorem is the triangle inequality for real
numbers, number 91 on Wiedijk's list and `abstri` in set.mm.

Two forms were introduced here and are now settled in `SYNTAX.md`: the
`cases` justification with its `case` parts, and the rule that a
calculation only joins, its lines citing numbered steps, with = and ≤
mixed in one chain.

The main theorem uses a lemma, x ≤ |x| and −x ≤ |x|, which is proved
first and is itself by cases.

---

## Theorem abs-bounds

```
theorem abs-bounds
  let x ∈ ℝ                                                           (H1)
  then x ≤ |x|. −x ≤ |x|.

1.  x ≥ 0 or x < 0
    thm:nonneg-or-neg x := x, from H1

2.  x ≤ |x|. −x ≤ |x|.
    cases, from 1

    case
    assume x ≥ 0                                                      (C1)

    2.1.  |x| = x
          def:abs x := x, from H1, C1

    2.2.  x ≤ |x|
          inequalities, from 2.1

    2.3.  −x ≤ |x|
          inequalities, from 2.1, C1

    2.4.  x ≤ |x|. −x ≤ |x|.
          lines 2.2, 2.3

    case
    assume x < 0                                                      (C2)

    2.5.  |x| = −x
          def:abs x := x, from H1, C2

    2.6.  −x ≤ |x|
          inequalities, from 2.5

    2.7.  x ≤ |x|
          inequalities, from 2.5, C2

    2.8.  x ≤ |x|. −x ≤ |x|.
          lines 2.6, 2.7
```

---

## Theorem triangle-inequality

```
theorem triangle-inequality
  let a ∈ ℝ                                                           (H1)
  let b ∈ ℝ                                                           (H2)
  then |a + b| ≤ |a| + |b|

1.  a + b ∈ ℝ
    thm:real-closure, from H1, H2

2.  a + b ≥ 0 or a + b < 0
    thm:nonneg-or-neg x := a + b, from 1

3.  a ≤ |a|. −a ≤ |a|.
    thm:abs-bounds x := a, from H1

4.  b ≤ |b|. −b ≤ |b|.
    thm:abs-bounds x := b, from H2

5.  |a + b| ≤ |a| + |b|
    cases, from 2

    case
    assume a + b ≥ 0                                                  (C1)

    5.1.  |a + b| = a + b
          def:abs x := a + b, from 1, C1

    5.2.  a + b ≤ |a| + |b|
          inequalities, from 3, 4

    5.3.  |a + b| ≤ |a| + |b|
          calculation
            |a + b| = a + b                 5.1
                    ≤ |a| + |b|             5.2

    case
    assume a + b < 0                                                  (C2)

    5.4.  |a + b| = −(a + b)
          def:abs x := a + b, from 1, C2

    5.5.  −(a + b) = −a + −b
          algebra

    5.6.  −a + −b ≤ |a| + |b|
          inequalities, from 3, 4

    5.7.  |a + b| ≤ |a| + |b|
          calculation
            |a + b| = −(a + b)              5.4
                    = −a + −b               5.5
                    ≤ |a| + |b|             5.6
```

---

## Rendered view of triangle-inequality

**Theorem triangle-inequality.** Let a and b be real numbers. Then
|a + b| ≤ |a| + |b|.

*Proof.*

1. a + b ∈ ℝ.
   By the theorem real-closure, from the hypotheses a ∈ ℝ and b ∈ ℝ. That
   theorem states: let x and y be real numbers; then x + y ∈ ℝ.

2. a + b ≥ 0 or a + b < 0.
   By the theorem nonneg-or-neg, with a + b as x, from line 1. That
   theorem states: let x be a real number; then x ≥ 0 or x < 0.

3. a ≤ |a|. −a ≤ |a|.
   By the theorem abs-bounds, with a as x, from the hypothesis a ∈ ℝ. That
   theorem states: let x be a real number; then x ≤ |x|, and −x ≤ |x|.

4. b ≤ |b|. −b ≤ |b|.
   By the theorem abs-bounds, with b as x, from the hypothesis b ∈ ℝ.

5. |a + b| ≤ |a| + |b|.
   By cases, from line 2.

   Case 1. Assume a + b ≥ 0.

   5.1. |a + b| = a + b.
        By the definition of |x| with a + b as x, from line 1 and the case
        assumption. That definition states: let x be a real number; if
        x ≥ 0 then |x| = x; if x < 0 then |x| = −x.

   5.2. a + b ≤ |a| + |b|.
        By the rules for inequalities, from lines 3 and 4.

   5.3. |a + b| ≤ |a| + |b|.
        Calculation:
        |a + b| = a + b, by line 5.1,
        ≤ |a| + |b|, by line 5.2.

   Case 2. Assume a + b < 0.

   5.4. |a + b| = −(a + b).
        By the definition of |x| with a + b as x, from line 1 and the case
        assumption.

   5.5. −(a + b) = −a + −b.
        By algebra.

   5.6. −a + −b ≤ |a| + |b|.
        By the rules for inequalities, from lines 3 and 4.

   5.7. |a + b| ≤ |a| + |b|.
        Calculation:
        |a + b| = −(a + b), by line 5.4,
        = −a + −b, by line 5.5,
        ≤ |a| + |b|, by line 5.6.

∎

---

## Database items

Items already listed in the earlier pilots (`arithmetic`, `algebra`,
`inequalities`, `lines`, `calculation`, the symbols) are not repeated. The
symbol |x| is new.

| symbols | what they are | set.mm |
|---|---|---|
| \|x\| | absolute value | cabs |
| −x | negation | cneg |

| pointer | statement | set.mm |
|---|---|---|
| def:abs | Let x ∈ ℝ. If x ≥ 0 then \|x\| = x. If x < 0 then \|x\| = −x. | absid, absnid (set.mm defines abs on ℂ by df-abs; these two theorems are the real case) |
| thm:nonneg-or-neg | Let x ∈ ℝ. Then x ≥ 0 or x < 0. | 0re, lelttric |
| thm:real-closure | Let x ∈ ℝ, y ∈ ℝ. Then x + y ∈ ℝ. | readdcl |
| thm:abs-bounds | proved above | leabs, absneg |
| thm:triangle-inequality | proved above | abstri (over ℂ) |

Methods.

| pointer | what the reader checks | set.mm |
|---|---|---|
| cases, from L | L claims "P or Q"; the block has one `case` part per disjunct, in order; each part opens with `assume` of its disjunct, labelled, and its last step claims the same formula as the step above the block | jaodan, jaoi |
| calculation, with ≤ | every line cites a numbered step stating that line's relation; where the chain mixes = with ≤ or <, the claim's relation is ≤ if every line is = or ≤, and < if any line is < | eqbrtrd, lelttrd, ... |

---

## What the pilot reveals

1. **Cases is a block with one part per disjunct.** The `case` marker
   works exactly as `base` and `step` did, with one difference: a case
   part carries its own assumption, so the marker is followed by an
   `assume` line with a label, and the sub-steps under it may cite that
   label. The disjunction being split is a cited line, here line 2 or
   line 1, not something the method finds on its own. Each part's last
   step repeats the claim of the step above the block, as the induction
   step repeated P(k + 1), so the reader checks the parts against one
   formula. Three alternatives were considered and rejected: repeating
   the disjunction on the method line; a marker carrying the formula and
   label, as `case a + b ≥ 0 (C1)`; and a `cases` step with no claim of
   its own. The form is now in `SYNTAX.md`.
2. **A definition may branch.** |x| is defined by two conditional
   sentences. Citing it with the condition's line in `from`, as at 2.1
   with C1, yields the consequent of that branch. This is a new use of
   `from`: the cited line does not discharge a `let` or `assume`
   hypothesis of the item but selects one of its sentences. It reads
   naturally, and the elaborator can check it. `SYNTAX.md` now states it
   as a convention at every citation: given a line stating A, a
   conditional sentence "if A then B" of the cited item yields B. Naming
   the branch with a keyword was considered and rejected.
3. **A calculation only joins, and may mix = and ≤.** Steps 5.3 and 5.7
   are chains whose lines are equalities and one inequality, each citing
   the numbered step that established it, and whose claim is the
   inequality between first and last term. This is decision 7 of
   `GOALS.md` in practice. The first draft put the methods on the chain
   lines themselves, as the earlier pilots did for equalities, so that
   each case was one block. Reviewing it settled the rule the other way
   for every chain: all reasoning is in numbered steps, and the chain is
   the reader's view of how they join, with its relation read off its
   lines. The two earlier pilots were rewritten to match. The
   elaborator's target is the family of mixed transitivity lemmas.
4. **A two-sentence line is cited for one of its sentences.** Line 3
   claims "a ≤ |a|. −a ≤ |a|." and is cited by 5.2 for its first sentence
   and by 5.6 for its second. This is the open item from the √2 pilot
   about whether a line number names one formula or several, now with a
   real use: the citation is by line, and which sentence is used is left
   for the reader to see, as it is when a theorem's conclusion has two
   sentences. It worked without strain here. If a later pilot cites a
   line with many sentences, a way to name one, such as "3.2" for the
   second sentence of line 3, may be wanted.
5. **A theorem's conclusion may be several sentences.** abs-bounds
   concludes "x ≤ |x|. −x ≤ |x|.", and its proof's last step in each case
   states both. The `then` line follows the same rule as a claim.
6. **The case steps repeat the block's claim.** Steps 5.3 and 5.7 both
   claim |a + b| ≤ |a| + |b|, as step 5 does. This is the same repetition
   noted for the one-step proof of the induction pilot, now occurring
   twice in one block. It is the price of every part ending in a step
   with a claim. Lamport's proofs have the same shape, with a QED step
   closing each case.
7. **`inequalities` has the same unstated hypotheses as `algebra`.**
   Steps 2.2, 2.3, 2.6 and 2.7 of abs-bounds and 5.2 and 5.6 here apply
   the rules for inequalities to real numbers, and the requires lines for
   "x is a real number" are not written. The "Not settled" item in
   `SYNTAX.md` now names `inequalities` beside `algebra`.
8. **Step 1 exists only to feed step 2.** a + b ∈ ℝ is a hypothesis of
   nonneg-or-neg and of def:abs, and it is proved as a numbered step
   rather than as a requires line because it is cited three times. By the
   role rule it is not a dull fact, since its use is not only to discharge
   one item's hypothesis, but it reads like one. The rule holds; the
   reading is a consequence of it.
9. **set.mm's absolute value is not defined by cases.** df-abs defines
   |x| on ℂ as √(x·x̄), and the two branches for reals are the theorems
   absid and absnid. So def:abs in this language elaborates to a pair of
   theorems, not to a definition. The pointer is still called def:abs
   because that is what it is to Reader A, and decision 12 of `GOALS.md`
   about checked definitions applies to the language's definitions, not
   set.mm's.
10. **The kernel proof will differ from set.mm's.** abstri is proved over
    ℂ through the complex absolute value in 78 essential steps. This
    text elaborates to a proof over ℝ by cases. As with √2, the archive
    will hold two proofs of statements that differ, since set.mm's is
    the ℂ version and this is its restriction to ℝ.

Numbers, for the record: abs-bounds has 10 numbered steps and 0 requires
lines; triangle-inequality has 12 numbered steps and 0 requires lines.
set.mm's abstri has 78 essential steps.
