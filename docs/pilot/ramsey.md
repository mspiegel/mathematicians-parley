# Pilot: Ramsey's theorem for two colours

Theorem 42 of `SELECTION.md`, Wiedijk #31. set.mm's `ramsey` is the
hypergraph form for any number of colours, proved by a recursion that is
not the reader's argument. The page proves the two-colour graph form with
the binomial bound, which needs no "least n":

  colour every pair of points of a finite V red (in E) or blue (in F); if
  |V| ≥ C(r + s − 2, r − 1), some r points have all their pairs red or some
  s points have all their pairs blue.

---

## Theorems

The proof is `proofs/wiedijk/ramsey.proof`, five theorems of 59 numbered
steps, 156 with those inside blocks. All five elaborate to
`corpus/elaboration/proofs/wiedijk/ramsey/`, assume nothing, and verify.

- `one-point-part`: a finite set with a point has a part of one point, all
  of whose pairs are in any given set, since it has no pairs.
- `two-point-parts`: a part of two points of W ∪ {v}, v ∉ W, lies in W or
  is {v, w} with w ∈ W.
- `grow-by-one`: if every point of N ⊆ X ∖ {v} is joined to v by a pair in
  E, a part W of N found for (k, j) gives one of X for (k + 1, j): W ∪ {v}
  where W's pairs are all in E, W itself where they are all in F.
- `ramsey-step`: the bounds for (k, j + 1) and (k + 1, j) give the bound
  for (k + 1, j + 1).
- `ramsey`: induction on r, and inside its step on s.

---

## Rendered view

**Lemma (ramsey-step).** Suppose every X ⊆ V with |X| ≥ C(k + j − 1, k − 1)
has k points with red pairs or j + 1 with blue, and every X with
|X| ≥ C(k + j − 1, k) has k + 1 red or j blue. Then every X with
|X| ≥ C(k + j, k) has k + 1 red or j + 1 blue.

*Proof.* C(k + j, k) ≥ 1, so X has a point v. Let R be the other points w
with {v, w} red and B the rest. |R| + |B| = |X| − 1 and, by Pascal's rule,
|X| ≥ C(k + j − 1, k) + C(k + j − 1, k − 1). If |R| < C(k + j − 1, k − 1),
then |R| + 1 ≤ C(k + j − 1, k − 1) and |B| ≥ C(k + j − 1, k). Inside R a part
for (k, j + 1) grows by v (grow-by-one). Inside B every pair {v, w} is blue,
since it is a pair of V and not red, and a part for (k + 1, j) grows by v
the same way, the lemma applied with the colours swapped. ∎

**Theorem (ramsey).** By induction on r and then on s. For r = 1 or s = 1
the bound is C(·, 0) = 1 or C(k, k) = 1, and one point does. The step is
ramsey-step, its bounds rewritten from the literal instances
C(k + (j + 1) − 2, k − 1) and C(k + 1 + j − 2, k + 1 − 1). ∎

---

## Database items

In `corpus/stdlib/counting.records`: `card-add-one` (`hashunsng`),
`card-two` (`hash2prd`), `card-positive` (`hashgt0n0`) and `binomial-nat`
(`bccl2`). In `corpus/stdlib/sets.records`: `set-builder-split` (`rabxm`)
and `set-builder-split-disjoint` (`rabnc`). In
`corpus/stdlib/reasoning.records`: `or-swap` (`pm1.4`). All mundane.

---

## What the pilot reveals

1. **Two colour sets make the step one lemma applied twice.** With E alone
   and blue meaning "not in E", the two halves of the step are mirror
   images, and the language has no "similarly". Naming both colours lets
   `grow-by-one` serve both halves, E and F swapped, at the price of two
   `or-swap` steps around the second use.
2. **A double induction is two nested `induction` blocks.** The inner one is
   the outer one's step, over "for all X ⊆ V", so the inductive hypotheses
   apply to the neighbourhoods R and B, which are parts of V.
3. **Literal instances need their arithmetic written.** P(k + 1) says
   C(k + 1 + (j + 1) − 2, k + 1 − 1); each index is rewritten by an `algebra`
   step and a `substitute`.
4. **A proof block whose assumption cannot hold may end "…, which is
   impossible".** The checker allowed it and the build did not; the build
   now does (`a-proof-block-ending-impossible`).
5. **A part's size is said back.** A letter over 𝒫X had no sort when a
   claim was said back, so |W| had no reading; a power set's members are
   sets (`a-part-counted-said-back`).
6. **Plain `inequalities` adds lines side by side.** Getting C(k + j − 1, k)
   ≤ |B| from |R| + 1 ≤ C(k + j − 1, k − 1) takes an `adding` row, a
   `transitivity` and a cancelling row.
