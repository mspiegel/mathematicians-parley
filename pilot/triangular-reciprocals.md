# Pilot: the sum of the reciprocals of the triangular numbers

Theorem 13 of `SELECTION.md`, set.mm's `trirecip`, Metamath 100 #42:

  1/1 + 1/3 + 1/6 + 1/10 + … = 2.

The first limit of a sequence in the corpus and the first sum over all of ℕ.
The partial sums telescope to 2 − 2/(n + 1), and an ε–N argument shows they
tend to 2. The intermediate value theorem made the ε–δ argument for a
function at a point; this makes the ε–N argument for a sequence as n grows,
where the input approaches no point and δ becomes a threshold N.

---

## Theorem triangular-reciprocals

The proof is `proof/triangular-reciprocals.proof`. It elaborates to
`elaboration/proof/triangular-reciprocals/triangular-reciprocals.mm`, which
assumes nothing and verifies.

---

## Rendered view

T(k) = k(k + 1)/2 is the k-th triangular number, for k ∈ ℕ.

**Theorem.** Σ(k = 1 to ∞) 1/T(k) = 2.

*Proof.*

1. For every k ∈ ℕ, 1/T(k) = 2/k − 2/(k + 1). By the definition of T, then
   algebra.
2. For every n ∈ ℕ, Σ(k = 1 to n) 1/T(k) = 2 − 2/(n + 1). The terms are
   rewritten by line 1 inside the sum, and the sum telescopes.
3. Every 1/T(k) is real, and 4. every partial sum is real.
5. For every ε > 0 there is N ∈ ℕ with, for every n ≥ N,
   |Σ(k = 1 to n) 1/T(k) − 2| < ε. Take N with 1/N < ε/2 (Archimedean);
   for n ≥ N, N ≤ n + 1, so 1/(n + 1) ≤ 1/N, and by line 2 the partial sum
   is within 2/(n + 1) ≤ 2/N < ε of 2.
6. So the partial sums tend to 2, by the definition of a limit.
7. So the series is 2, since a series is the limit of its partial sums.

∎

---

## Database items

In `db/notation.records`: `series`, Σ(k = a to ∞), and `tends-to`,
"x(n) → L as n → ∞", a relation rather than an operator — set.mm's `~~>`.

In `stdlib/`: `definition tends-to` and `theorem series-value` (calculus);
`archimedean`, `quotient-real`, `reciprocal-positive` and `reciprocal-order`
(numbers); `sum-telescopes` and `range-nat` (sums).

In `elaboration/stdlib/proved.mm`, proved below the readable layer by
`elaboration/stdlib/proofs_series.py`: `climnnre`, the target of
`tends-to`, and `sersumlim`, the target of `series-value`.

---

## What the pilot reveals

1. **The definition of a limit had to be proved, not cited.** set.mm's
   `clim2` says a sequence tends to L over ℝ⁺, over an upper integer set,
   with every term complex, and it names its index apart from the sequence
   it reads. The page writes the sequence as a rule in n, which set.mm
   holds as a map binding n, so `clim2` cannot read it at all. `climnnre`
   says the limit as the page does and is proved from `rlimclim`, `rlim2`,
   `ralrp` and `rexuzre`. It is the second family of lemmas this corpus
   proves below the readable layer, after geometry, and the two now share
   one script and one file.

2. **The value of a series is a join.** A textbook defines Σ(k = 1 to ∞)
   t(k) as the limit of the partial sums. set.mm defines an infinite sum
   through a sequence of its own, and no label says the textbook's form.
   `sersumlim` does, from `isumclim3` and `climuni`. The last step of the
   proof is a citation of that join, which is where it belongs: it is the
   definition, not an argument.

3. **T is defined once, above the theorem.** The statement reads as a
   textbook states it, with T in it. What set.mm is asked to prove writes T's
   rule out, and the proof's last line, about T, is carried to the statement
   by rewriting T(k) to its rule inside the infinite sum — which holds only
   for k in T's domain, so the rewrite goes under the sum's range.

4. **A lemma may name its summand only in its hypotheses.** `telfsum`
   concludes about the summand at j, at j + 1 and at the ends, and names the
   summand itself nowhere in its conclusion. The claim fixes the four values;
   the summand is read back from them, in a letter the lemma keeps apart.

5. **Reciprocals are atoms of the inequality method.** `inequalities` knew
   ε/2 as half of ε, and knew nothing about 2/(n + 1). The argument needs
   2/(n + 1) to be twice 1/(n + 1), and a first draft said so in a line of
   its own. `METHODS.md` now reads a numeral over a term as the numeral times
   the term's reciprocal, which removed that line. What a reader states
   anyway stays on the page: 1/(n + 1) ≤ 1/N and 1/(n + 1) > 0 are cited
   facts about reciprocals, not arithmetic.

   Reading every fact in the normaliser's standard form first was
   considered, to have one meaning of "the same expression". It does not
   work: the normaliser writes 2/(n + 1) − 1/N as one fraction, and the
   atoms the argument needs are gone.

6. **The inequality method wrote only the shapes the corpus had met.**
   The ε–N step combines three facts, two of them scaled by 2, and small
   steps like "k ≥ 1, so k ≠ 0" leave a number over. Both were decided and
   not written, and were taken as stated. `ELABORATION.md` now describes the
   general combination, which runs where the shapes before it decline, so
   no existing proof changed.

7. **Realness is said whole where a function hypothesis cannot be taken
   apart.** `series-value` asks every term to be real, and a term 1/T(k)
   holds no name a membership could be asked of. The page says it whole —
   "for every k ∈ ℕ, 1/T(k) ∈ ℝ" — and the checker and elaborator both read
   that as the function hypothesis said once. Line 3 still derives it in
   numbered steps through 2/k and 2/(k + 1), because a line whose claim is a
   membership is proved by citing items, not by a method.

8. **An obtained name can be the letter the goal binds.** Line 5 obtains N
   from "there is N ∈ ℕ with 1/N < ε/2" inside a block claiming "there is
   N ∈ ℕ with …". Both "there is" lines bind N, so the obtained N and the
   claim's N are one letter, and the lemmas that close the block and exhibit
   the witness keep those apart. Each renames the claim to a letter nothing
   holds and back.

9. **Rules the elaborator follows are written down first.** Growing the
   elaborator for this proof is what `GOALS.md` decisions 15 to 17 were
   written for: each rule is stated in `ELABORATION.md` or `METHODS.md` as
   mathematics, each has this proof as its test, and no step is taken as
   stated.

Numbers, for the record: 49 numbered steps and 41 requires lines, against
set.mm's 42 essential steps for `trirecip`. The requires lines are the price
`READERS.md` records for writing dull facts down, and an ε–N argument over
reciprocals is dense in them: every atom's realness and every divisor's
disequality is written. The elaborated proof is 100 KB in compressed form
and about 96 million labels written out.
