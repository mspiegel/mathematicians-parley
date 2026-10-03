# Pilot: Cauchy–Schwarz for finite sums

Theorem 26 of `SELECTION.md`, Wiedijk #78:

  (Σ aₖbₖ)² ≤ (Σ aₖ²)(Σ bₖ²) for real a₁, …, aₙ and b₁, …, bₙ.

set.mm's `csbren` says it of finite sums over any finite index set, in
deduction form. The proof here is the textbook one: Σ(aₖt + bₖ)² is never
negative, and it is a quadratic in t, so at its lowest point it says the
inequality.

---

## Theorems expand and cauchy-schwarz

The proof is `proofs/cauchy-schwarz.proof`, two theorems. `expand`
multiplies the quadratic out, 13 numbered steps, 16 with those inside its
block. `cauchy-schwarz` is 9 numbered steps, 48 with those inside its
blocks. Both elaborate to `corpus/elaboration/proofs/cauchy-schwarz/`,
assume nothing, and verify.

---

## Rendered view

**Theorem (expand).** Let n ∈ ℕ, a, b : {1, …, n} → ℝ and t ∈ ℝ. Then
Σ(aₖt + bₖ)² = t²·Σaₖ² + 2t·Σaₖbₖ + Σbₖ².

*Proof.* Multiply out each term and split the sum. ∎

**Theorem (Cauchy–Schwarz).** Let n ∈ ℕ and a, b : {1, …, n} → ℝ. Then
(Σaₖbₖ)² ≤ (Σaₖ²)(Σbₖ²).

*Proof.* For every real t, t²·Σaₖ² + 2t·Σaₖbₖ + Σbₖ² = Σ(aₖt + bₖ)² ≥ 0.
Σaₖ² ≥ 0 since each square is, so either it is 0 or it is positive.

If Σaₖ² = 0, every aₖ² is 0, so every aₖ is 0, so Σaₖbₖ = 0 and both sides
are 0.

If Σaₖ² > 0, write A = Σaₖ², B = Σaₖbₖ and C = Σbₖ². At t = −B/A the
quadratic is C − B²/A ≥ 0, so B²/A ≤ C, and multiplying by A > 0 gives
B² ≤ AC. ∎

---

## Decisions made with the reader

1. **The sums run from 1 to n**, with a and b functions on {1, …, n}, as a
   textbook indexes a list. set.mm's index set is any finite set.
2. **The case Σaₖ² = 0 is a case on the page.** A textbook often waves it
   through; here it is the second of three cases, the first (Σaₖ² < 0)
   refused at once.
3. **The discriminant step is on the page**: the quadratic at t = −B/A, then
   multiplied by A > 0, rather than a library item saying a quadratic that
   is never negative has a discriminant that is not positive.

---

## What the pilot reveals

1. **A sum lemma pushed to an outer frame knew too little.** set.mm's sum
   lemmas keep their index out of the scope, so under the case Σaₖ² = 0,
   which names k, `sumeq2dv` and `fsum00` were proved one frame out, where
   the lines written inside the case are not. The lemma is now first proved
   in the innermost frame over a letter nothing holds and renamed back, and
   an antecedent the outer frame cannot settle is discharged once what is
   built is carried in (`ELABORATION.md`, Scopes). A planted case had held
   this up as a defect the elaborator reports: the step it planted is
   sound, and a test proof (`tests/elaborator/sum-letter-in-scope.proof`)
   now has it as its conclusion, so the gate verifies the renamed proof.
2. **A frame's facts were those it opened with.** A frame widened by a
   `fix` now takes the facts known when the `fix` opens, so lines written
   in a case before it are there for a lemma proved in the case's frame.
3. **`expand` is a theorem of its own,** as `binomial-step` is: the sum
   algebra, stated where no hypothesis names the sum's index.
4. **A function's value is a number from its type.** a(k) ∈ ℝ where
   a : {1, …, n} → ℝ and k is in the range, inside a membership, is
   `ffvelcdm` from the `let` line (`function_value`); and a claim a line
   says of every index is read at the letter a sum lemma moved to
   (`instance_of_universal`).
5. **A define inside a case is the case's.** A, B and C are named only
   where Σaₖ² > 0. A define is now read after its case is entered.
6. **A defined name's membership is read as the claim is.** `membership`
   reads A as the sum it stands for, so the facts A ∈ ℝ and A ≠ 0 are read
   the same way, and `same` does so wherever a define is in force.
7. **A biconditional was read on the wrong side.** `lemul2` says
   A ≤ B ↔ C·A ≤ C·B, and the claim A·(B²/A) ≤ A·C fits both sides; the
   near side won, as any inequality fits it. The side whose pattern fixes
   more constructors is now read. Reading the far side first instead broke
   `subsets`, where `ralrnmpt`'s near side is the right one, and the full
   build caught it.
8. **The algebra normaliser did not reach −(a/b),** and the gate caught
   the step taken as stated. It is now `divnegd`. Multiplying the
   denominators out then reached A⁷, and set.mm has no `7z`, so a power's
   exponent is in ℤ by `nnzi` from `7nn`. That and `function_value`
   changed six other files' proofs by one line each, and they verify.
9. **A defined name and its sum are two atoms to `inequalities`.** A > 0
   is not C3 written again: the page says A = Σaₖ², by D1, and cites it.
10. **Five mundane items:** square-nonneg (`sqge0`), square-zero
    (`sqeq0`), multiply-le (`lemul2`), sum-nonneg (`fsumge0`) and
    sum-zero-terms (`fsum00`).
