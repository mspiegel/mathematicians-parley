# Pilot: Cauchy–Schwarz for finite sums

Theorem 26 of `SELECTION.md`, Wiedijk #78:

  (Σ aₖbₖ)² ≤ (Σ aₖ²)(Σ bₖ²) for real a₁, …, aₙ and b₁, …, bₙ.

set.mm's `csbren` says it of finite sums over any finite index set, in
deduction form. The proof here is the textbook one: Σ(aₖt + bₖ)² is never
negative, and it is a quadratic in t, so at its lowest point it says the
inequality.

---

## Theorem cauchy-schwarz

The proof is `proofs/cauchy-schwarz.proof`, one theorem of 5 numbered steps,
30 with those inside its blocks. It elaborates to
`corpus/elaboration/proofs/cauchy-schwarz/`, assumes nothing, and verifies.

---

## Rendered view

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
3. **The quadratic is multiplied out in one step.** The first draft put it
   in a theorem of its own, `expand`, of 13 steps: the sum lemmas could not
   be used where a define's equation named the sum's index, and `algebra`
   took a sum for one atom, so each split (`sum-add`) and each constant
   taken out (`sum-scaled`) was a step, put in place by a `substitute`.
   The reader asked whether that was a fault of `sum-add` or of the
   implementation; it was `algebra`'s, which now reads a finite sum as
   linear (`METHODS.md`), and step 1.3 is `algebra`. Five other proofs'
   files change by one line each, and verify.
4. **A function's value is a number from its type.** a(k) ∈ ℝ where
   a : {1, …, n} → ℝ and k is in the range, inside a membership, is
   `ffvelcdm` from the `let` line (`function_value`); and a claim a line
   says of every index is read at the letter a sum lemma moved to
   (`instance_of_universal`).
   The first draft restated a(k) ∈ ℝ as a numbered step seven times, each
   `mun:function-value, from K`. The reader asked why the step could not
   use H2, which says it, and chose to cite the type with the domain line:
   `requires a(k) ∈ ℝ: from H2, K4`. A function's type is now cited for its
   values (`READERS.md`), and the seven steps are gone; so is
   `divisibility-by-three`'s 1.4 and `mean-value`'s 12.2.
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
9. **A defined name and its sum were two atoms to `inequalities`.** A > 0
   was not C3 written again, so the page said A = Σaₖ², by D1, and cited
   it. `inequalities` now reads a defined name as what it names in a step
   that writes both (`METHODS.md`), and A > 0 is `inequalities, from D1, C3`,
   the define cited because the step uses what A is.
   The quadratic at t = −B/A carried four `requires` lines, two sums and A
   and B real, for the comparison of its two spellings; `settle` now builds
   a sum's membership from its terms, and they are gone.
10. **Five mundane items:** square-nonneg (`sqge0`), square-zero
    (`sqeq0`), multiply-le (`lemul2`), sum-nonneg (`fsumge0`) and
    sum-zero-terms (`fsum00`).
11. **A "for all" with one step was a block of one step.** The reader asked
    why "for all k, a(k)² ≥ 0" needed a `fix` block, and chose to let such a
    step be one line: the item applied at a member (`SYNTAX.md`, a step said
    of every member). The reading is decided by what is cited, not tried one
    way then the other, which the reader asked for when the first draft did
    try. Three blocks here became lines, and eight elsewhere. Two of those,
    `euler` 19 and `harmonic` 1, first built proofs the verifier refused,
    and each showed a fault in reading a cited line's bound letters that the
    blocks had hidden: a lemma's letter kept apart from another the claim
    fixed was not given a fresh one (`gfprodrp`'s x and k), and a cited
    corpus theorem's conclusion was taken for a claim over other letters
    without renaming the two. Both are fixed, and three other proofs'
    files changed by a few lines and verify.
12. **The sums' memberships were steps of their own.** Three steps said
    each sum is real and a fourth joined them, for the requires lines of
    the cases to cite. They were dull facts written apart from the steps
    they serve, against `READERS.md`, and were there because a `requires`
    line inside the case Σaₖ² = 0 was proved outside it. With that fixed,
    each step that needs a sum real says so where it needs it, by
    `membership`, and the four steps are gone. The case Σaₖ² > 0 had six
    more: A, B and C real, A ≠ 0, and −B/A and B²/A real. They are
    `requires` lines now. `membership` builds a sum from its terms as the
    lookup does, and takes A > 0 for A ≠ 0 as a divisor asks, which is how
    a reader reads it; A ≠ 0 elsewhere is `inequalities, from` A > 0.
