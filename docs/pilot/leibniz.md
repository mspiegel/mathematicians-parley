# Pilot: Leibniz's series for π

Theorem 49 of `SELECTION.md`, set.mm's `leibpisum`, Metamath 100 #26:

  Σ(k = 0 to ∞) (−1)^k/(2k + 1) = π/4.

set.mm proves it through the power series of arctan and Abel's theorem. The
page proves it through the integrals J(n) = ∫(0 to 1) t^(2n)/(1 + t²) dt.

---

## Theorems power-integral to leibniz

The proof is `proofs/wiedijk/leibniz.proof`, seven theorems. All elaborate
to `corpus/elaboration/proofs/wiedijk/leibniz/`, assume nothing, and verify.

Numbers: `power-integral` is 46 steps, `integrand-continuous` 26,
`integral-of-arctan-derivative` 35, `integral-recurrence` 32,
`integral-bounds` 39, `series-remainder` 19, `leibniz` 29.

---

## Rendered view

Let J(n) = ∫(0 to 1) t^(2n)/(1 + t²) dt.

1. J(0) = arctan(1) − arctan(0) = π/4, since arctan′(t) = 1/(1 + t²).
2. J(n) + J(n + 1) = ∫(0 to 1) t^(2n) dt = 1/(2n + 1), so
   J(n + 1) = 1/(2n + 1) − J(n).
3. By induction, π/4 − Σ(k = 0 to n) (−1)^k/(2k + 1) = (−1)^(n + 1)·J(n + 1).
4. 0 ≤ J(n + 1) ≤ ∫(0 to 1) t^(2n + 2) dt = 1/(2n + 3), so the partial sums
   come within any ε > 0 of π/4 and stay there.

∎

---

## Database items

Fifteen records, each with its lemma in `proved.mm`. In
`corpus/stdlib/calculus.records`: `continuous-constant`,
`continuous-power`, `continuous-scaled`, `continuous-quotient`,
`derivative-power`, `derivative-scaled`, `integral-difference`,
`integral-order` and `integral-nonneg`, which a proof names, and the mundane
`series-sum-from-zero`. In `corpus/stdlib/trigonometry.records`:
`continuous-arctan` and `derivative-arctan`, which a proof names, and the
mundane `arctan`, `arctan-values` and `arctan-real`.

---

## What the pilot reveals

1. **An equation carried into an integrand.** Rewriting the integrand of
   ∫(a to b) under its letter's membership of [a, b] is a congruence the
   build had not had; it is the lemma `gditgeq3d`.

2. **Tool faults met on the way.** A requires line said of every member of
   an interval has the member real; a divisor is said nonzero in either
   spelling of a square; a theorem of the same file stated over a define is
   compared in the standard spelling; and the build makes a step that cites
   a define standing inside one side of the claim.
