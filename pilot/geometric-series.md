# Pilot: the sum of a geometric series

Tenth pilot, first draft. Its purpose is a calculation chain in a theorem
that set.mm states in deduction form, with a `ph` context on every
hypothesis, and a second induction, this one from 0. Number 66 on
Wiedijk's list, `geoser` in set.mm.

The sum 1 + a + a² + ... + aⁿ is defined by recursion as G(n), as the
arithmetic series was, and the theorem is G(n) = (1 − a^(n + 1))/(1 − a).

Provisional forms, listed in the batch report: induction from 0 as in the
subsets pilot; the exponent rule a^(m + 1) = a^m·a cited as a theorem
rather than absorbed into `algebra`.

---

## Theorem geometric-sum

```
theorem geometric-sum
  let a ∈ ℝ                                                           (H1)
  assume a ≠ 1                                                        (H2)
  let n ∈ ℕ₀                                                          (H3)
  then G(n) = (1 − a^(n + 1))/(1 − a)

1.  1 − a ≠ 0
    algebra, from H2

2.  G(n) = (1 − a^(n + 1))/(1 − a)
    induction on n starting at 0, from H3

    base
    2.1.  G(0) = 1
          def:G

    2.2.  a^(0 + 1) = a
          arithmetic

    2.3.  1 = (1 − a)/(1 − a)
          algebra
          requires 1 − a ≠ 0: from 1

    2.4.  (1 − a)/(1 − a) = (1 − a^(0 + 1))/(1 − a)
          substitute a^(0 + 1) = a (line 2.2)

    2.5.  G(0) = (1 − a^(0 + 1))/(1 − a)
          calculation
            G(0) = 1                              2.1
                 = (1 − a)/(1 − a)                2.3
                 = (1 − a^(0 + 1))/(1 − a)        2.4

    step
    2.6.  For every k ∈ ℕ₀, if G(k) = (1 − a^(k + 1))/(1 − a)
          then G(k + 1) = (1 − a^((k + 1) + 1))/(1 − a).
          fix
          let k ∈ ℕ₀                                                  (K)
          assume G(k) = (1 − a^(k + 1))/(1 − a)                       (IH)

          2.6.1.  G(k + 1) = G(k) + a^(k + 1)
                  def:G n := k, from K

          2.6.2.  G(k) + a^(k + 1) = (1 − a^(k + 1))/(1 − a) + a^(k + 1)
                  substitute G(k) = (1 − a^(k + 1))/(1 − a) (IH)

          2.6.3.  a^((k + 1) + 1) = a^(k + 1)·a
                  thm:exponent-step m := k + 1, from H1
                  requires k + 1 ∈ ℕ₀: thm:nat0-closure, from K

          2.6.4.  (1 − a^(k + 1))/(1 − a) + a^(k + 1) = (1 − a^(k + 1)·a)/(1 − a)
                  algebra
                  requires 1 − a ≠ 0: from 1

          2.6.5.  (1 − a^(k + 1)·a)/(1 − a) = (1 − a^((k + 1) + 1))/(1 − a)
                  substitute a^((k + 1) + 1) = a^(k + 1)·a (line 2.6.3), right to left

          2.6.6.  G(k + 1) = (1 − a^((k + 1) + 1))/(1 − a)
                  calculation
                    G(k + 1) = G(k) + a^(k + 1)                         2.6.1
                             = (1 − a^(k + 1))/(1 − a) + a^(k + 1)      2.6.2
                             = (1 − a^(k + 1)·a)/(1 − a)               2.6.4
                             = (1 − a^((k + 1) + 1))/(1 − a)           2.6.5
```

---

## Database items

| pointer | statement | set.mm |
|---|---|---|
| def:G | Let a ∈ ℝ. G(0) = 1. Let n ∈ ℕ₀. G(n + 1) = G(n) + a^(n + 1). | (Σ over 0...n with fsum1 and fsump1) |
| thm:exponent-step | Let a ∈ ℝ, m ∈ ℕ₀. Then a^(m + 1) = a^m·a. | expp1 |
| thm:nat0-closure | Let k ∈ ℕ₀. Then k + 1 ∈ ℕ₀. | peano2nn0 |
| thm:geometric-sum | proved above | geoser |

---

## What the pilot reveals

1. **A requires line may cite a step.** At 2.3 and 2.6.4 the hypothesis
   1 − a ≠ 0 of the division is discharged by "from 1", a numbered step,
   rather than by a method of its own. SYNTAX.md says a requires line has
   "its own justification in the same forms"; citing a line is one of the
   forms, but this is the first time a requires line has done only that.
   It is right by the role rule, since step 1 exists for the sake of
   those two hypotheses and nothing else, which raises the question of
   whether step 1 should itself have been a requires line, written twice.
2. **Exponent laws are theorems, not algebra.** a^((k + 1) + 1) =
   a^(k + 1)·a is cited from thm:exponent-step, and `algebra` is used only
   after it, on an expression where the exponents are opaque symbols.
   This draws a line on the boundary of `algebra`: ring and field
   identities in the variables and named subterms, with no knowledge of
   what a^(k + 1) means. GOALS.md open question 6 asked how much algebra
   must do; this is the pilot's answer.
3. **a^(0 + 1) = a is arithmetic, not algebra.** Step 2.2 treats the
   closed exponent as a numeral computation. The line between
   `arithmetic` and `algebra` is: closed numerals against symbols.
4. **Deduction form is invisible.** set.mm's geoser has every hypothesis
   under `ph ->`. The readable statement has `let` and `assume` lines,
   and the elaborator supplies the context. Nothing in the text shows
   it, which is what READERS.md wanted, and this is the first pilot to
   confirm it on a deduction-form target.
5. **Two inductions from 0 now.** With the subsets pilot, two proofs use
   base P(0). Decided: the starting point is written on the method line,
   `induction on n starting at 0`, always, so that inductions from 2 or 4
   need no new form; SYNTAX.md's entry says so. Reading the base off the
   cited set was the rejected alternative.

Numbers, for the record: 14 numbered steps, 3 requires lines. set.mm's
geoser has 18 essential steps.
