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

The skeleton is `proof/geometric-series.proof`. The items it cites are in
`db/`.

---

## Database items

This pilot introduced `def:G`, `thm:exponent-step`, `thm:nat0-closure` and
`thm:geometric-sum` in `db/items.db`, and the G row in `db/notation.db`. The
table that used to stand here was merged into those files; `DATABASE.md`
records what the merge decided.

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
3. **a^(0 + 1) = a is two facts, not one.** The base case needs the literal
   instance a^(0 + 1), and reaching a from it takes 0 + 1 = 1, which is
   arithmetic, and then a^1 = a, which is an exponent law. Writing the whole
   claim as one `arithmetic` step let an exponent law in by the back door,
   contradicting finding 2 above within this same file. The base case now
   spends four steps and cites `thm:exponent-one`. The line between
   `arithmetic` and `algebra` is closed numerals against symbols, and neither
   of them knows what an exponent means.
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

Numbers, for the record: 17 numbered steps, 3 requires lines. set.mm's
geoser has 18 essential steps.
