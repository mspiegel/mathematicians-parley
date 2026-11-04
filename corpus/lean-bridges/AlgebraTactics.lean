module

public import Mathlib
public import Tactics

/-!
# What an `algebra` step leaves to the ring and field tactics

`parley_ring` closes an identity of `algebra` with no line cited, and
`parley_field` what `linear_combination` asks of one that divides; each
clears the divisions with `parley_clear` when `ring1` alone does not close
it. A generated file imports this module only when it calls one of them.
-/

public section

/-- Clears what an `algebra` step divides by, from the lines saying each
divisor is not 0, a product, a quotient or a negation not 0 taken as each
of its parts not 0. A natural number above 0, the q of p/q, is not 0. -/
macro "parley_clear" : tactic =>
  `(tactic| ((try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or,
      pow_eq_zero_iff, Nat.pos_iff_ne_zero] at *) <;> (try cases_type* And) <;> field_simp))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
macro "parley_ring" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A factorial divided by itself, which is not 0.
    | (field_simp [LeanBridges.Counting.factorial, Nat.factorial_ne_zero]; done)
    | (simp only [inv_inv, one_div, div_div, div_pow] <;> ring1; done)
    | (parley_clear <;> ring1; done)
    | (parley_clear; done))

/-- What `linear_combination` asks once the cited equations are subtracted,
where the step divides: zero, once the divisions are cleared. -/
macro "parley_field" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    -- A divisor said not 0 in its own least type, 3 * (n : ℤ) - 1 ≠ 0, and
    -- divided by in ℝ, written the other way round, ↑n * 3 - 1: the facts
    -- cast up and both normalised, field_simp sees they are one.
    | ((try rify at *); ring_nf at *; field_simp; ring1; done)
    -- Divisors field_simp does not clear, 3n − 1 beside a fact that says it
    -- is not 0: the fractions are joined and multiplied out one at a time,
    -- each divisor shown not 0 from the facts.
    | ((try push_cast at *); (try rify at *);
        simp (disch := simp_all) only [div_add_div, div_sub_div, div_eq_div_iff, eq_div_iff,
          div_eq_iff, mul_one_div, mul_div_assoc', div_mul_eq_mul_div, div_add', add_div',
          div_sub', sub_div']; ring1; done)
    | (parley_clear <;> ring1; done))

end
