module

public import Mathlib

/-!
# Tactics the generated proofs use

Each closes a goal of one kind the page leaves to its reader, and is named
for that kind, so a generated proof says what it asks and the search for
how is written once, here. Every alternative closes the goal or fails:
`ring`, `norm_num` and `apply` can succeed while leaving a goal open, so
each alternative ends in `done`, and `ring1` is used for `ring`.
-/

public section

/-- What a page leaves to its reader: a side condition of a cited item, a
membership said once, a line restated or joined from lines above, or a
block's last line taken as what the block owes. The lines above are taken
apart at each "and" first. -/
macro "parley_side" : tactic =>
  `(tactic| ((try cases_type* And) <;> first
    | (assumption; done)
    | (apply Eq.symm; assumption; done)
    | (apply Ne.symm; assumption; done)
    | (constructor <;> assumption; done)
    | (positivity; done)
    | (omega; done)
    | (linarith; done)
    | (intro _; linarith; done)
    | (norm_num at *; done)
    | (norm_num at *; omega; done)
    | (norm_num at *; linarith; done)
    | (contradiction; done)
    | (exfalso; linarith; done)
    | (simp_all; done)))

/-- `parley_suppose h`, where `h` denies what a contradiction block claims:
proves the block's `suppose` line, which says the same as `h` in the words
the page chose. -/
macro "parley_suppose " h:ident : tactic =>
  `(tactic| first
    | (exact $h; done)
    | (push_neg at $h:ident; exact $h; done)
    | (push_neg at $h:ident; linarith; done)
    | (simpa using $h; done)
    | (simp only [not_not] at $h:ident; exact $h; done)
    | (intro _; apply $h; simp_all; done))

/-- Clears what an `algebra` step divides by, from the lines saying each
divisor is not 0, a product, a quotient or a negation not 0 taken as each
of its parts not 0. -/
macro "parley_clear" : tactic =>
  `(tactic| ((try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or,
      pow_eq_zero_iff] at *) <;> (try cases_type* And) <;> field_simp))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
macro "parley_ring" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (simp only [inv_inv, one_div, div_div, div_pow] <;> ring1; done)
    | (parley_clear <;> ring1; done)
    | (parley_clear; done))

/-- What `linear_combination` asks once the cited equations are subtracted,
where the step divides: zero, once the divisions are cleared. -/
macro "parley_field" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (parley_clear <;> ring1; done))

end
