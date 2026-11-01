module

public import Mathlib
public import Parley.Library.Counting

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
    | (assumption_mod_cast; done)
    | (push_cast at *; linarith; done)
    | (qify at *; linarith; done)
    | (rify at *; linarith; done)
    | (apply lt_of_le_of_ne <;> (first | linarith | assumption | (apply Ne.symm; assumption)); done)
    | (intro _; linarith; done)
    | (norm_num at *; done)
    | (norm_num at *; subst_vars; norm_num; done)
    | (norm_cast at *; subst_vars; norm_num; done)
    | (norm_num at *; omega; done)
    | (norm_num at *; norm_cast at *; omega; done)
    | (norm_num at *; linarith; done)
    | (contradiction; done)
    | (exfalso; apply ‹¬ _›; exact Int.ModEq.symm ‹_›; done)
    | (exfalso; linarith; done)
    -- An integer a line gives as a quotient, (M! + 1)/N, in an equation of
    -- integers: in ℚ, with the division cleared, it is linear.
    | (qify at *; field_simp at *; linarith; done)
    | (simp_all; done)))

/-- `parley_suppose h`, where `h` denies what a contradiction block claims:
proves the block's `suppose` line, which says the same as `h` in the words
the page chose. -/
macro "parley_suppose " h:ident : tactic =>
  `(tactic| first
    | (exact $h; done)
    | (exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact $h; done)
    | (push_neg at $h:ident; linarith; done)
    | (simpa using $h; done)
    | (simp only [not_not] at $h:ident; exact $h; done)
    | (simp only [not_not, ne_eq] at $h:ident; exact Eq.symm $h; done)
    | (push_neg at $h:ident; exact Eq.symm $h; done)
    | (intro _; apply $h; simp_all; done))

/-- `arithmetic`: a closed fact of numbers, worked out, and that a fraction
which is no whole number is no member of ℕ or ℤ. -/
macro "parley_arith" : tactic =>
  `(tactic| first
    | (norm_num; done)
    | (norm_num [Parley.Library.factorial, Parley.Library.choose, Nat.factorial]; done)
    | (rintro ⟨m, _, h⟩; field_simp at h; norm_cast at h; omega)
    | (rintro ⟨m, h⟩; field_simp at h; norm_cast at h; omega))

/-- Clears what an `algebra` step divides by, from the lines saying each
divisor is not 0, a product, a quotient or a negation not 0 taken as each
of its parts not 0. -/
macro "parley_clear" : tactic =>
  `(tactic| ((try simp only [ne_eq, mul_eq_zero, div_eq_zero_iff, neg_eq_zero, not_or,
      pow_eq_zero_iff] at *) <;> (try cases_type* And) <;> field_simp))

/-- An identity of `algebra` with no line cited: a ring identity, or one
once the divisions are cleared. -/
-- The check `linear_combination` ends with: `ring1`, or `ring1` after the
-- casts are pushed in, where a function's argument is cast two ways,
-- C(↑m + 1, 1) beside C(↑(m + 1), 1), which ring1 takes as two atoms.
macro "parley_norm" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done))

macro "parley_ring" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    | (simp only [inv_inv, one_div, div_div, div_pow] <;> ring1; done)
    | (parley_clear <;> ring1; done)
    | (parley_clear; done))

/-- `substitute`, into the goal: the goal is what the equation `e` makes of
a term in it, either way round. -/
macro "parley_subst " e:term:max : tactic =>
  `(tactic| first
    | (rw [$e:term]; done)
    | (rw [← $e:term]; done)
    | (rw [$e:term]; ring1; done)
    | (rw [← $e:term]; ring1; done)
    | (simp only [$e:term]; done)
    | (simp only [← $e:term]; done)
    | (simp only [$e:term]; ring1; done)
    | (simp only [← $e:term]; ring1; done)
    | (linear_combination $e:term; done)
    | (linear_combination (-1 : _) * $e:term; done)
    | (have h := $e:term; norm_cast at h; rw [h]; done)
    | (have h := $e:term; norm_cast at h; rw [← h]; done)
    | (have h := $e:term; norm_cast at h; simp only [h]; done))

/-- `substitute` into the line `h`: the goal is `h` with a term put for
another by the equation `e`, either way round. -/
macro "parley_subst_at " e:term:max h:ident : tactic =>
  `(tactic| first
    | (rw [$e:term] at $h:ident; exact $h; done)
    | (rw [← $e:term] at $h:ident; exact $h; done)
    | (rw [$e:term]; exact $h; done)
    | (rw [← $e:term]; exact $h; done)
    | (simp only [$e:term] at $h:ident ⊢; exact $h; done)
    | (simp only [← $e:term] at $h:ident ⊢; exact $h; done)
    -- An equation of naturals cast up to ℤ, put where ℕ is wanted, an
    -- exponent, is taken back down first.
    | (have e := $e; norm_cast at e; rw [← e] at $h:ident; exact $h; done)
    | (have e := $e; norm_cast at e; rw [e] at $h:ident; exact $h; done)
    | (rw [$e:term] at $h:ident; linarith; done)
    | (rw [← $e:term] at $h:ident; linarith; done)
    | (simp only [$e:term] at $h:ident ⊢; linarith; done)
    | (simp only [← $e:term] at $h:ident ⊢; linarith; done)
    | (rw [$e:term] at $h:ident; parley_side; done)
    | (rw [← $e:term] at $h:ident; parley_side; done)
    | (rw [$e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term] at $h:ident; exact_mod_cast $h; done)
    | (rw [← $e:term]; exact $h _; done)
    | (rw [$e:term]; exact $h _; done)
    | (exact $h _; done))

/-- What `linear_combination` asks once the cited equations are subtracted,
where the step divides: zero, once the divisions are cleared. -/
macro "parley_field" : tactic =>
  `(tactic| first
    | (ring1; done)
    | (push_cast; ring1; done)
    | (parley_clear <;> ring1; done))

end
