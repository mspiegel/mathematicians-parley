module

public import Mathlib
public import Tactics

/-!
# What an order step leaves to linear arithmetic

`parley_order` closes an `inequalities`, `transitivity` or `antisymmetry`
step. A generated file imports this module only when it calls it.
-/

public section

/-- An order between numbers that follows from the lines above by linear
arithmetic, as an `inequalities`, `transitivity` or `antisymmetry` step's
does: the ways of `parley_side` that close such a goal, the cheapest first,
and none that do not. -/
macro "parley_order" : tactic =>
  `(tactic| ((try cases_type* And) <;> (try casesm* _ ∧ _) <;> first
    | (assumption; done)
    | (constructor <;> assumption; done)
    | (positivity; done)
    | (omega; done)
    | (linarith; done)
    -- Natural numbers in ℝ, 2 ≤ N + 1 from 0 < N: the casts moved out.
    | (norm_cast at *; omega; done)
    | (push_cast at *; assumption; done)
    | (assumption_mod_cast; done)
    | (push_cast at *; linarith; done)
    | (qify at *; linarith; done)
    | (rify at *; linarith; done)
    | (norm_num at *; omega; done)
    | (apply lt_of_le_of_ne <;> (first | linarith | assumption | (apply Ne.symm; assumption)); done)
    -- Quotients as products with an inverse, so that 4/n and 1/2^n meet
    -- 1/n and (2^n)⁻¹ as the same terms.
    | (simp only [div_eq_mul_inv, one_mul] at *; linarith; done)))

end
