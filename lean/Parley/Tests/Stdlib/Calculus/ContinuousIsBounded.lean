module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ContinuousIsBounded

theorem continuous_is_bounded (c : ℝ) (d : ℝ) (h : ℝ → ℝ) (hH3 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH4 : ContinuousOn h (Set.Icc c d : Set ℝ)) :
    (∃ M : ℝ, ∀ y ∈ (Set.Icc c d : Set ℝ), abs (h y) ≤ M) := by
  -- 1. thm:continuous-bounded a := c, b := d, f := h, from H4
  have s1 : ∃ M : ℝ, ∀ y ∈ (Set.Icc c d : Set ℝ), abs (h y) ≤ M := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_bounded (f := h) (a := c) (b := d) hH4 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ContinuousIsBounded
