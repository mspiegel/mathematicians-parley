module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnIntegralNotNegative

theorem an_integral_not_negative (c : ℝ) (d : ℝ) (hH3 : c < d) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ (Set.Icc c d : Set ℝ), h y ≥ 0) (hH6 : ContinuousOn h (Set.Icc c d : Set ℝ)) :
    (∫ s in c..d, (h s : ℝ)) ≥ 0 := by
  -- 1. thm:integral-nonneg a := c, b := d, f := h, from H3, H5, H6
  have s1 : (∫ s in c..d, (h s : ℝ)) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := h) (a := c) (b := d) hH3 (by parley_set_side) hH6)] | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := h) (a := c) (b := d) hH3 (by parley_set_side) hH6); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := h) (a := c) (b := d) hH3 (by parley_set_side) hH6) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_nonneg (f := h) (a := c) (b := d) hH3 (by parley_set_side) hH6); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AnIntegralNotNegative
