module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.IntegralsInOrder

theorem integrals_in_order (c : ℝ) (d : ℝ) (hH3 : c < d) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hH5 : Set.MapsTo k (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH6 : ∀ y ∈ (Set.Icc c d : Set ℝ), h y ≤ k y) (hH7 : ContinuousOn h (Set.Icc c d : Set ℝ)) (hH8 : ContinuousOn k (Set.Icc c d : Set ℝ)) :
    (∫ s in c..d, (h s : ℝ)) ≤ (∫ s in c..d, (k s : ℝ)) := by
  -- 1. thm:integral-order a := c, b := d, f := h, g := k, from H3, H6, H7, H8
  have s1 : (∫ s in c..d, (h s : ℝ)) ≤ (∫ s in c..d, (k s : ℝ)) := by first | linarith [(Parley.Items.Stdlib.Calculus.thm_integral_order (f := h) (g := k) (a := c) (b := d) hH3 (by parley_set_side) hH7 hH8 (by parley_set_side) (by parley_set_side))] | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_order (f := h) (g := k) (a := c) (b := d) hH3 (by parley_set_side) hH7 hH8 (by parley_set_side) (by parley_set_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_order (f := h) (g := k) (a := c) (b := d) hH3 (by parley_set_side) hH7 hH8 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_order (f := h) (g := k) (a := c) (b := d) hH3 (by parley_set_side) hH7 hH8 (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.IntegralsInOrder
