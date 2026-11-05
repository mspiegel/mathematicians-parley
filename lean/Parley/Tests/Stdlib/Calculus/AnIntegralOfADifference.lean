module

public import PowerTactics
public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AnIntegralOfADifference

theorem an_integral_of_a_difference (c : ℝ) (d : ℝ) (hH3 : c < d) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (k : ℝ → ℝ) (hH5 : Set.MapsTo k (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH6 : Set.MapsTo H (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ∀ y ∈ (Set.Icc c d : Set ℝ), H y = h y - k y) (hH8 : ContinuousOn h (Set.Icc c d : Set ℝ)) (hH9 : ContinuousOn k (Set.Icc c d : Set ℝ)) :
    (∫ s in c..d, (H s : ℝ)) = (∫ s in c..d, (h s : ℝ)) - (∫ s in c..d, (k s : ℝ)) := by
  -- 1. thm:integral-difference a := c, b := d, f := h, g := k, h := H, from H3, H7, H8, H9
  have s1 : (∫ s in c..d, (H s : ℝ)) = (∫ s in c..d, (h s : ℝ)) - (∫ s in c..d, (k s : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.thm_integral_difference (f := h) (g := k) (h := H) (a := c) (b := d) hH3 (by parley_set_side) hH8 hH9 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AnIntegralOfADifference
