module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.AreaUnderOtherLetters

theorem area_under_other_letters (c : ℝ) (d : ℝ) (hH3 : c < d) (g : ℝ → ℝ) (hH4 : Set.MapsTo g (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH5 : ContinuousOn g (Set.Icc c d : Set ℝ)) (H : ℝ → ℝ) (hH6 : Set.MapsTo H (Set.Icc c d : Set ℝ) (Set.univ : Set ℝ)) (hH7 : ∀ y ∈ (Set.Icc c d : Set ℝ), H y = (∫ s in c..y, (g s : ℝ))) :
    (∀ y ∈ (Set.Ioo c d : Set ℝ), (deriv H) y = g y) := by
  -- 1. thm:area-function a := c, b := d, f := g, G := H, from H3, H5, H7
  have s1 : ∀ y ∈ (Set.Ioo c d : Set ℝ), (deriv H) y = g y := by first | exact (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := g) (G := H) (a := c) (b := d) hH3 hH5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := g) (G := H) (a := c) (b := d) hH3 hH5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := g) (G := H) (a := c) (b := d) hH3 hH5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := g) (G := H) (a := c) (b := d) hH3 hH5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_area_function_3 (f := g) (G := H) (a := c) (b := d) hH3 hH5 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.AreaUnderOtherLetters
