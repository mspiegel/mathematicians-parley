module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.APowerIsContinuous

theorem a_power_is_continuous (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH3 : ∀ y ∈ E, h y = y ^ 3) :
    ContinuousOn h E := by
  -- 1. thm:continuous-power D := E, n := 3, g := h, from H1, H3
  have s1 : ContinuousOn h E := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := h) (D := E) hH1 (n := 3) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_power (g := h) (D := E) hH1 (n := 3) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := h) (D := E) hH1 (n := 3) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := h) (D := E) hH1 (n := 3) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_power (g := h) (D := E) hH1 (n := 3) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.APowerIsContinuous
