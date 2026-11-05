module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ALimitFilledIn

theorem a_limit_filled_in (U : Set ℝ) (hH1 : U ⊆ (Set.univ : Set ℝ)) (hH2 : IsOpen U) (p : ℝ) (hH3 : p ∈ U) (h : ℝ → ℝ) (hH4 : Set.MapsTo h (U \ ({p} : Set ℝ)) (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH5 : Set.MapsTo H U (Set.univ : Set ℝ)) (hH6 : ∀ y ∈ U \ ({p} : Set ℝ), H y = h y) (hH7 : H p = 0) (hH8 : ∀ x ∈ (U \ ({p} : Set ℝ)), (U \ ({p} : Set ℝ)) ∈ nhds x ∧ DifferentiableAt ℝ h x) (hH9 : Filter.Tendsto h (nhdsWithin p ((U \ ({p} : Set ℝ)) \ {p})) (nhds 0)) :
    ContinuousOn H U := by
  -- 1. thm:continuous-extension c := p, L := 0, f := h, F := H, from H1, H2, H3, H6, H7, H8, H9
  have s1 : ContinuousOn H U := by first | exact (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := h) (F := H) (U := U) (c := p) hH1 hH2 hH3 (L := (0 : ℝ)) (by parley_set_side) (by parley_set_side) hH8 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := h) (F := H) (U := U) (c := p) hH1 hH2 hH3 (L := (0 : ℝ)) (by parley_set_side) (by parley_set_side) hH8 (by parley_set_side) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := h) (F := H) (U := U) (c := p) hH1 hH2 hH3 (L := (0 : ℝ)) (by parley_set_side) (by parley_set_side) hH8 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := h) (F := H) (U := U) (c := p) hH1 hH2 hH3 (L := (0 : ℝ)) (by parley_set_side) (by parley_set_side) hH8 (by parley_set_side) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.thm_continuous_extension (f := h) (F := H) (U := U) (c := p) hH1 hH2 hH3 (L := (0 : ℝ)) (by parley_set_side) (by parley_set_side) hH8 (by parley_set_side) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.ALimitFilledIn
