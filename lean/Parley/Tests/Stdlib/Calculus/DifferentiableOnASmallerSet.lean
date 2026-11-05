module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.DifferentiableOnASmallerSet

theorem differentiable_on_a_smaller_set (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h D (Set.univ : Set ℝ)) (V : Set ℝ) (hH3 : V ⊆ D) (W : Set ℝ) (hH4 : W ⊆ V) (hH5 : ∀ x ∈ V, D ∈ nhds x ∧ DifferentiableAt ℝ h x) :
    (∀ x ∈ W, D ∈ nhds x ∧ DifferentiableAt ℝ h x) := by
  -- 1. mun:differentiable-on-part U := V, S := W, f := h, from H1, H3, H4, H5
  have s1 : ∀ x ∈ W, D ∈ nhds x ∧ DifferentiableAt ℝ h x := by first | exact (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.DifferentiableOnASmallerSet
