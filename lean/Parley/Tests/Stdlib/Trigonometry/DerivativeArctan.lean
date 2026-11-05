module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/stdlib/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Trigonometry.DerivativeArctan

theorem derivative_arctan (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH2 : V ⊆ E) (hH3 : IsOpen V) (h : ℝ → ℝ) (hH4 : Set.MapsTo h E (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ E, h y = Real.arctan y) :
    (∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x) ∧ (∀ y ∈ V, (deriv h) y = 1 / (1 + y ^ 2)) := by
  -- 1. thm:trigonometry-derivative-arctan D := E, U := V, g := h, from H1, H2, H3, H5
  have s1a : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_1 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)); parley_set_side)
  have s1b : ∀ y ∈ V, (deriv h) y = 1 / (1 + y ^ 2) := by first | exact (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_derivative_arctan_2 (g := h) (D := E) (U := V) hH1 hH2 hH3 (by parley_set_side) (by parley_set_side)); parley_set_side)
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Tests.Stdlib.Trigonometry.DerivativeArctan
