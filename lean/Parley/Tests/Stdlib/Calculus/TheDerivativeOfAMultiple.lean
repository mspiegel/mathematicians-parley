module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.TheDerivativeOfAMultiple

theorem the_derivative_of_a_multiple (E : Set ℝ) (hH1 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH2 : V ⊆ E) (h : ℝ → ℝ) (hH3 : Set.MapsTo h E (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH4 : Set.MapsTo H E (Set.univ : Set ℝ)) (hH5 : ∀ y ∈ E, H y = 7 * h y) (hH6 : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ h x) :
    (∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ H x) ∧ (∀ y ∈ V, (deriv H) y = 7 * (deriv h) y) := by
  -- 1. thm:derivative-scaled D := E, U := V, c := 7, F := H, f := h, from H1, H2, H5, H6
  have s1a : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ H x := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_1 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6); parley_set_side)
  have s1b : ∀ y ∈ V, (deriv H) y = 7 * (deriv h) y := by first | exact (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | exact ((Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6)).symm | simpa using (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | exact_mod_cast (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6) | (have h := (Parley.Items.Stdlib.Calculus.thm_derivative_scaled_2 (F := H) (f := h) (D := E) (U := V) hH1 hH2 (c := (7 : ℝ)) (by parley_set_side) hH6); parley_set_side)
  exact ⟨by parley_set_side, by parley_set_side⟩

end Parley.Tests.Stdlib.Calculus.TheDerivativeOfAMultiple
