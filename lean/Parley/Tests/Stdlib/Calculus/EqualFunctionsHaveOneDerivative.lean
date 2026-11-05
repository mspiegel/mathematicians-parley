module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.EqualFunctionsHaveOneDerivative

theorem equal_functions_have_one_derivative (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (E : Set ℝ) (hH2 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH3 : V ⊆ D) (hH4 : V ⊆ E) (hH5 : IsOpen V) (h : ℝ → ℝ) (hH6 : Set.MapsTo h D (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH7 : Set.MapsTo H E (Set.univ : Set ℝ)) (hH8 : ∀ y ∈ V, H y = h y) (hH9 : ∀ x ∈ V, D ∈ nhds x ∧ DifferentiableAt ℝ h x) :
    (∀ y ∈ V, (deriv H) y = (deriv h) y) := by
  -- 1. mun:derivative-local U := V, f := h, F := H, from H1, H2, H3, H4, H5, H8, H9
  have s1 : ∀ y ∈ V, (deriv H) y = (deriv h) y := by first | exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9 (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9 (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9 (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9 (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Calculus.mun_derivative_local_2 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9 (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.EqualFunctionsHaveOneDerivative
