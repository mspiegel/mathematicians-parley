module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.ADerivativeOnAPartIsReal

theorem a_derivative_on_a_part_is_real (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h D (Set.univ : Set ℝ)) (S : Set ℝ) (hH3 : S ⊆ D) (hH4 : ∀ x ∈ S, D ∈ nhds x ∧ DifferentiableAt ℝ h x) (y : ℝ) (hH5 : y ∈ S) :
    True := by
  -- 1. mun:derivative-real-on U := S, f := h, x := y, from H1, H3, H4, H5
  all_goals parley_set_side

end Parley.Tests.Stdlib.Calculus.ADerivativeOnAPartIsReal
