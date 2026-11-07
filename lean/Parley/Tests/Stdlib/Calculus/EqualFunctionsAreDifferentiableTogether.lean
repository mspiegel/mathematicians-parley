module

public import SetTactics
public import Tactics
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.EqualFunctionsAreDifferentiableTogether

theorem equal_functions_are_differentiable_together (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (E : Set ℝ) (hH2 : E ⊆ (Set.univ : Set ℝ)) (V : Set ℝ) (hH3 : V ⊆ D) (hH4 : V ⊆ E) (hH5 : IsOpen V) (h : ℝ → ℝ) (hH6 : Set.MapsTo h D (Set.univ : Set ℝ)) (H : ℝ → ℝ) (hH7 : Set.MapsTo H E (Set.univ : Set ℝ)) (hH8 : ∀ y ∈ V, H y = h y) (hH9 : ∀ x ∈ V, D ∈ nhds x ∧ DifferentiableAt ℝ h x) :
    (∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ H x) := by
  -- 1. mun:derivative-local U := V, f := h, F := H, from H1, H2, H3, H4, H5, H8, H9
  have s1 : ∀ x ∈ V, E ∈ nhds x ∧ DifferentiableAt ℝ H x := by exact (Parley.Items.Stdlib.Calculus.mun_derivative_local_1 (f := h) (F := H) (D := D) (E := E) (U := V) hH1 hH2 hH3 hH4 hH5 (by parley_set_side) hH9)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.EqualFunctionsAreDifferentiableTogether
