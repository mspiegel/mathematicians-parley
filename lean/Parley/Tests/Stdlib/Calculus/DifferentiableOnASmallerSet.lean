module

public import SetTactics
public import Tactics
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.DifferentiableOnASmallerSet

theorem differentiable_on_a_smaller_set (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (h : ℝ → ℝ) (hH2 : Set.MapsTo h D (Set.univ : Set ℝ)) (V : Set ℝ) (hH3 : V ⊆ D) (W : Set ℝ) (hH4 : W ⊆ V) (hH5 : ∀ x ∈ V, D ∈ nhds x ∧ DifferentiableAt ℝ h x) :
    (∀ x ∈ W, D ∈ nhds x ∧ DifferentiableAt ℝ h x) := by
  -- 1. mun:differentiable-on-part U := V, S := W, f := h, from H1, H3, H4, H5
  have s1 : ∀ x ∈ W, D ∈ nhds x ∧ DifferentiableAt ℝ h x := by exact (Parley.Items.Stdlib.Calculus.mun_differentiable_on_part (f := h) (D := D) (U := V) (S := W) hH1 hH3 hH4 hH5)
  all_goals exact s1

end Parley.Tests.Stdlib.Calculus.DifferentiableOnASmallerSet
