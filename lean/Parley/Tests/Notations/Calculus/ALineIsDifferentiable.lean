module

public import SetTactics
public import Tactics
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/notations/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Calculus.ALineIsDifferentiable

theorem a_line_is_differentiable (g : ℝ → ℝ) (hH1 : Set.MapsTo g (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) (Set.univ : Set ℝ)) (hH2 : ∀ x ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ), g x = 2 * x) :
    (∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ g x) := by
  -- 1. thm:derivative-linear D := [0, 1], U := (0, 1), m := 2, from H2
  have r100_1 : (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_interval_real (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r100_2 : (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) ⊆ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_within_closed (a := (0 : ℝ)) (b := (1 : ℝ)))
  have r100_3 : IsOpen (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := (0 : ℝ)) (b := (1 : ℝ)))
  have s1 : ∀ x ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ), (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ) ∈ nhds x ∧ DifferentiableAt ℝ g x := by exact (Parley.Items.Stdlib.Calculus.thm_derivative_linear_1 (g := g) (D := (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (U := (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) (by parley_set_side) (by parley_set_side) (by parley_set_side) (m := (2 : ℝ)) (by parley_set_side))
  all_goals exact s1

end Parley.Tests.Notations.Calculus.ALineIsDifferentiable
