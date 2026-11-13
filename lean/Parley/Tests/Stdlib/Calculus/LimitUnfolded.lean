module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.LimitUnfolded

theorem limit_unfolded (D : Set ℝ) (hH1 : D ⊆ (Set.univ : Set ℝ)) (f : ℝ → ℝ) (hH2 : Set.MapsTo f D (Set.univ : Set ℝ)) (c : ℝ) (L : ℝ) (hH5 : Filter.Tendsto f (nhdsWithin c (D \ {c})) (nhds L)) :
    (∀ ε : ℝ, ε > 0 → (∃ δ : ℝ, δ > 0 ∧ (∀ x ∈ D, x ≠ c ∧ abs (x - c) < δ → abs (f x - L) < ε))) := by
  -- 1. def:limit-at, from H1, H5
  exact ((Parley.Items.Stdlib.Calculus.def_limit_at (f := f) (D := D) hH1 (c := c) (L := L))).mp hH5

end Parley.Tests.Stdlib.Calculus.LimitUnfolded
