module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Parley.Items.Stdlib.Calculus

/-! Written from tests/stdlib/calculus.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Calculus.OpenButForAPoint

theorem open_but_for_a_point (a : ℝ) (b : ℝ) (c : ℝ) (hH3 : c ∈ (Set.Ioo a b : Set ℝ)) :
    IsOpen ((Set.Ioo a b : Set ℝ) \ ({c} : Set ℝ)) := by
  -- 1. mun:open-without-point U := (a, b), from H3
  have r245_1 : (Set.Ioo a b : Set ℝ) ⊆ (Set.univ : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_real (a := a) (b := b))
  have r245_2 : IsOpen (Set.Ioo a b : Set ℝ) := by exact (Parley.Items.Stdlib.Calculus.mun_open_interval_open (a := a) (b := b))
  exact (Parley.Items.Stdlib.Calculus.mun_open_without_point (U := (Set.Ioo a b : Set ℝ)) (c := c) r245_1 r245_2 hH3)

end Parley.Tests.Stdlib.Calculus.OpenButForAPoint
