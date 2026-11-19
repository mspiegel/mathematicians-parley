module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/elaborator/distance-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayInAnInequalitiesRow

theorem a_distance_the_other_way_in_an_inequalities_row (A : ℂ) (B : ℂ) (hH3 : dist A B < 3) :
    dist B A ≤ 3 := by
  -- 1. inequalities
  rw [dist_comm B A]
  exact (by linarith only [hH3])

end Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayInAnInequalitiesRow
