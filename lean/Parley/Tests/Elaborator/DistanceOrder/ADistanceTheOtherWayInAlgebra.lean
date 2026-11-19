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
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/elaborator/distance-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayInAlgebra

theorem a_distance_the_other_way_in_algebra (A : ℂ) (B : ℂ) (x : ℝ) (hH4 : dist A B = 3) :
    dist B A + x = 3 + x := by
  -- 1. algebra, from H4
  rw [dist_comm B A]
  exact (by linear_combination hH4)

end Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayInAlgebra
