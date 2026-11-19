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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/elaborator/distance-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayRestated

theorem a_distance_the_other_way_restated (A : ℂ) (B : ℂ) (hH3 : dist A B = 3) :
    dist B A = 3 := by
  -- 1. restate H3
  exact (by (have h := hH3; rw [dist_comm A B] at h; exact h) : dist B A = 3)

end Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWayRestated
