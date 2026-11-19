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
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Written from tests/elaborator/distance-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWaySubstitutedInto

theorem a_distance_the_other_way_substituted_into (A : ℂ) (B : ℂ) (x : ℝ) (hH4 : dist A B = 3) (hH5 : dist B A + x = 5) :
    3 + x = 5 := by
  -- 1. substitute |AB| = 3 (H4) into H5
  exact Eq.subst (motive := (fun t : ℝ => t + x = 5)) hH4 (by (have h := hH5; rw [dist_comm B A] at h; exact h) : dist A B + x = 5)

end Parley.Tests.Elaborator.DistanceOrder.ADistanceTheOtherWaySubstitutedInto
