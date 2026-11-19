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

namespace Parley.Tests.Elaborator.DistanceOrder.ADistanceTheSubstitutionLeavesWrittenTheOtherWay

theorem a_distance_the_substitution_leaves_written_the_other_way (A : ℂ) (B : ℂ) (x : ℝ) (hH4 : x = 3) (hH5 : dist A B + x = 5) :
    dist B A + 3 = 5 := by
  -- 1. substitute x = 3 (H4) into H5
  (have h := (by (have h := Eq.subst (motive := (fun t : ℝ => dist A B + t = 5)) hH4 hH5; rw [dist_comm A B] at h; exact h) : dist B A + 3 = 5); push_cast at h ⊢; exact_mod_cast h)

end Parley.Tests.Elaborator.DistanceOrder.ADistanceTheSubstitutionLeavesWrittenTheOtherWay
