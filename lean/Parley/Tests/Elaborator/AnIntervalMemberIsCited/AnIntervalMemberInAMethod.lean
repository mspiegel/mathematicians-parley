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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberInAMethod

theorem an_interval_member_in_a_method (s : ℝ) (hH1 : s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (t : ℝ) (hH2 : t ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) :
    True := by
  -- 1. membership
  exact trivial

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberInAMethod
