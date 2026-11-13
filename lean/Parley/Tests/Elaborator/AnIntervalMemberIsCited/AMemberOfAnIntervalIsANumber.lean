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

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AMemberOfAnIntervalIsANumber

theorem a_member_of_an_interval_is_a_number (a : ℝ) (b : ℝ) :
    (∀ x ∈ (Set.Icc a b : Set ℝ), True) := by
  -- 1. membership
  intro x h_x; exact by trivial

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AMemberOfAnIntervalIsANumber
