module

public import SetTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AMemberOfAnIntervalIsANumber

theorem a_member_of_an_interval_is_a_number (a : ℝ) (b : ℝ) :
    (∀ x ∈ (Set.Icc a b : Set ℝ), True) := by
  -- 1. membership
  have s1 : ∀ x ∈ (Set.Icc a b : Set ℝ), True := by intro x h_x; parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AMemberOfAnIntervalIsANumber
