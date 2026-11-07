module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.DividedByAHalf

theorem divided_by_a_half (x : ℝ) (hH2 : x ≠ 0) :
    3 / (x / 2) = 6 / x := by
  -- 1. algebra
  have r42_1 : x ≠ 0 := by parley_side
  have s1 : 3 / (x / 2) = 6 / x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.Divisors.DividedByAHalf
