module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes

theorem a_square_made_ten_times (x : ℝ) (z : ℝ) (hH3 : x ^ 2 ≠ 0) :
    (1 / 10 * x ^ 3 + z) / x ^ 2 = (1 / 10 * x ^ 3 + z) / x ^ 2 := by
  -- 1. algebra
  have r32_1 : x ^ 2 ≠ 0 := by exact hH3
  parley_ring

end Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes
