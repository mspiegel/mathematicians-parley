module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes

theorem a_square_made_ten_times (x : ℝ) (z : ℝ) (hH3 : x ^ 2 ≠ 0) :
    (1 / 10 * x ^ 3 + z) / x ^ 2 = (1 / 10 * x ^ 3 + z) / x ^ 2 := by
  -- 1. algebra
  have r32_1 : x ^ 2 ≠ 0 := by exact hH3
  have hz1 : x ≠ 0 := (pow_ne_zero_iff (by norm_num)).mp r32_1; field

end Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes
