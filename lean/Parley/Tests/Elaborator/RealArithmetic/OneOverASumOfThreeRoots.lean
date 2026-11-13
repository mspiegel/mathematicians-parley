module

public import RealTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots

theorem one_over_a_sum_of_three_roots :
    1 / (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ≠ 0 := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots
