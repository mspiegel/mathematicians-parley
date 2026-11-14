module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumOfThreeRoots

theorem a_square_of_a_sum_of_three_roots :
    (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ^ 2 = 10 + 2 * Real.sqrt (6 : ℝ) + 2 * Real.sqrt (10 : ℝ) + 2 * Real.sqrt (15 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (15 : ℝ) = Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (15 : ℝ) = 3 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) 5]
  have hv2 : Real.sqrt (10 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (10 : ℝ) = 2 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 5]
  have hv3 : Real.sqrt (6 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by rw [congrArg Real.sqrt (show (6 : ℝ) = 2 * 3 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 3]
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr5 : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  linear_combination (-2) * hv1 + (-2) * hv2 + (-2) * hv3 + hr2 + hr3 + hr5

end Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumOfThreeRoots
