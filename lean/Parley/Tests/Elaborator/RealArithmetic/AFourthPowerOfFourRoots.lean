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

namespace Parley.Tests.Elaborator.RealArithmetic.AFourthPowerOfFourRoots

theorem a_fourth_power_of_four_roots :
    (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ) + Real.sqrt (7 : ℝ)) ^ 4 = 693 + 164 * Real.sqrt (6 : ℝ) + 148 * Real.sqrt (10 : ℝ) + 132 * Real.sqrt (14 : ℝ) + 140 * Real.sqrt (15 : ℝ) + 124 * Real.sqrt (21 : ℝ) + 108 * Real.sqrt (35 : ℝ) + 24 * Real.sqrt (210 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (210 : ℝ) = Real.sqrt (2 : ℝ) * (Real.sqrt (3 : ℝ) * (Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ))) := by rw [congrArg Real.sqrt (show (210 : ℝ) = 2 * (3 * (5 * 7)) by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) (3 * (5 * 7)), Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (5 * 7), Real.sqrt_mul (show (0 : ℝ) ≤ 5 by norm_num) 7]
  have hv2 : Real.sqrt (35 : ℝ) = Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ) := by rw [congrArg Real.sqrt (show (35 : ℝ) = 5 * 7 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 5 by norm_num) 7]
  have hv3 : Real.sqrt (21 : ℝ) = Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) := by rw [congrArg Real.sqrt (show (21 : ℝ) = 3 * 7 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) 7]
  have hv4 : Real.sqrt (15 : ℝ) = Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (15 : ℝ) = 3 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) 5]
  have hv5 : Real.sqrt (14 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) := by rw [congrArg Real.sqrt (show (14 : ℝ) = 2 * 7 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 7]
  have hv6 : Real.sqrt (10 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (10 : ℝ) = 2 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 5]
  have hv7 : Real.sqrt (6 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by rw [congrArg Real.sqrt (show (6 : ℝ) = 2 * 3 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 3]
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr5 : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hr7 : Real.sqrt (7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  linear_combination (-24) * hv1 + (-108) * hv2 + (-124) * hv3 + (-140) * hv4 + (-132) * hv5 + (-148) * hv6 + (-164) * hv7 + (4 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 4 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 4 * Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) + Real.sqrt (2 : ℝ) ^ 2 + 12 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 12 * Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) + 6 * Real.sqrt (3 : ℝ) ^ 2 + 12 * Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ) + 6 * Real.sqrt (5 : ℝ) ^ 2 + 6 * Real.sqrt (7 : ℝ) ^ 2 + 2) * hr2 + (4 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 12 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 12 * Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) + 4 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 4 * Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) + Real.sqrt (3 : ℝ) ^ 2 + 12 * Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ) + 6 * Real.sqrt (5 : ℝ) ^ 2 + 6 * Real.sqrt (7 : ℝ) ^ 2 + 15) * hr3 + (12 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 4 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 12 * Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) + 4 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 12 * Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) + 4 * Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ) + Real.sqrt (5 : ℝ) ^ 2 + 6 * Real.sqrt (7 : ℝ) ^ 2 + 35) * hr5 + (12 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 12 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 4 * Real.sqrt (2 : ℝ) * Real.sqrt (7 : ℝ) + 12 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 4 * Real.sqrt (3 : ℝ) * Real.sqrt (7 : ℝ) + 4 * Real.sqrt (5 : ℝ) * Real.sqrt (7 : ℝ) + Real.sqrt (7 : ℝ) ^ 2 + 67) * hr7

end Parley.Tests.Elaborator.RealArithmetic.AFourthPowerOfFourRoots
