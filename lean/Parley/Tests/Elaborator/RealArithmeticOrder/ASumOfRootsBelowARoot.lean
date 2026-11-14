module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ASumOfRootsBelowARoot

theorem a_sum_of_roots_below_a_root :
    Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) < Real.sqrt (10 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (10 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) := by rw [congrArg Real.sqrt (show (10 : ℝ) = 2 * 5 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 5]
  have hf1 : Real.sqrt (10 : ℝ) - (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) = Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) - Real.sqrt (2 : ℝ) - Real.sqrt (3 : ℝ) := by linear_combination hv1
  have hf2 : (181 / 128 : ℝ) < Real.sqrt (2 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (181 / 128 : ℝ) by norm_num)).mpr (show (181 / 128 : ℝ) ^ 2 < 2 by norm_num)
  have hf3 : Real.sqrt (2 : ℝ) < (363 / 256 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (363 / 256 : ℝ) by norm_num)).mpr (show 2 < (363 / 256 : ℝ) ^ 2 by norm_num)
  have hf4 : (143 / 64 : ℝ) < Real.sqrt (5 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (143 / 64 : ℝ) by norm_num)).mpr (show (143 / 64 : ℝ) ^ 2 < 5 by norm_num)
  have hf5 : Real.sqrt (5 : ℝ) < (573 / 256 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (573 / 256 : ℝ) by norm_num)).mpr (show 5 < (573 / 256 : ℝ) ^ 2 by norm_num)
  have hf6 : (181 / 128 : ℝ) * (143 / 64 : ℝ) < Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) := mul_lt_mul'' hf2 hf4 (show (0 : ℝ) ≤ (181 / 128 : ℝ) by norm_num) (show (0 : ℝ) ≤ (143 / 64 : ℝ) by norm_num)
  have hf7 : Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) < (363 / 256 : ℝ) * (573 / 256 : ℝ) := mul_lt_mul'' hf3 hf5 (le_of_lt (lt_of_le_of_lt (show (0 : ℝ) ≤ (181 / 128 : ℝ) by norm_num) hf2)) (le_of_lt (lt_of_le_of_lt (show (0 : ℝ) ≤ (143 / 64 : ℝ) by norm_num) hf4))
  have hf8 : (443 / 256 : ℝ) < Real.sqrt (3 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (443 / 256 : ℝ) by norm_num)).mpr (show (443 / 256 : ℝ) ^ 2 < 3 by norm_num)
  have hf9 : Real.sqrt (3 : ℝ) < (111 / 64 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (111 / 64 : ℝ) by norm_num)).mpr (show 3 < (111 / 64 : ℝ) ^ 2 by norm_num)
  linarith only [hf1, hf2, hf3, hf6, hf7, hf8, hf9]

end Parley.Tests.Elaborator.RealArithmeticOrder.ASumOfRootsBelowARoot
