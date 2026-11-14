module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
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

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients

theorem a_power_with_halved_coefficients :
    ((1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) / 2) ^ 6 = 81 / 4 + 55 / 4 * Real.sqrt (2 : ℝ) + 45 / 4 * Real.sqrt (3 : ℝ) + 33 / 4 * Real.sqrt (6 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (6 : ℝ) = Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) := by rw [congrArg Real.sqrt (show (6 : ℝ) = 2 * 3 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 by norm_num) 3]
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  linear_combination (-(33 / 4 : ℝ)) * hv1 + ((5 / 16 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) ^ 3 + (15 / 64 : ℝ) * Real.sqrt (2 : ℝ) ^ 2 * Real.sqrt (3 : ℝ) ^ 2 + (3 / 32 : ℝ) * Real.sqrt (2 : ℝ) ^ 3 * Real.sqrt (3 : ℝ) + (1 / 64 : ℝ) * Real.sqrt (2 : ℝ) ^ 4 + (15 / 64 : ℝ) * Real.sqrt (3 : ℝ) ^ 4 + (15 / 16 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) ^ 2 + (15 / 32 : ℝ) * Real.sqrt (2 : ℝ) ^ 2 * Real.sqrt (3 : ℝ) + (3 / 32 : ℝ) * Real.sqrt (2 : ℝ) ^ 3 + (15 / 16 : ℝ) * Real.sqrt (3 : ℝ) ^ 3 + (9 / 8 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + (17 / 64 : ℝ) * Real.sqrt (2 : ℝ) ^ 2 + (15 / 8 : ℝ) * Real.sqrt (3 : ℝ) ^ 2 + (1 / 2 : ℝ) * Real.sqrt (2 : ℝ) + (15 / 8 : ℝ) * Real.sqrt (3 : ℝ) + (49 / 64 : ℝ)) * hr2 + ((3 / 32 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) ^ 3 + (1 / 64 : ℝ) * Real.sqrt (3 : ℝ) ^ 4 + (15 / 32 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) ^ 2 + (3 / 32 : ℝ) * Real.sqrt (3 : ℝ) ^ 3 + (59 / 32 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + (3 / 4 : ℝ) * Real.sqrt (3 : ℝ) ^ 2 + (135 / 32 : ℝ) * Real.sqrt (2 : ℝ) + (79 / 32 : ℝ) * Real.sqrt (3 : ℝ) + (399 / 64 : ℝ)) * hr3

end Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients
