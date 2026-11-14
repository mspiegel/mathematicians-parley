module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ANegativePower

theorem a_negative_power :
    (1 + Real.sqrt (2 : ℝ)) ^ (-2 : ℤ) = 3 - 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hv1 : (1 + Real.sqrt (2 : ℝ)) ^ (-2 : ℤ) = -(2 * Real.sqrt (2 : ℝ)) + 3 := by rw [zpow_neg, zpow_ofNat]; exact inv_eq_of_mul_eq_one_left (show (-(2 * Real.sqrt (2 : ℝ)) + 3) * (1 + Real.sqrt (2 : ℝ)) ^ 2 = 1 by linear_combination (-(2 * Real.sqrt (2 : ℝ)) - 1) * hr2)
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmetic.ANegativePower
