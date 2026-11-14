module

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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootLessOneAboveZero

theorem a_root_less_one_above_zero :
    0 < Real.sqrt (2 : ℝ) - 1 := by
  -- 1. real arithmetic
  have hf1 : (11 / 8 : ℝ) < Real.sqrt (2 : ℝ) := (Real.lt_sqrt (show (0 : ℝ) ≤ (11 / 8 : ℝ) by norm_num)).mpr (show (11 / 8 : ℝ) ^ 2 < 2 by norm_num)
  have hf2 : Real.sqrt (2 : ℝ) < (23 / 16 : ℝ) := (Real.sqrt_lt' (show (0 : ℝ) < (23 / 16 : ℝ) by norm_num)).mpr (show 2 < (23 / 16 : ℝ) ^ 2 by norm_num)
  linarith only [hf1, hf2]

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootLessOneAboveZero
