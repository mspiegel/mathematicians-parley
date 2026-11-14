module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAHalf

theorem a_logarithm_of_a_half :
    Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.log (1 / 2 : ℝ) = 0 - Real.log (2 : ℝ) := by rw [Real.log_div (show (1 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num), Real.log_one]
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAHalf
