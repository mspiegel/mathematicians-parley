module

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
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAProduct

theorem a_logarithm_of_a_product :
    Real.log (6 : ℝ) - Real.log (2 : ℝ) = Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  have hv1 : Real.log (6 : ℝ) = Real.log (2 : ℝ) + Real.log (3 : ℝ) := by rw [congrArg Real.log (show (6 : ℝ) = 2 * 3 by ring1), Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (3 : ℝ) ≠ 0 by norm_num)]
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAProduct
