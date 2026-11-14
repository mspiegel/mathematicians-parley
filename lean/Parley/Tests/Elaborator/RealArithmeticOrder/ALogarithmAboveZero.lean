module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmAboveZero

theorem a_logarithm_above_zero :
    0 < Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  have hf1 : Real.log (2 : ℝ) = Real.log (2 : ℝ) := by rw []
  have hf2 : (0 : ℝ) < Real.log (2 : ℝ) := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  linarith only [hf1, hf2]

end Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmAboveZero
