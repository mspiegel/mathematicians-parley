module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmAboveZero

theorem a_logarithm_above_zero :
    0 < Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : 0 < Real.log (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmAboveZero
