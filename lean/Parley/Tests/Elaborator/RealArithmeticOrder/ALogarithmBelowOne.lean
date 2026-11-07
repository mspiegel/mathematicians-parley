module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmBelowOne

theorem a_logarithm_below_one :
    Real.log (2 : ℝ) < 1 := by
  -- 1. real arithmetic
  have s1 : Real.log (2 : ℝ) < 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ALogarithmBelowOne
