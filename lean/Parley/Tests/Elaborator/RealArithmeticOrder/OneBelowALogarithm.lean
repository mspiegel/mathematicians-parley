module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowALogarithm

theorem one_below_a_logarithm :
    1 < Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  have s1 : 1 < Real.log (3 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowALogarithm
