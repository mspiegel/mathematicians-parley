module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.LogarithmsByTheirRatio

theorem logarithms_by_their_ratio :
    Real.log (3 : ℝ) < 2 * Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.log (3 : ℝ) < 2 * Real.log (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.LogarithmsByTheirRatio
