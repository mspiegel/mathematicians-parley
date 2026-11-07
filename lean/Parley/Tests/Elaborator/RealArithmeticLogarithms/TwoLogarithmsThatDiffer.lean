module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer

theorem two_logarithms_that_differ :
    Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.log (2 : ℝ) ≠ Real.log (3 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.TwoLogarithmsThatDiffer
