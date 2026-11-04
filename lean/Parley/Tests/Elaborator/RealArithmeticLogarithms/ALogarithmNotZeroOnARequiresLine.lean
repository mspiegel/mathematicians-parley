module

public import AlgebraTactics
public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmNotZeroOnARequiresLine

theorem a_logarithm_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.log (2 : ℝ) / Real.log (2 : ℝ) = a := by
  -- 1. algebra
  have r83_1 : Real.log (2 : ℝ) ≠ 0 := by parley_real
  have s1 : a * Real.log (2 : ℝ) / Real.log (2 : ℝ) = a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmNotZeroOnARequiresLine
