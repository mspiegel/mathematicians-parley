module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPower

theorem a_logarithm_of_a_power :
    Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPower
