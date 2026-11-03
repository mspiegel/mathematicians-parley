module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AChainThroughLogarithms

theorem a_chain_through_logarithms :
    Real.log (4 : ℝ) + Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) := by
  -- 1. calculation
  have s1 : Real.log (4 : ℝ) + Real.log (2 : ℝ) = 3 * Real.log (2 : ℝ) := by
    calc Real.log (4 : ℝ) + Real.log (2 : ℝ) = 2 * Real.log (2 : ℝ) + Real.log (2 : ℝ) := by parley_real
      _ = 3 * Real.log (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AChainThroughLogarithms
