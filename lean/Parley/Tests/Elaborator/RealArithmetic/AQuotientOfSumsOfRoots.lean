module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfSumsOfRoots

theorem a_quotient_of_sums_of_roots :
    (Real.sqrt (6 : ℝ) + Real.sqrt (2 : ℝ)) / (Real.sqrt (3 : ℝ) + 1) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (6 : ℝ) + Real.sqrt (2 : ℝ)) / (Real.sqrt (3 : ℝ) + 1) = Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfSumsOfRoots
