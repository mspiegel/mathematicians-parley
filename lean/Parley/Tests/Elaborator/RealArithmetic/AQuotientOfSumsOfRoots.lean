module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfSumsOfRoots

theorem a_quotient_of_sums_of_roots :
    (Real.sqrt (6 : ℝ) + Real.sqrt (2 : ℝ)) / (Real.sqrt (3 : ℝ) + 1) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (6 : ℝ) + Real.sqrt (2 : ℝ)) / (Real.sqrt (3 : ℝ) + 1) = Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfSumsOfRoots
