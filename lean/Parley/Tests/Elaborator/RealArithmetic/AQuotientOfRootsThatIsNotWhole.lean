module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsNotWhole

theorem a_quotient_of_roots_that_is_not_whole :
    ¬ (∃ m : ℤ, (m : ℝ) = Real.sqrt (2 : ℝ) / Real.sqrt (8 : ℝ)) := by
  -- 1. real arithmetic
  have s1 : ¬ (∃ m : ℤ, (m : ℝ) = Real.sqrt (2 : ℝ) / Real.sqrt (8 : ℝ)) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsNotWhole
