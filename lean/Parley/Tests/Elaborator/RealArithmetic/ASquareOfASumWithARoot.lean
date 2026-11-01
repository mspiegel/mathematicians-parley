module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumWithARoot

theorem a_square_of_a_sum_with_a_root :
    (1 + Real.sqrt (2 : ℝ)) ^ 2 = 3 + 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (1 + Real.sqrt (2 : ℝ)) ^ 2 = 3 + 2 * Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ASquareOfASumWithARoot
