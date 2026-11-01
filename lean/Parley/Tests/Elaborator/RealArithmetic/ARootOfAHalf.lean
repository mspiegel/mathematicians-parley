module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfAHalf

theorem a_root_of_a_half :
    2 * Real.sqrt (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : 2 * Real.sqrt (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootOfAHalf
