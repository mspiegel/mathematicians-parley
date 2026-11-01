module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootWithASquarePart

theorem a_root_with_a_square_part :
    Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootWithASquarePart
