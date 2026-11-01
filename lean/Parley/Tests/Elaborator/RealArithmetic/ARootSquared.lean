module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootSquared

theorem a_root_squared :
    Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) = 2 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootSquared
