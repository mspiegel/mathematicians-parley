module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootLessOneIsNotZero

theorem a_root_less_one_is_not_zero :
    Real.sqrt (2 : ℝ) - 1 ≠ 0 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) - 1 ≠ 0 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootLessOneIsNotZero
