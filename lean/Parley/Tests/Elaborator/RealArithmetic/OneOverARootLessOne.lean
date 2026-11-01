module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.OneOverARootLessOne

theorem one_over_a_root_less_one :
    1 / (Real.sqrt (3 : ℝ) - 1) = (Real.sqrt (3 : ℝ) + 1) / 2 := by
  -- 1. real arithmetic
  have s1 : 1 / (Real.sqrt (3 : ℝ) - 1) = (Real.sqrt (3 : ℝ) + 1) / 2 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.OneOverARootLessOne
