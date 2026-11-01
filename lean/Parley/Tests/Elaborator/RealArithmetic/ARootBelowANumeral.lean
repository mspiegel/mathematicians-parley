module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootBelowANumeral

theorem a_root_below_a_numeral :
    Real.sqrt (4 : ℝ) < 3 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) < 3 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootBelowANumeral
