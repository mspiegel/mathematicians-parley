module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootBelowAFraction

theorem a_root_below_a_fraction :
    Real.sqrt (2 : ℝ) < 3 / 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) < 3 / 2 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootBelowAFraction
