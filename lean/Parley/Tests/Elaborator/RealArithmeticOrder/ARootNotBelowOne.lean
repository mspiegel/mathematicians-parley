module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootNotBelowOne

theorem a_root_not_below_one :
    ¬ Real.sqrt (2 : ℝ) < 1 := by
  -- 1. real arithmetic
  have s1 : ¬ Real.sqrt (2 : ℝ) < 1 := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootNotBelowOne
