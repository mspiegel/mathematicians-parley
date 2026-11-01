module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowARoot

theorem one_below_a_root :
    1 < Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : 1 < Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowARoot
