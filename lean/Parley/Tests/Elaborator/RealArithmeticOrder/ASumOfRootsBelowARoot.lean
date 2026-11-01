module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ASumOfRootsBelowARoot

theorem a_sum_of_roots_below_a_root :
    Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) < Real.sqrt (10 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) < Real.sqrt (10 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmeticOrder.ASumOfRootsBelowARoot
