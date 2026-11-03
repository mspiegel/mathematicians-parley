module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootAtMostItsValue

theorem a_root_at_most_its_value :
    Real.sqrt (4 : ℝ) ≤ 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (4 : ℝ) ≤ 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootAtMostItsValue
