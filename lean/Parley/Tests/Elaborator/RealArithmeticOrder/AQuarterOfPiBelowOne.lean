module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.AQuarterOfPiBelowOne

theorem a_quarter_of_pi_below_one :
    Real.pi / 4 < 1 := by
  -- 1. real arithmetic
  have s1 : Real.pi / 4 < 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.AQuarterOfPiBelowOne
