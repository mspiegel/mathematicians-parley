module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ASineBelowOne

theorem a_sine_below_one :
    Real.sin (Real.pi / 4) < 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 4) < 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ASineBelowOne
