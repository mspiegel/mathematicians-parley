module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiAboveZero

theorem pi_above_zero :
    0 < Real.pi := by
  -- 1. real arithmetic
  have s1 : 0 < Real.pi := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiAboveZero
