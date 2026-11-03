module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen

theorem pi_squared_below_sixteen :
    Real.pi ^ 2 < 16 := by
  -- 1. real arithmetic
  have s1 : Real.pi ^ 2 < 16 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen
