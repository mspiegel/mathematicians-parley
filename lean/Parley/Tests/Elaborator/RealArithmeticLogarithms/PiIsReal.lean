module

public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.PiIsReal

theorem pi_is_real :
    True := by
  -- 1. real arithmetic
  all_goals parley_side

end Parley.Tests.Elaborator.RealArithmeticLogarithms.PiIsReal
