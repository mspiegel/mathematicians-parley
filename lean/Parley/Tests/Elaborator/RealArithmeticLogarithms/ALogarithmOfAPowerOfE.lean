module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPowerOfE

theorem a_logarithm_of_a_power_of_e :
    Real.log (Real.exp 1 ^ 3) = 3 := by
  -- 1. real arithmetic
  have s1 : Real.log (Real.exp 1 ^ 3) = 3 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPowerOfE
