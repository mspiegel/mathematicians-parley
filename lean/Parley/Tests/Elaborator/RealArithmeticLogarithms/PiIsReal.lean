module

public import Tactics
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.PiIsReal

theorem pi_is_real :
    True := by
  -- 1. real arithmetic
  exact trivial

end Parley.Tests.Elaborator.RealArithmeticLogarithms.PiIsReal
