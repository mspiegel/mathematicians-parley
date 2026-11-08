module

public import Tactics
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootThatIsReal

theorem a_root_that_is_real :
    True := by
  -- 1. real arithmetic
  exact trivial

end Parley.Tests.Elaborator.RealArithmetic.ARootThatIsReal
