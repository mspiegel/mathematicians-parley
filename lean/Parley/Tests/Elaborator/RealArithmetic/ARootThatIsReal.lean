module

public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootThatIsReal

theorem a_root_that_is_real :
    True := by
  -- 1. real arithmetic
  all_goals parley_side

end Parley.Tests.Elaborator.RealArithmetic.ARootThatIsReal
