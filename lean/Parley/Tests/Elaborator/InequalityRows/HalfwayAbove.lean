module

public import Tactics

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.HalfwayAbove

theorem halfway_above (A : ℝ) (B : ℝ) (hH3 : A < B) :
    A < (A + B) / 2 := by
  -- 1. inequalities
  have s1 : A < (A + B) / 2 := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.InequalityRows.HalfwayAbove
