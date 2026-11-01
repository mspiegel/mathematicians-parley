module

public import Parley.Library

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero

theorem positive_so_not_zero (x : ℝ) (H2 : 0 < x) :
    x ≠ 0 := by
  -- 1. inequalities
  have s1 : x ≠ 0 := by parley_side
  parley_side

end Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero
