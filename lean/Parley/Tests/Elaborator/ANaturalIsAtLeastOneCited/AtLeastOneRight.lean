module

public import Parley.Library

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight

theorem at_least_one_right (x : ℤ) (hH2 : x ≥ 1) :
    0 < x := by
  -- 1. inequalities, from H2
  have s1 : 0 < x := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight
