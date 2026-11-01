module

public import Parley.Library

/-! Written from tests/elaborator/both-directions.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BothDirections.OneMore

theorem one_more (n : ℤ) :
    (n + 1 = 3 ↔ n = 2) := by
  -- 1. both directions
  have s1 : n + 1 = 3 ↔ n = 2 := by
    constructor
    · skip
      intro D1
      -- 1.1. algebra, from D1
      have s1_1 : n = 2 := by linear_combination D1
      all_goals parley_side
    · skip
      intro D2
      -- 1.2. algebra, from D2
      have s1_2 : n + 1 = 3 := by linear_combination D2
      all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.BothDirections.OneMore
