module

public import Tactics

/-! Written from tests/docs/tri.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Tri.TriOne

theorem tri_one :
    (1 * (1 + 1) / 2 : ℚ) = 1 := by
  -- 1. calculation
  have s1 : (1 * (1 + 1) / 2 : ℚ) = 1 := by
    calc (1 * (1 + 1) / 2 : ℚ) = 1 * (1 + 1) / 2 := by parley_side
      _ = 1 := by norm_num
  all_goals exact s1

end Parley.Tests.Docs.Tri.TriOne
