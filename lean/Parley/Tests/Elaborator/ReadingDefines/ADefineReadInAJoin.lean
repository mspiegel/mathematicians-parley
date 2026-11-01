module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAJoin

theorem a_define_read_in_a_join (a : ℝ) (H2 : a + 1 > 0) :
    a + 1 > 0 := by
  set e : ℝ := a + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := by parley_subst_at D1 H2
  -- 2. restate D1, 1
  have s2 : a + 1 > 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAJoin
