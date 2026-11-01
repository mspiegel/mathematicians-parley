module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInACaseSplit

theorem a_define_read_in_a_case_split (a : ℝ) (H2 : a + 1 < 0 ∨ a + 1 > 0) :
    a + 1 ≠ 0 := by
  set e : ℝ := a + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e < 0 ∨ e > 0 := by parley_subst_at D1 H2
  -- 2. cases, from D1, 1
  have s2 : a + 1 ≠ 0 := by
    rcases s1 with C1 | C2
    · skip
      -- 2.1. inequalities
      have s2_1 : a + 1 ≠ 0 := by parley_side
      all_goals parley_side
    · skip
      -- 2.2. inequalities
      have s2_2 : a + 1 ≠ 0 := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInACaseSplit
