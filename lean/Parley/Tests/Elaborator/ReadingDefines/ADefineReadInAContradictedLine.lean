module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAContradictedLine

theorem a_define_read_in_a_contradicted_line (a : ℝ) (H2 : a + 1 ≠ 0) :
    a ≠ -1 := by
  set e : ℝ := a + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e ≠ 0 := by parley_subst_at D1 H2
  -- 2. contradiction
  have s2 : a ≠ -1 := by
    by_contra hc_S
    have S : a = -1 := by parley_suppose hc_S
    -- 2.1. algebra, from D1, S
    have s2_1 : a + 1 = 0 := by linear_combination S
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAContradictedLine
