module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

theorem a_define_read_in_an_algebra_step (a : ℝ) (b : ℝ) (H3 : a + 1 = 2 * b) :
    a = 2 * b - 1 := by
  set e : ℝ := a + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * b := by parley_subst_at D1 H3
  -- 2. algebra, from D1, 1
  have s2 : a = 2 * b - 1 := by linear_combination (-1) * D1 + s1
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep
