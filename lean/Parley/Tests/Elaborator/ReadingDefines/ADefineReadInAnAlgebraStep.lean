module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep

theorem a_define_read_in_an_algebra_step (a : ℝ) (b : ℝ) (hH3 : a + 1 = 2 * b) :
    a = 2 * b - 1 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * b := by parley_subst_at hD1 hH3
  -- 2. algebra, from D1, 1
  have s2 : a = 2 * b - 1 := by
    try simp only [hD1] at *
    try push_cast at *
    linear_combination s1
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnAlgebraStep
