module

public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine

theorem a_define_read_in_an_instantiated_line (a : ℝ) (H2 : ∀ x : ℝ, x + (a + 1) > x) :
    2 + (a + 1) > 2 := by
  set e : ℝ := a + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : ∀ x : ℝ, x + e > x := by intro x; parley_subst_at D1 H2
  -- 2. instantiate x := 2 in line 1, from D1
  have s2 : 2 + (a + 1) > 2 := by linarith [(s1 (2 : ℝ))]
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnInstantiatedLine
