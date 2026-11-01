module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

theorem a_define_read_in_an_unfolded_definition (a : ℤ) (b : ℤ) (H3 : a + 1 = 2 * b) :
    Even (a + 1) := by
  set e : ℝ := (a : ℝ) + 1 with D1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * (b : ℝ) := by
    have H3_w : (a : ℝ) + 1 = 2 * (b : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) H3; push_cast at h; linear_combination h
    parley_subst_at D1 H3_w
  -- 2. def:even n := a + 1, from D1, 1
  have s2 : Even (a + 1) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a + 1))).mpr ⟨b, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition
