module

public import Parley.Items.Stdlib.Divisibility
public import Parley.Library

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition

theorem a_define_read_in_an_unfolded_definition (a : ℤ) (b : ℤ) (hH3 : a + 1 = 2 * b) :
    Even (a + 1) := by
  set e : ℝ := (a : ℝ) + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H3
  have s1 : e = 2 * (b : ℝ) := by
    have hH3_w : (a : ℝ) + 1 = 2 * (b : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) hH3; push_cast at h; linear_combination (norm := parley_norm) h
    parley_subst_at hD1 hH3_w
  -- 2. def:even n := a + 1, from D1, 1
  have s2 : Even (a + 1) := ((Parley.Items.Stdlib.Divisibility.def_even (n := a + 1))).mpr ⟨b, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnUnfoldedDefinition
