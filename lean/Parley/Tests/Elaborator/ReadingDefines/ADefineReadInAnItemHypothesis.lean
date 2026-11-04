module

public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-defines.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnItemHypothesis

theorem a_define_read_in_an_item_hypothesis (a : ℝ) (hH2 : a + 1 > 0) :
    1 / (a + 1) > 0 := by
  set e : ℝ := a + 1 with hD1
  -- 1. substitute e = a + 1 (D1) into H2
  have s1 : e > 0 := by parley_subst_at hD1 hH2
  -- 2. mun:reciprocal-positive, from D1, 1
  have s2 : 1 / (a + 1) > 0 := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := a + 1) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := a + 1) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := a + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := a + 1) (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Tests.Elaborator.ReadingDefines.ADefineReadInAnItemHypothesis
