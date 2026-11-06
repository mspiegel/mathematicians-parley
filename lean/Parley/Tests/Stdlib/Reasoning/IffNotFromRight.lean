module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffNotFromRight

theorem iff_not_from_right (x : ℝ) (hH2 : x = 0 ↔ x ^ 2 = 0) (hH3 : x ^ 2 ≠ 0) :
    x ≠ 0 := by
  -- 1. mun:reasoning-iff-not-from-right, from H2, H3
  have s1 : x ≠ 0 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 0) (Q := x ^ 2 = 0) hH2 hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.IffNotFromRight
