module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/elaborator/an-equation-turned-inside.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnEquationTurnedInside.AnEquationTurnedInside

theorem an_equation_turned_inside (x : ℝ) (y : ℝ) (hH3 : x = 1 ↔ y + 0 = 2) (hH4 : 2 ≠ y) :
    x ≠ 1 := by
  -- 1. mun:iff-not-from-right, from H3, H4
  have s1 : x ≠ 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_iff_not_from_right (P := x = 1) (Q := y + 0 = 2) hH3 (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.AnEquationTurnedInside.AnEquationTurnedInside
