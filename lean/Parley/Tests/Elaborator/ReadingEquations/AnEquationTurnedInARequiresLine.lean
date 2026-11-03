module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInARequiresLine

theorem an_equation_turned_in_a_requires_line (x : ℝ) (hH2 : 0 = x ^ 2) :
    x = 0 := by
  -- 1. mun:square-zero
  have r168_1 : x ^ 2 = 0 := by parley_side
  have s1 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_zero (x := x) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInARequiresLine
