module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsSquare

theorem abs_square (x : ℝ) :
    abs x ^ 2 = x ^ 2 := by
  -- 1. mun:numbers-abs-square
  have s1 : abs x ^ 2 = x ^ 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_square (x := x))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_square (x := x)); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.AbsSquare
