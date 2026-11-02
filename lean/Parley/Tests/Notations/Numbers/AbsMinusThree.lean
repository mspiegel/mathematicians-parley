module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.AbsMinusThree

theorem abs_minus_three :
    (abs (-3) : ℤ) = 3 := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) < 0 := by parley_arith
  -- 2. def:abs x := −3, from 1
  have s2 : (abs (-3) : ℤ) = -(-3) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := (-3 : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h)
  -- 3. calculation
  have s3 : (abs (-3) : ℤ) = 3 := by
    calc (abs (-3) : ℤ) = -(-3) := by parley_side
      _ = 3 := by norm_num
  all_goals parley_side

end Parley.Tests.Notations.Numbers.AbsMinusThree
