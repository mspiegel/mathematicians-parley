module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsOne

theorem abs_one :
    (abs 1 : ℤ) = 1 := by
  -- 1. mun:numbers-abs-one
  have s1 : (abs 1 : ℤ) = 1 := by first | linear_combination (norm := parley_norm) Parley.Items.Stdlib.Numbers.mun_abs_one | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast Parley.Items.Stdlib.Numbers.mun_abs_one | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_one).symm | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; rify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; qify; linear_combination (norm := parley_norm) h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; parley_int_power h) | (have h := Parley.Items.Stdlib.Numbers.mun_abs_one; parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsOne
