module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntegerSign

theorem integer_sign (m : ℤ) :
    (0 ≤ m ∨ 0 ≤ -m) := by
  -- 1. mun:numbers-integer-sign n := m
  have s1 : 0 ≤ m ∨ 0 ≤ -m := by first | exact (Parley.Items.Stdlib.Numbers.mun_integer_sign (n := m)) | exact ((Parley.Items.Stdlib.Numbers.mun_integer_sign (n := m))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_integer_sign (n := m)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_integer_sign (n := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_integer_sign (n := m)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.IntegerSign
