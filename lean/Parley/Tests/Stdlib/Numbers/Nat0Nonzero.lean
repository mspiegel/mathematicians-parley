module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Nonzero

theorem nat0_nonzero (m : ℕ) (hH2 : (m : ℤ) ≠ 0) :
    0 < m := by
  -- 1. mun:numbers-nat0-nonzero, from H2
  have s1 : 0 < m := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.Nat0Nonzero
