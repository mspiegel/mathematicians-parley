module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Nonzero

theorem nat0_nonzero (m : ℤ) (hH1 : 0 ≤ m) (hH2 : m ≠ 0) :
    0 < m := by
  -- 1. mun:numbers-nat0-nonzero, from H2
  have s1 : 0 < m := by first | exact (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side) hH2) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side) hH2)).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side) hH2) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side) hH2) | (have h := (Parley.Items.Stdlib.Numbers.mun_nat0_nonzero (m := m) (by parley_side) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.Nat0Nonzero
