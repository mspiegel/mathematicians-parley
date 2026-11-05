module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerNat0

theorem power_nat0 (a : ℕ) (m : ℕ) :
    0 ≤ (a : ℤ) ^ (m + 1) := by
  -- 1. mun:numbers-power-nat0 m := m + 1
  have s1 : 0 ≤ (a : ℤ) ^ (m + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (m := m + 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (m := m + 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (m := m + 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (m := m + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (m := m + 1)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerNat0
