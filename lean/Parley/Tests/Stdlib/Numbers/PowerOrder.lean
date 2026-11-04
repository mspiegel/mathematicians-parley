module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOrder

theorem power_order (a : ℝ) (m : ℤ) (n : ℤ) (hH4 : a > 1) :
    (m < n ↔ a ^ m < a ^ n) := by
  -- 1. mun:numbers-power-order, from H4
  have s1 : m < n ↔ a ^ m < a ^ n := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOrder
