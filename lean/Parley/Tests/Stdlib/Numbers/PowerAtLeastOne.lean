module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerAtLeastOne

theorem power_at_least_one (b : ℝ) (m : ℕ) (hH3 : 1 ≤ b) :
    1 ≤ b ^ m := by
  -- 1. mun:numbers-power-at-least-one a := b, n := m, from H3
  have s1 : 1 ≤ b ^ m := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerAtLeastOne
