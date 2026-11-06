module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerAtLeastOne

theorem power_at_least_one (b : ℝ) (m : ℤ) (hH2 : 0 ≤ m) (hH3 : 1 ≤ b) :
    1 ≤ b ^ m.toNat := by
  -- 1. mun:numbers-power-at-least-one a := b, n := m, from H3
  have s1 : 1 ≤ b ^ m.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_at_least_one (a := b) (n := m) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerAtLeastOne
