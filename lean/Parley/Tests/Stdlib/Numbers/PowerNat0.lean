module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Core
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerNat0

theorem power_nat0 (a : ℤ) (hH1 : 0 ≤ a) (m : ℤ) (hH2 : 0 ≤ m) :
    0 ≤ a ^ (m + 1).toNat := by
  -- 1. mun:numbers-power-nat0 m := m + 1
  have s1 : 0 ≤ a ^ (m + 1).toNat := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerNat0
