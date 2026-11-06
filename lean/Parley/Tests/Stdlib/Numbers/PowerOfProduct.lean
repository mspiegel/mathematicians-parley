module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfProduct

theorem power_of_product (y : ℂ) (z : ℂ) (k : ℤ) (hH3 : 0 ≤ k) :
    (y * z) ^ k.toNat = y ^ k.toNat * z ^ k.toNat := by
  -- 1. mun:numbers-power-of-product a := y, b := z, n := k
  have s1 : (y * z) ^ k.toNat = y ^ k.toNat * z ^ k.toNat := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOfProduct
