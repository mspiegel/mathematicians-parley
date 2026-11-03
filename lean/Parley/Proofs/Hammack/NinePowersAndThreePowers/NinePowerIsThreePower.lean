module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero
public import Parley.Proofs.Hammack.NinePowersAndThreePowers.PositivePowerIsReal

/-! Written from proofs/hammack/nine-powers-and-three-powers.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower

theorem nine_power_is_three_power (m : ℤ) :
    (9 ^ m : ℚ) = 3 ^ (2 * m) := by
  -- 1. mun:nonneg-or-neg x := m
  have s1 : m ≥ 0 ∨ m < 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | exact ((Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := m)); parley_side)
  -- 2. mun:exponent-sum-integer a := 3, n := m
  have r109_1 : (3 : ℤ) ≠ 0 := by parley_arith
  have s2 : (3 ^ (m + m) : ℚ) = 3 ^ m * 3 ^ m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := (3 : ℚ)) (by parley_side) (m := m) (n := m)); parley_side)
  -- 3. substitute
  have s3 : (3 ^ (2 * m) : ℚ) = 3 ^ m * 3 ^ m := by
    have c1 : m + m = 2 * m := by parley_ring
    have c1_w : (m : ℚ) + (m : ℚ) = 2 * (m : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
    have row1 : (3 ^ (2 * m) : ℚ) = 3 ^ m * 3 ^ m := by first | parley_subst_at c1_w s2 | parley_subst_at c1 s2
    exact row1
  -- 4. cases, from 1
  have s4 : (9 ^ m : ℚ) = 3 ^ m * 3 ^ m := by
    rcases s1 with hC1 | hC2
    · skip
      -- 4.1. mun:nat0-as-int
      have r124_1 : 0 ≤ m := by parley_side
      have s4_1 : 0 ≤ m := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := m))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := m))).mpr (by parley_side); parley_side)
      lift m to ℕ using (id s4_1)
      -- 4.2. thm:nine-power-from-zero n := m, from 4.1
      have s4_2 : (9 ^ m : ℤ) = 3 ^ m * 3 ^ m := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)) | exact_mod_cast ((Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m))).symm | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := m)); parley_side)
      all_goals parley_side
    · skip
      -- 4.3. inequalities
      have s4_3 : -m > 0 := by parley_order
      -- 4.4. mun:nat0-as-int
      have r139_1 : -m ≥ 0 := by parley_side
      have s4_4 : 0 ≤ -m := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := -m))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := -m))).mpr (by parley_side); parley_side)
      -- 4.5. thm:nine-power-from-zero n := −m, from 4.4
      have s4_5 : (9 ^ (-m) : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)) | exact_mod_cast ((Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat))).symm | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerFromZero.nine_power_from_zero (n := (-m).toNat)); parley_side)
      -- 4.6. thm:positive-power-is-real a := 9
      have r146_1 : (9 : ℤ) > 0 := by parley_arith
      -- 4.7. thm:positive-power-is-real a := 3
      have r150_1 : (3 : ℤ) > 0 := by parley_arith
      -- 4.8. mun:power-positive a := 9
      have r154_1 : (0 : ℤ) < 9 := by parley_arith
      have s4_8 : (9 ^ m : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (9 : ℚ)) (m := m) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (9 : ℚ)) (m := m) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (9 : ℚ)) (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (9 : ℚ)) (m := m) (by parley_side)); parley_side)
      -- 4.9. mun:power-positive a := 3
      have r158_1 : (0 : ℤ) < 3 := by parley_arith
      have s4_9 : (3 ^ m : ℚ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := m) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := m) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_positive (a := (3 : ℚ)) (m := m) (by parley_side)); parley_side)
      -- 4.10. substitute
      have r162_1 : (9 : ℤ) ≠ 0 := by parley_arith
      have s4_10 : (1 / 9 ^ m : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by
        have c1 : (9 ^ (-m) : ℚ) = 1 / 9 ^ m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (9 : ℚ)) (by parley_side) (m := m)); parley_side)
        have row1 : (1 / 9 ^ m : ℚ) = 3 ^ (-m) * 3 ^ (-m) := by parley_subst_at c1 s4_5
        exact row1
      -- 4.11. substitute
      have r168_1 : (3 : ℤ) ≠ 0 := by parley_arith
      have s4_11 : (1 / 9 ^ m : ℚ) = 1 / 3 ^ m * (1 / 3 ^ m) := by
        have c1 : (3 ^ (-m) : ℚ) = 1 / 3 ^ m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := (3 : ℚ)) (by parley_side) (m := m)); parley_side)
        have row1 : (1 / 9 ^ m : ℚ) = 1 / 3 ^ m * (1 / 3 ^ m) := by parley_subst_at c1 s4_10
        exact row1
      -- 4.12. inequalities
      have s4_12 : (9 ^ m : ℚ) ≠ 0 := by parley_side
      -- 4.13. inequalities
      have s4_13 : (3 ^ m : ℚ) ≠ 0 := by parley_side
      -- 4.14. algebra, from 4.6, 4.7, 4.11
      have r186_1 : (9 ^ m : ℚ) ≠ 0 := by parley_side
      have r186_2 : (3 ^ m : ℚ) ≠ 0 := by parley_side
      have s4_14 : (9 ^ m : ℚ) = 3 ^ m * 3 ^ m := by linear_combination (norm := parley_field) (-(3 ^ m) ^ 2 * 9 ^ m) * s4_11
      all_goals parley_side
  -- 5. thm:positive-power-is-real a := 3
  have r191_1 : (3 : ℤ) > 0 := by parley_arith
  -- 6. algebra, from 3, 4, 5
  have s6 : (9 ^ m : ℚ) = 3 ^ (2 * m) := by linear_combination (norm := parley_norm) (-1) * s3 + s4
  all_goals exact s6

end Parley.Proofs.Hammack.NinePowersAndThreePowers.NinePowerIsThreePower
