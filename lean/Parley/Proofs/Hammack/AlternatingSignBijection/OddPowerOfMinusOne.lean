module

public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

theorem odd_power_of_minus_one (k : ℤ) (hH1 : 0 ≤ k) :
    ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
  -- 1. thm:even-power-of-minus-one
  have s1 : ((-1) ^ (2 * k).toNat : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k) (by parley_side)); parley_side)
  -- 2. calculation
  have s2 : ((-1) ^ (2 * k + 1).toNat : ℤ) = -1 := by
    calc ((-1) ^ (2 * k + 1).toNat : ℤ) = (-1) ^ (2 * k).toNat * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k) (by parley_side)); parley_side)
      _ = 1 * -1 := by parley_subst s1
      _ = -1 := by norm_num
  all_goals exact s2

end Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne
