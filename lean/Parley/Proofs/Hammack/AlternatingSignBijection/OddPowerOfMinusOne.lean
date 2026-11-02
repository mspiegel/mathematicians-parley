module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

theorem odd_power_of_minus_one (k : ℕ) :
    ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
  -- 1. thm:even-power-of-minus-one
  have s1 : ((-1) ^ (2 * k) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k))).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); qify; linear_combination (norm := parley_norm) h)
  -- 2. calculation
  have s2 : ((-1) ^ (2 * k + 1) : ℤ) = -1 := by
    calc ((-1) ^ (2 * k + 1) : ℤ) = (-1) ^ (2 * k) * -1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (-1 : ℤ)) (m := 2 * k)); qify; linear_combination (norm := parley_norm) h)
      _ = 1 * -1 := by parley_subst s1
      _ = -1 := by norm_num
  all_goals parley_side

end Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne
