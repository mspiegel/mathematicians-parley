module

public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven

theorem sign_of_even (n : ℕ) (hH1 : 0 < n) (hH2 : Even (n : ℤ)) :
    ((-1) ^ n : ℤ) = 1 := by
  -- 1. obtain k: def:even, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_even (n := (n : ℤ)))).mp (by parley_side)
  -- 2. inequalities, from H1
  have s2 : (n : ℤ) ≥ 1 := by parley_side
  -- 3. substitute n = 2·k (line 1) into line 2
  have s3 : 2 * k ≥ 1 := by parley_subst_at s1 s2
  -- 4. inequalities, from 3
  have s4 : 2 * k > 0 := by parley_side
  -- 5. inequalities
  have s5 : k > 0 := by parley_side
  -- 6. mun:pos-int-nat m := k, from 5
  have s6 : 0 < k := by first | exact (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_pos_int_nat (m := k) (by parley_side)); parley_side)
  lift k to ℕ using s6.le
  -- 7. thm:even-power-of-minus-one, from 6
  have s7 : ((-1) ^ (2 * k) : ℤ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k))).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.EvenPowerOfMinusOne.even_power_of_minus_one (k := k)); parley_side)
  -- 8. substitute 2·k = n (line 1) into line 7
  have s8 : ((-1) ^ n : ℤ) = 1 := by parley_subst_at s1 s7
  all_goals parley_side

end Parley.Proofs.Hammack.AlternatingSignBijection.SignOfEven
