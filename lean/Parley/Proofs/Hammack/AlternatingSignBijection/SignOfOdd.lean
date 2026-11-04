module

public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne

/-! Written from proofs/hammack/alternating-sign-bijection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd

theorem sign_of_odd (n : ℕ) (hH1 : 0 < n) (hH2 : Odd (n : ℤ)) :
    ((-1) ^ n : ℤ) = -1 := by
  -- 1. obtain k: def:odd, from H2
  obtain ⟨k, s1⟩ := ((Parley.Items.Stdlib.Divisibility.def_odd (n := (n : ℤ)))).mp (by parley_side)
  -- 2. inequalities, from H1
  have s2 : (n : ℤ) ≥ 1 := by parley_order
  -- 3. substitute n = 2·k + 1 (line 1) into line 2
  have s3 : 2 * k + 1 ≥ 1 := by parley_subst_at s1 s2
  -- 4. inequalities
  have s4 : k ≥ 0 := by parley_order
  -- 5. mun:nat0-as-int n := k, from 4
  have s5 : 0 ≤ k := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := k))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_nat0_as_int (n := k))).mpr (by parley_side); parley_side)
  lift k to ℕ using (id s5)
  -- 6. thm:odd-power-of-minus-one, from 5
  have s6 : ((-1) ^ (2 * k + 1) : ℤ) = -1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)) | exact_mod_cast ((Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k))).symm | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.AlternatingSignBijection.OddPowerOfMinusOne.odd_power_of_minus_one (k := k)); parley_side)
  -- 7. substitute 2·k + 1 = n (line 1) into line 6
  have s7 : ((-1) ^ n : ℤ) = -1 := by parley_subst_at s1 s6
  all_goals exact s7

end Parley.Proofs.Hammack.AlternatingSignBijection.SignOfOdd
