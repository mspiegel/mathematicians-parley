module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/mersenne-prime-exponent.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound

theorem two_power_bound (d : ℕ) (hH1 : 0 < d) :
    2 ^ d ≥ (d : ℤ) + 1 := by
  -- 1. induction on m starting at 1
  have s1 : ∀ m : ℕ, 0 < m → 2 ^ m ≥ (m : ℤ) + 1 := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 1 : ℤ) ≥ 1 + 1 := by parley_arith
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. mun:exponent-step a := 2
      have s1_2 : (2 ^ (m + 1) : ℤ) = 2 ^ m * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := m)); parley_side)
      -- 1.3. inequalities
      have s1_3 : 2 ^ m * 2 ≥ ((m : ℤ) + 1) * 2 := by parley_side
      -- 1.4. inequalities, from K
      have s1_4 : ((m : ℤ) + 1) * 2 ≥ (m : ℤ) + 1 + 1 := by parley_side
      -- 1.5. transitivity, from 1.2, 1.3, 1.4
      have s1_5 : 2 ^ (m + 1) ≥ (m : ℤ) + 1 + 1 := by parley_side
      all_goals parley_side
  -- 2. instantiate m := d in line 1
  have s2 : 2 ^ d ≥ (d : ℤ) + 1 := by first | linarith [(s1 d (by parley_side))] | (have h := (s1 d (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 d (by parley_side)) | (have h := (s1 d (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.MersennePrimeExponent.TwoPowerBound
