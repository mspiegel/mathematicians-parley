module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-of-one-minus-halves.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour

theorem power_of_two_at_least_four (m : ℕ) (hH1 : 0 < m) :
    (2 ^ (m + 1) : ℤ) ≥ 4 := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → (2 ^ (k + 1) : ℤ) ≥ 4 := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 ^ (1 + 1) : ℤ) ≥ 4 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:power-nat a := 2, m := k + 1
      have s1_2 : 0 < 2 ^ (k + 1) := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k + 1)); parley_side)
      -- 1.3. inequalities, from 1.2
      have s1_3 : (2 ^ (k + 1) : ℤ) ≥ 0 := by parley_side
      -- 1.4. inequalities, from IH, 1.3
      have s1_4 : (2 ^ (k + 1) + 2 ^ (k + 1) : ℤ) ≥ 4 := by parley_side
      -- 1.5. calculation
      have s1_5 : (2 ^ (k + 1 + 1) : ℤ) ≥ 4 := by
        calc (2 ^ (k + 1 + 1) : ℤ) = 2 ^ (k + 1) * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); parley_side)
          _ = 2 ^ (k + 1) + 2 ^ (k + 1) := by parley_ring
          _ ≥ 4 := by parley_side
      all_goals parley_side
  -- 2. instantiate k := m in line 1
  have s2 : (2 ^ (m + 1) : ℤ) ≥ 4 := by first | linarith [(s1 m (by parley_side))] | (have h := (s1 m (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 m (by parley_side)) | (have h := (s1 m (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.ProductOfOneMinusHalves.PowerOfTwoAtLeastFour
