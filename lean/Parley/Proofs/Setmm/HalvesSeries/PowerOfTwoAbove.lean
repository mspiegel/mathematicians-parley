module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/setmm/halves-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove

theorem power_of_two_above (n : ℕ) (hH1 : 0 < n) :
    (n : ℤ) ≤ 2 ^ n := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → (k : ℤ) ≤ 2 ^ k := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (1 : ℤ) ≤ 2 ^ 1 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:power-nat a := 2, m := k
      have s1_2 : 0 < 2 ^ k := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := k))
      -- 1.3. inequalities, from IH, 1.2
      have s1_3 : (k : ℤ) + 1 ≤ 2 ^ k + 2 ^ k := by parley_side
      -- 1.4. calculation
      have s1_4 : (k : ℤ) + 1 ≤ 2 ^ (k + 1) := by
        calc (k : ℤ) + 1 ≤ 2 ^ k + 2 ^ k := by parley_side
          _ = 2 ^ k * 2 := by parley_ring
          _ = 2 ^ (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k))).symm
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : (n : ℤ) ≤ 2 ^ n := by first | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side))
  all_goals parley_side

end Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove
