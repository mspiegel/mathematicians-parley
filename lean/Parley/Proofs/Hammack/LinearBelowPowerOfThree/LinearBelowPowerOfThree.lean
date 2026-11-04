module

public import ArithTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/linear-below-power-of-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree

theorem linear_below_power_of_three (n : ℕ) (hH1 : 0 < n) :
    2 * (n : ℤ) + 1 ≤ 3 ^ n := by
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → 2 * (k : ℤ) + 1 ≤ 3 ^ k := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. arithmetic
      have s1_1 : (2 * 1 + 1 : ℤ) ≤ 3 ^ 1 := by parley_arith
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. mun:exponent-step a := 3
      have s1_2 : (3 ^ (k + 1) : ℤ) = 3 ^ k * 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k)); parley_side)
      -- 1.3. inequalities
      have s1_3 : 6 * (k : ℤ) + 3 ≤ 3 ^ k * 3 := by parley_order
      -- 1.4. inequalities, from K
      have s1_4 : 0 < (k : ℤ) := by parley_order
      -- 1.5. inequalities
      have s1_5 : 2 * ((k : ℤ) + 1) + 1 ≤ 6 * (k : ℤ) + 3 := by parley_order
      -- 1.6. transitivity, from 1.5, 1.3, 1.2
      have s1_6 : 2 * ((k : ℤ) + 1) + 1 ≤ 3 ^ (k + 1) := by parley_order
      all_goals parley_side
  -- 2. instantiate k := n in line 1
  have s2 : 2 * (n : ℤ) + 1 ≤ 3 ^ n := by first | linarith [(s1 n (by parley_side))] | (have h := (s1 n (by parley_side)); push_cast at h; linarith) | exact_mod_cast (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.LinearBelowPowerOfThree.LinearBelowPowerOfThree
