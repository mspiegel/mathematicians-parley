module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf

/-! Written from proofs/hammack/five-divides-power-of-two-multiple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesPowerOfTwoMultiple

theorem five_divides_power_of_two_multiple (a : ℤ) (n : ℕ) (hH2 : 0 < n) (hH3 : (5 : ℤ) ∣ 2 ^ n * a) :
    (5 : ℤ) ∣ a := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, ∀ c : ℤ, (5 : ℤ) ∣ 2 ^ k * c → (5 : ℤ) ∣ c := by
    intro k
    induction k with
    | zero =>
      intro c
      intro hA
      -- 1.1. arithmetic
      have s1_1 : (2 ^ 0 : ℤ) = 1 := by parley_arith
      -- 1.2. substitute 2^0 = 1 (line 1.1) into A
      have s1_2 : (5 : ℤ) ∣ 1 * c := by parley_subst_at s1_1 hA
      -- 1.3. restate 1.2
      have s1_3 : (5 : ℤ) ∣ c := by parley_side
      all_goals parley_side
    | succ k hIH =>
      intro c
      intro hA
      -- 1.4. mun:exponent-step a := 2, m := k
      have s1_4 : (2 ^ (k + 1) : ℤ) = 2 ^ k * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k)); parley_side)
      -- 1.5. algebra, from 1.4
      have s1_5 : 2 ^ (k + 1) * c = 2 ^ k * (2 * c) := by linear_combination (norm := parley_norm) (c) * s1_4
      -- 1.6. substitute 2^(k + 1)·c = 2^k·(2·c) (line 1.5) into A
      have s1_6 : (5 : ℤ) ∣ 2 ^ k * (2 * c) := by parley_subst_at s1_5 hA
      -- 1.7. instantiate c := 2·c in IH, from 1.6
      have s1_7 : (5 : ℤ) ∣ 2 * c := by first | exact (hIH (2 * c) (by parley_side)) | exact ((hIH (2 * c) (by parley_side))).symm | simpa using (hIH (2 * c) (by parley_side)) | exact_mod_cast (hIH (2 * c) (by parley_side)) | (have h := (hIH (2 * c) (by parley_side)); parley_side)
      -- 1.8. thm:five-divides-half b := c, from 1.7
      have s1_8 : (5 : ℤ) ∣ c := by first | exact (Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) (by parley_side)) | exact ((Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) (by parley_side))).symm | simpa using (Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) (by parley_side)) | exact_mod_cast (Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) (by parley_side)) | (have h := (Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesHalf.five_divides_half (b := c) (by parley_side)); parley_side)
      all_goals parley_side
  -- 2. instantiate k := n, c := a in line 1, from H3
  have s2 : (5 : ℤ) ∣ a := by first | exact (s1 n a (by parley_side)) | exact ((s1 n a (by parley_side))).symm | simpa using (s1 n a (by parley_side)) | exact_mod_cast (s1 n a (by parley_side)) | (have h := (s1 n a (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.FiveDividesPowerOfTwoMultiple.FiveDividesPowerOfTwoMultiple
