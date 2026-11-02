module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-eight-i-minus-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfEightIMinusFive.SumOfEightIMinusFive

theorem sum_of_eight_i_minus_five (n : ℕ) (hH1 : 0 < n) :
    (∑ i ∈ Finset.Icc (1 : ℤ) (n : ℤ), (8 * i - 5 : ℤ)) = 4 * (n : ℤ) ^ 2 - (n : ℤ) := by
  set S : ℕ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (8 * j - 5 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → S k = 4 * (k : ℤ) ^ 2 - (k : ℤ) := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 1 = 4 * 1 ^ 2 - 1 := by
        calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (8 * j - 5 : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 8 * 1 - 5 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ))); parley_side)
          _ = 4 * 1 ^ 2 - 1 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : (k : ℤ) ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (8 * ((k : ℤ) + 1) - 5) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (8 * j - 5 : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (8 * j - 5 : ℤ)) + (8 * ((k : ℤ) + 1) - 5) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = S k + (8 * ((k : ℤ) + 1) - 5) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. calculation
      have s1_3 : S (k + 1) = 4 * ((k : ℤ) + 1) ^ 2 - ((k : ℤ) + 1) := by
        calc S (k + 1) = S k + (8 * ((k : ℤ) + 1) - 5) := by parley_side
          _ = 4 * (k : ℤ) ^ 2 - (k : ℤ) + (8 * ((k : ℤ) + 1) - 5) := by parley_subst hIH
          _ = 4 * ((k : ℤ) + 1) ^ 2 - ((k : ℤ) + 1) := by parley_ring
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ i ∈ Finset.Icc (1 : ℤ) (n : ℤ), (8 * i - 5 : ℤ)) = 4 * (n : ℤ) ^ 2 - (n : ℤ) := by
    calc (∑ i ∈ Finset.Icc (1 : ℤ) (n : ℤ), (8 * i - 5 : ℤ)) = S n := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      _ = 4 * (n : ℤ) ^ 2 - (n : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.SumOfEightIMinusFive.SumOfEightIMinusFive
