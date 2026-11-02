module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/odd-numbers-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum

theorem odd_numbers_sum (N : ℕ) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = (N : ℤ) ^ 2 := by
  set S : ℕ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (2 * j - 1 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → S k = (k : ℤ) ^ 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 1 = 1 ^ 2 := by
        calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (2 * j - 1 : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 2 * 1 - 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ))); parley_side)
          _ = 1 ^ 2 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r29_1 : (k : ℤ) ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (2 * ((k : ℤ) + 1) - 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (2 * j - 1 : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (2 * j - 1 : ℤ)) + (2 * ((k : ℤ) + 1) - 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = S k + (2 * ((k : ℤ) + 1) - 1) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. calculation
      have s1_3 : S (k + 1) = ((k : ℤ) + 1) ^ 2 := by
        calc S (k + 1) = S k + (2 * ((k : ℤ) + 1) - 1) := by parley_side
          _ = (k : ℤ) ^ 2 + (2 * ((k : ℤ) + 1) - 1) := by parley_subst hIH
          _ = ((k : ℤ) + 1) ^ 2 := by parley_ring
      all_goals parley_side
  -- 2. def:nat0 n := N
  have s2 : 0 < N ∨ (N : ℤ) = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.def_nat0 (n := (N : ℤ)))).mp (by parley_side); parley_side)
  -- 3. cases, from 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = (N : ℤ) ^ 2 := by
    rcases s2 with hC1 | hC2
    · skip
      -- 3.1. D1, from C1
      have s3_1 : (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = S N := by parley_side
      -- 3.2. calculation
      have s3_2 : (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = (N : ℤ) ^ 2 := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = S N := by parley_side
          _ = (N : ℤ) ^ 2 := by first | linear_combination (norm := parley_norm) (s1 N (by parley_side)) | (have h := (s1 N (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 N (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 N (by parley_side)) | exact_mod_cast ((s1 N (by parley_side))).symm | (have h := (s1 N (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 N (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 N (by parley_side)); parley_int_power h) | (have h := (s1 N (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      -- 3.3. mun:sum-single a := 0
      have s3_3 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 2 * 0 - 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ))); parley_side)
      -- 3.4. mun:sum-first n := 0
      have s3_4 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 2 * 0 - 1 + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := 0)); parley_side)
      -- 3.5. algebra, from 3.3, 3.4
      have s3_5 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by linear_combination (norm := parley_norm) s3_3 + (-1) * s3_4
      -- 3.6. calculation
      have s3_6 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 ^ 2 := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by parley_side
          _ = 0 ^ 2 := by norm_num
      -- 3.7. substitute N = 0 (C2) into line 3.6
      have s3_7 : (∑ k ∈ Finset.Icc (1 : ℤ) (N : ℤ), (2 * k - 1 : ℤ)) = (N : ℤ) ^ 2 := by parley_subst_at hC2 s3_6
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum
