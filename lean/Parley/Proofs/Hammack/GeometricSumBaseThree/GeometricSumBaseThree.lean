module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/geometric-sum-base-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GeometricSumBaseThree.GeometricSumBaseThree

theorem geometric_sum_base_three (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (3 ^ k : ℚ)) = (3 ^ (n + 1) - 3) / 2 := by
  set S : ℕ → ℚ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (3 ^ j : ℚ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → S k = (3 ^ (k + 1) - 3) / 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 1 = (3 ^ (1 + 1) - 3) / 2 := by
        calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (3 ^ j : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 3 ^ 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ))); parley_side)
          _ = (3 ^ (1 + 1) - 3) / 2 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : (k : ℤ) ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + 3 ^ (k + 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (3 ^ j : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (3 ^ j : ℚ)) + 3 ^ (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j : ℚ))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = S k + 3 ^ (k + 1) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. mun:exponent-step a := 3, m := k + 1
      have s1_3 : (3 ^ (k + 1 + 1) : ℤ) = 3 ^ (k + 1) * 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1)); parley_side)
      -- 1.4. calculation
      have s1_4 : S (k + 1) = (3 ^ (k + 1 + 1) - 3) / 2 := by
        calc S (k + 1) = S k + 3 ^ (k + 1) := by parley_side
          _ = (3 ^ (k + 1) - 3) / 2 + 3 ^ (k + 1) := by parley_subst hIH
          _ = (3 ^ (k + 1) * 3 - 3) / 2 := by parley_ring
          _ = (3 ^ (k + 1 + 1) - 3) / 2 := by
              have s1_3_w : (3 ^ (k + 1 + 1) : ℚ) = 3 ^ (k + 1) * 3 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1_3; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s1_3_w | parley_subst s1_3
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (3 ^ k : ℚ)) = (3 ^ (n + 1) - 3) / 2 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (3 ^ k : ℚ)) = S n := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (3 ^ (n + 1) - 3) / 2 := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.GeometricSumBaseThree.GeometricSumBaseThree
