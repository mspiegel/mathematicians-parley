module

public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/geometric-sum-base-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo

theorem geometric_sum_base_two (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k : ℚ)) = 2 ^ (n + 1) - 1 := by
  set S : ℕ → ℚ := fun m => ∑ j ∈ Finset.Icc (0 : ℤ) (m : ℤ), (2 ^ j : ℚ) with hD1
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℕ, S k = 2 ^ (k + 1) - 1 := by
    intro k
    induction k with
    | zero =>
      -- 1.1. calculation
      have s1_1 : S 0 = 2 ^ 1 - 1 := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 ^ j : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 2 ^ 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ))); parley_side)
          _ = 2 ^ 1 - 1 := by norm_num
      all_goals parley_side
    | succ k hIH =>
      -- 1.2. calculation
      have r28_1 : (k : ℤ) ≥ 0 := by parley_side
      have s1_2 : S (k + 1) = S k + 2 ^ (k + 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) ((k : ℤ) + 1), (2 ^ j : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), (2 ^ j : ℚ)) + 2 ^ (k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j : ℚ))) (a := (0 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = S k + 2 ^ (k + 1) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. mun:exponent-step a := 2, m := k + 1
      have s1_3 : (2 ^ (k + 1 + 1) : ℤ) = 2 ^ (k + 1) * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1)); parley_side)
      -- 1.4. calculation
      have s1_4 : S (k + 1) = 2 ^ (k + 1 + 1) - 1 := by
        calc S (k + 1) = S k + 2 ^ (k + 1) := by parley_side
          _ = 2 ^ (k + 1) - 1 + 2 ^ (k + 1) := by parley_subst hIH
          _ = 2 ^ (k + 1) * 2 - 1 := by parley_ring
          _ = 2 ^ (k + 1 + 1) - 1 := by
              have s1_3_w : (2 ^ (k + 1 + 1) : ℚ) = 2 ^ (k + 1) * 2 := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1_3; push_cast at h; linear_combination (norm := parley_norm) h
              first | parley_subst s1_3_w | parley_subst s1_3
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k : ℚ)) = 2 ^ (n + 1) - 1 := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (2 ^ k : ℚ)) = S n := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      _ = 2 ^ (n + 1) - 1 := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); parley_int_power h) | (have h := (s1 n); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo
