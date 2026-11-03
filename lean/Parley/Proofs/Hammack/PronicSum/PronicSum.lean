module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/pronic-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PronicSum.PronicSum

theorem pronic_sum (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * ((k : ℚ) + 1) : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) / 3 := by
  set S : ℕ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (j * (j + 1) : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → (S k : ℚ) = (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) / 3 := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (S 1 : ℚ) = 1 * (1 + 1) * (1 + 2) / 3 := by
        calc (S 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) * ((j : ℚ) + 1) : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 1 * (1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) * ((j : ℚ) + 1))) (a := (1 : ℤ))); parley_side)
          _ = 1 * (1 + 1) * (1 + 2) / 3 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : (k : ℤ) ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (j * (j + 1) : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (j * (j + 1) : ℤ)) + ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j * (j + 1))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = S k + ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. calculation
      have s1_3 : (S (k + 1) : ℚ) = ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) * ((k : ℚ) + 1 + 2) / 3 := by
        calc (S (k + 1) : ℚ) = (S k : ℚ) + ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) := by parley_side
          _ = (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) / 3 + ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) := by parley_subst hIH
          _ = ((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) * ((k : ℚ) + 1 + 2) / 3 := by parley_ring
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * ((k : ℚ) + 1) : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) / 3 := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) * ((k : ℚ) + 1) : ℚ)) = (S n : ℚ) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) / 3 := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.PronicSum.PronicSum
