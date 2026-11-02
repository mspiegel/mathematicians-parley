module

public import LeanBridges
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep

/-! Written from proofs/hammack/reciprocal-product-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalProductSum

theorem reciprocal_product_sum (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / ((k : ℚ) * ((k : ℚ) + 1)) : ℚ)) = 1 - 1 / ((n : ℚ) + 1) := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on k starting at 1
  have s2 : ∀ k : ℕ, 0 < k → (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / ((k : ℚ) + 1) := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / (1 + 1) := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 / (1 * (1 + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ))); parley_side)
          _ = 1 - 1 / (1 + 1) := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 2.2. calculation
      have r43_1 : (k : ℤ) ≥ 1 := by parley_side
      have s2_2 : (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = 1 - 1 / ((k : ℚ) + 1 + 1) := by
        calc (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (1 / ((j : ℚ) * ((j : ℚ) + 1)) : ℚ)) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 1 / ((j : ℚ) * ((j : ℚ) + 1)))) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = 1 - 1 / ((k : ℚ) + 1) + 1 / (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1)) := by parley_subst hIH
          _ = 1 - 1 / ((k : ℚ) + 1 + 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)) | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep.reciprocal_step (m := k + 1) (by parley_side)); parley_side)
      all_goals parley_side
  -- 3. instantiate k := n in line 2
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / ((k : ℚ) * ((k : ℚ) + 1)) : ℚ)) = 1 - 1 / ((n : ℚ) + 1) := by first | linear_combination (norm := parley_norm) (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s2 n (by parley_side)) | exact_mod_cast ((s2 n (by parley_side))).symm | (have h := (s2 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); parley_int_power h) | (have h := (s2 n (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalProductSum
