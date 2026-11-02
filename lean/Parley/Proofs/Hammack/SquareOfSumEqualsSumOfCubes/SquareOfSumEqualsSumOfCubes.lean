module

public import Tactics
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.SumFormula.SumFormula

/-! Written from proofs/hammack/square-of-sum-equals-sum-of-cubes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SquareOfSumEqualsSumOfCubes.SquareOfSumEqualsSumOfCubes

theorem square_of_sum_equals_sum_of_cubes (n : ℕ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℤ)) ^ 2 = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k ^ 3 : ℤ)) := by
  set C : ℕ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) (m : ℤ), (j ^ 3 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℕ, 0 < k → (C k : ℚ) = ((k : ℚ) * ((k : ℚ) + 1) / 2) ^ 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := h_k
    induction k, h_k using Nat.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (C 1 : ℚ) = (1 * (1 + 1) / 2) ^ 2 := by
        calc (C 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), ((j : ℚ) ^ 3 : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = 1 ^ 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (j : ℚ) ^ 3)) (a := (1 : ℤ))); parley_side)
          _ = (1 * (1 + 1) / 2) ^ 2 := by norm_num
      all_goals parley_side
    | succ k hK hIH =>
      -- 1.2. calculation
      have r29_1 : (k : ℤ) ≥ 1 := by parley_side
      have s1_2 : C (k + 1) = C k + ((k : ℤ) + 1) ^ 3 := by
        calc C (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) ((k : ℤ) + 1), (j ^ 3 : ℤ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) (k : ℤ), (j ^ 3 : ℤ)) + ((k : ℤ) + 1) ^ 3 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => j ^ 3)) (a := (1 : ℤ)) (n := (k : ℤ)) (by parley_side)); parley_side)
          _ = C k + ((k : ℤ) + 1) ^ 3 := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. calculation
      have s1_3 : (C (k + 1) : ℚ) = (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) / 2) ^ 2 := by
        calc (C (k + 1) : ℚ) = (C k : ℚ) + ((k : ℚ) + 1) ^ 3 := by parley_side
          _ = ((k : ℚ) * ((k : ℚ) + 1) / 2) ^ 2 + ((k : ℚ) + 1) ^ 3 := by parley_subst hIH
          _ = (((k : ℚ) + 1) * ((k : ℚ) + 1 + 1) / 2) ^ 2 := by parley_ring
      all_goals parley_side
  -- 2. thm:sum-formula
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) : ℚ)) = (n : ℚ) * ((n : ℚ) + 1) / 2 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side))).symm | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Wiedijk.SumFormula.SumFormula.sum_formula (n := n) (by parley_side)); parley_side)
  -- 3. calculation
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k : ℤ)) ^ 2 = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (k ^ 3 : ℤ)) := by
    qify
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) : ℚ)) ^ 2 = ((n : ℚ) * ((n : ℚ) + 1) / 2) ^ 2 := by parley_subst s2
      _ = (C n : ℚ) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), ((k : ℚ) ^ 3 : ℚ)) := by first | (simp only [hD1]; push_cast; norm_num; done) | parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.SquareOfSumEqualsSumOfCubes.SquareOfSumEqualsSumOfCubes
