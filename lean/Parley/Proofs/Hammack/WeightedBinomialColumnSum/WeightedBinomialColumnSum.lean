module

public import LeanBridges
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/weighted-binomial-column-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialColumnSum.WeightedBinomialColumnSum

theorem weighted_binomial_column_sum (m : ℕ) (hH1 : 0 < m) (n : ℕ) (hH2 : 0 < n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (n : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (n : ℤ) + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + (n : ℤ) + 1) ((m : ℤ) + 2) : ℤ) := by
  -- 1. induction on j starting at 0
  have s1 : ∀ j : ℕ, (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (j : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 2) : ℤ) := by
    intro j
    induction j with
    | zero =>
      -- 1.1. mun:sum-single a := 0
      have s1_1 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = 0 * (LeanBridges.Counting.choose (m : ℤ) (m : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h)
      -- 1.2. inequalities
      have s1_2 : (m : ℤ) + 1 < (m : ℤ) + 2 := by parley_side
      -- 1.3. def:C n := m + 1, k := m + 2, from 1.2
      have s1_3 : (LeanBridges.Counting.choose ((m : ℤ) + 1) ((m : ℤ) + 2) : ℤ) = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := m + 1) (k := (m : ℤ) + 2)) (by parley_side); qify; linear_combination (norm := parley_norm) h)
      -- 1.4. algebra, from 1.1, 1.3
      have s1_4 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = 0 * (LeanBridges.Counting.choose ((m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + 1) ((m : ℤ) + 2) : ℤ) := by linear_combination (norm := parley_norm) s1_1 + s1_3
      all_goals parley_side
    | succ j hIH =>
      -- 1.5. mun:sum-extended a := 0, n := j
      have r35_1 : (j : ℤ) ≥ 0 := by parley_side
      have s1_5 : (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) + ((j : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + ((j : ℤ) + 1)) (m : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (j : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h)
      -- 1.6. substitute
      have s1_6 : (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) + ((j : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) (m : ℤ) : ℤ) := by
        have c1 : (m : ℤ) + ((j : ℤ) + 1) = (m : ℤ) + (j : ℤ) + 1 := by parley_ring
        have row1 : (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (j : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) + ((j : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) (m : ℤ) : ℤ) := by parley_subst_at c1 s1_5
        exact row1
      -- 1.7. thm:pascal n := m + j + 1, k := m + 1
      have s1_7 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1 - 1) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 1)); qify; linear_combination (norm := parley_norm) h)
      -- 1.8. substitute
      have s1_8 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) (m : ℤ) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by
        have c1 : (m : ℤ) + 1 - 1 = (m : ℤ) := by parley_ring
        have row1 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) (m : ℤ) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by parley_subst_at c1 s1_7
        exact row1
      -- 1.9. thm:pascal n := m + j + 1, k := m + 2
      have s1_9 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 2) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 2 - 1) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 2) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + j + 1) (k := (m : ℤ) + 2)); qify; linear_combination (norm := parley_norm) h)
      -- 1.10. substitute
      have s1_10 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 2) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 2) : ℤ) := by
        have c1 : (m : ℤ) + 2 - 1 = (m : ℤ) + 1 := by parley_ring
        have row1 : (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 2) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1) ((m : ℤ) + 1) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 2) : ℤ) := by parley_subst_at c1 s1_9
        exact row1
      -- 1.11. algebra, from IH, 1.6, 1.8, 1.10
      have s1_11 : (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = ((j : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + (j : ℤ) + 1 + 1) ((m : ℤ) + 2) : ℤ) := by linear_combination (norm := parley_norm) hIH + s1_6 + ((j : ℤ) + 1) * s1_8 + (-1) * s1_10
      -- 1.12. algebra
      have s1_12 : (m : ℤ) + (j : ℤ) + 1 + 1 = (m : ℤ) + ((j : ℤ) + 1) + 1 := by parley_ring
      -- 1.13. substitute (m + j + 1) + 1 = m + (j + 1) + 1 (line 1.12) into line 1.11
      have s1_13 : (∑ k ∈ Finset.Icc (0 : ℤ) ((j : ℤ) + 1), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = ((j : ℤ) + 1) * (LeanBridges.Counting.choose ((m : ℤ) + ((j : ℤ) + 1) + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + ((j : ℤ) + 1) + 1) ((m : ℤ) + 2) : ℤ) := by parley_subst_at s1_12 s1_11
      all_goals parley_side
  -- 2. instantiate j := n in line 1
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), k * (LeanBridges.Counting.choose ((m : ℤ) + k) (m : ℤ) : ℤ)) = (n : ℤ) * (LeanBridges.Counting.choose ((m : ℤ) + (n : ℤ) + 1) ((m : ℤ) + 1) : ℤ) - (LeanBridges.Counting.choose ((m : ℤ) + (n : ℤ) + 1) ((m : ℤ) + 2) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Proofs.Hammack.WeightedBinomialColumnSum.WeightedBinomialColumnSum
