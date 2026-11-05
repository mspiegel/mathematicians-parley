module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-binomials-along-a-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal

theorem sum_of_binomials_along_a_diagonal (n : ℕ) (k : ℕ) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ))) :
    (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) = (LeanBridges.Counting.choose ((n : ℤ) + (k : ℤ) + 1) (k : ℤ) : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, S (m : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) := by
    intro m
    induction m with
    | zero =>
      -- 1.1. calculation
      have s1_1 : S 0 = (LeanBridges.Counting.choose ((n : ℤ) + 1) (0 : ℤ) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (LeanBridges.Counting.choose (n : ℤ) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n)); parley_side)
          _ = (LeanBridges.Counting.choose ((n : ℤ) + 1) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1)); parley_side)
      all_goals parley_side
    | succ m hIH =>
      -- 1.2. calculation
      have r31_1 : (m : ℤ) ≥ 0 := by parley_side
      have s1_2 : S ((m : ℤ) + 1) = S (m : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) := by
        calc S ((m : ℤ) + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) ((m : ℤ) + 1), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) + (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_side)
          _ = S (m : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. algebra
      have s1_3 : (n : ℤ) + ((m : ℤ) + 1) = (n : ℤ) + (m : ℤ) + 1 := by parley_ring
      -- 1.4. thm:pascal n := n + m + 1, k := m + 1
      have s1_4 : (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1 - 1) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (k := (m : ℤ) + 1)); parley_side)
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by
        have c1 : (m : ℤ) + 1 - 1 = (m : ℤ) := by parley_ring
        have row1 : (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by parley_subst_at c1 s1_4
        exact row1
      -- 1.6. algebra
      have s1_6 : (n : ℤ) + (m : ℤ) + 1 + 1 = (n : ℤ) + ((m : ℤ) + 1) + 1 := by parley_ring
      -- 1.7. substitute n + (m + 1) = n + m + 1 (line 1.3)
      have s1_7 : (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) := by parley_subst s1_3
      -- 1.8. calculation
      have s1_8 : S ((m : ℤ) + 1) = (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1) + 1) ((m : ℤ) + 1) : ℤ) := by
        calc S ((m : ℤ) + 1) = S (m : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1)) ((m : ℤ) + 1) : ℤ) := by parley_subst hIH
          _ = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) := by parley_subst s1_7
          _ = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) ((m : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1) (m : ℤ) : ℤ) := by parley_ring
          _ = (LeanBridges.Counting.choose ((n : ℤ) + (m : ℤ) + 1 + 1) ((m : ℤ) + 1) : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose ((n : ℤ) + ((m : ℤ) + 1) + 1) ((m : ℤ) + 1) : ℤ) := by parley_subst s1_6
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) = (LeanBridges.Counting.choose ((n : ℤ) + (k : ℤ) + 1) (k : ℤ) : ℤ) := by
    calc (∑ j ∈ Finset.Icc (0 : ℤ) (k : ℤ), ((LeanBridges.Counting.choose ((n : ℤ) + j) j : ℤ) : ℤ)) = S (k : ℤ) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (LeanBridges.Counting.choose ((n : ℤ) + (k : ℤ) + 1) (k : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 k) | (have h := (s1 k); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 k); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 k) | exact_mod_cast ((s1 k)).symm | (have h := (s1 k); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 k); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 k); parley_int_power h) | (have h := (s1 k); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal
