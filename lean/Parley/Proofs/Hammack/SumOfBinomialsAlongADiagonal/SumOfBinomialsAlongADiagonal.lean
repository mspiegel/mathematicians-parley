module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-binomials-along-a-diagonal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal

theorem sum_of_binomials_along_a_diagonal (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : 0 ≤ k) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ))) :
    (∑ j ∈ Finset.Icc (0 : ℤ) k, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + k + 1) k : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → S m = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 0 = (LeanBridges.Counting.choose (n + 1) (0 : ℤ) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (LeanBridges.Counting.choose n (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n) (by parley_side)); parley_side)
          _ = (LeanBridges.Counting.choose (n + 1) (0 : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.mun_binomial_zero_index (n := n + 1) (by parley_side)); parley_side)
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.2. calculation
      have r31_1 : m ≥ 0 := by parley_side
      have s1_2 : S (m + 1) = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by
        calc S (m + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose (n + j) j : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); parley_side)
          _ = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.3. algebra
      have s1_3 : n + (m + 1) = n + m + 1 := by parley_ring
      -- 1.4. thm:pascal n := n + m + 1, k := m + 1
      have s1_4 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) (m + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := n + m + 1) (by parley_side) (k := m + 1)); parley_side)
      -- 1.5. substitute
      have s1_5 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by
        have c1 : m + 1 - 1 = m := by parley_ring
        have row1 : (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by parley_subst_at c1 s1_4
        exact row1
      -- 1.6. algebra
      have s1_6 : n + m + 1 + 1 = n + (m + 1) + 1 := by parley_ring
      -- 1.7. substitute n + (m + 1) = n + m + 1 (line 1.3)
      have s1_7 : (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) = (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) := by parley_subst s1_3
      -- 1.8. calculation
      have s1_8 : S (m + 1) = (LeanBridges.Counting.choose (n + (m + 1) + 1) (m + 1) : ℤ) := by
        calc S (m + 1) = S m + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) + (LeanBridges.Counting.choose (n + (m + 1)) (m + 1) : ℤ) := by parley_subst hIH
          _ = (LeanBridges.Counting.choose (n + m + 1) m : ℤ) + (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) := by parley_subst s1_7
          _ = (LeanBridges.Counting.choose (n + m + 1) (m + 1) : ℤ) + (LeanBridges.Counting.choose (n + m + 1) m : ℤ) := by parley_ring
          _ = (LeanBridges.Counting.choose (n + m + 1 + 1) (m + 1) : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose (n + (m + 1) + 1) (m + 1) : ℤ) := by parley_subst s1_6
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ j ∈ Finset.Icc (0 : ℤ) k, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + k + 1) k : ℤ) := by
    calc (∑ j ∈ Finset.Icc (0 : ℤ) k, ((LeanBridges.Counting.choose (n + j) j : ℤ) : ℤ)) = S k := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (LeanBridges.Counting.choose (n + k + 1) k : ℤ) := by first | linear_combination (norm := parley_norm) (s1 k (by parley_side)) | (have h := (s1 k (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 k (by parley_side)) | exact_mod_cast ((s1 k (by parley_side))).symm | (have h := (s1 k (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 k (by parley_side)); parley_int_power h) | (have h := (s1 k (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfBinomialsAlongADiagonal.SumOfBinomialsAlongADiagonal
