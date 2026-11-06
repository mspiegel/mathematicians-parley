module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Functions
public import OrderTactics
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

/-! Written from proofs/hammack/sum-of-binomials-down-a-column.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn

theorem sum_of_binomials_down_a_column (n : ℤ) (hH1 : 0 < n) (r : ℤ) (hH2 : 0 < r) (hH3 : r ≤ n) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose j r : ℤ) : ℤ))) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose k r : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + 1) (r + 1) : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℤ, 0 ≤ m → S m = (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) := by
    intro m h_m
    replace h_m : 0 ≤ m := by omega
    induction m, h_m using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. inequalities, from H2
      have s1_1 : 0 < r := by parley_order
      -- 1.2. inequalities, from H2
      have s1_2 : 1 < r + 1 := by parley_order
      -- 1.3. calculation
      have s1_3 : S 0 = (LeanBridges.Counting.choose (1 : ℤ) (r + 1) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (LeanBridges.Counting.choose (0 : ℤ) r : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (0 : ℤ)) (by parley_side) (k := r)) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.choose (1 : ℤ) (r + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := (1 : ℤ)) (by parley_side) (k := r + 1)) (by parley_side); parley_side)
      all_goals parley_side
    | succ m hK hIH =>
      -- 1.4. calculation
      have r38_1 : m ≥ 0 := by parley_side
      have s1_4 : S (m + 1) = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by
        calc S (m + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose j r : ℤ) : ℤ)) + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j r : ℤ))) (a := (0 : ℤ)) (n := m) (by parley_side)); parley_side)
          _ = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.5. thm:pascal n := m + 1, k := r + 1
      have s1_5 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) (r + 1 - 1) : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (by parley_side) (k := r + 1)); parley_side)
      -- 1.6. substitute
      have s1_6 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by
        have c1 : r + 1 - 1 = r := by parley_ring
        have row1 : (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by parley_subst_at c1 s1_5
        exact row1
      -- 1.7. calculation
      have s1_7 : S (m + 1) = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by
        calc S (m + 1) = S m + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose (m + 1) (r + 1) : ℤ) + (LeanBridges.Counting.choose (m + 1) r : ℤ) := by parley_subst hIH
          _ = (LeanBridges.Counting.choose (m + 1 + 1) (r + 1) : ℤ) := by parley_side
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose k r : ℤ) : ℤ)) = (LeanBridges.Counting.choose (n + 1) (r + 1) : ℤ) := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose k r : ℤ) : ℤ)) = S n := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (LeanBridges.Counting.choose (n + 1) (r + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n (by parley_side)) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n (by parley_side)) | exact_mod_cast ((s1 n (by parley_side))).symm | (have h := (s1 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n (by parley_side)); parley_int_power h) | (have h := (s1 n (by parley_side)); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn
