module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-binomials-down-a-column.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn

theorem sum_of_binomials_down_a_column (n : ℕ) (hH1 : 0 < n) (r : ℕ) (hH2 : 0 < r) (hH3 : (r : ℤ) ≤ (n : ℤ)) (S : ℤ → ℤ) (hD1 : ∀ m : ℤ, 0 ≤ m → S m = (∑ j ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose j (r : ℤ) : ℤ) : ℤ))) :
    (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose k (r : ℤ) : ℤ) : ℤ)) = (LeanBridges.Counting.choose ((n : ℤ) + 1) ((r : ℤ) + 1) : ℤ) := by
  -- 1. induction on m starting at 0
  have s1 : ∀ m : ℕ, S (m : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1) : ℤ) := by
    intro m
    induction m with
    | zero =>
      -- 1.1. inequalities, from H2
      have s1_1 : 0 < (r : ℤ) := by parley_order
      -- 1.2. inequalities, from H2
      have s1_2 : 1 < (r : ℤ) + 1 := by parley_order
      -- 1.3. calculation
      have s1_3 : S 0 = (LeanBridges.Counting.choose (1 : ℤ) ((r : ℤ) + 1) : ℤ) := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), ((LeanBridges.Counting.choose j (r : ℤ) : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (LeanBridges.Counting.choose (0 : ℤ) (r : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ))); parley_side)
          _ = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 0) (k := (r : ℤ))) (by parley_side); parley_side)
          _ = (LeanBridges.Counting.choose (1 : ℤ) ((r : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side)).symm | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.def_C_3 (n := 1) (k := (r : ℤ) + 1)) (by parley_side); parley_side)
      all_goals parley_side
    | succ m hIH =>
      -- 1.4. calculation
      have r38_1 : (m : ℤ) ≥ 0 := by parley_side
      have s1_4 : S ((m : ℤ) + 1) = S (m : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) := by
        calc S ((m : ℤ) + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) ((m : ℤ) + 1), ((LeanBridges.Counting.choose j (r : ℤ) : ℤ) : ℤ)) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) (m : ℤ), ((LeanBridges.Counting.choose j (r : ℤ) : ℤ) : ℤ)) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (LeanBridges.Counting.choose j (r : ℤ) : ℤ))) (a := (0 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_side)
          _ = S (m : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      -- 1.5. thm:pascal n := m + 1, k := r + 1
      have s1_5 : (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1 - 1) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + 1 + 1) ((r : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)) | exact_mod_cast ((Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1))).symm | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Counting.thm_pascal (n := m + 1) (k := (r : ℤ) + 1)); parley_side)
      -- 1.6. substitute
      have s1_6 : (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + 1 + 1) ((r : ℤ) + 1) : ℤ) := by
        have c1 : (r : ℤ) + 1 - 1 = (r : ℤ) := by parley_ring
        have row1 : (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) = (LeanBridges.Counting.choose ((m : ℤ) + 1 + 1) ((r : ℤ) + 1) : ℤ) := by parley_subst_at c1 s1_5
        exact row1
      -- 1.7. calculation
      have s1_7 : S ((m : ℤ) + 1) = (LeanBridges.Counting.choose ((m : ℤ) + 1 + 1) ((r : ℤ) + 1) : ℤ) := by
        calc S ((m : ℤ) + 1) = S (m : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) := by parley_side
          _ = (LeanBridges.Counting.choose ((m : ℤ) + 1) ((r : ℤ) + 1) : ℤ) + (LeanBridges.Counting.choose ((m : ℤ) + 1) (r : ℤ) : ℤ) := by parley_subst hIH
          _ = (LeanBridges.Counting.choose ((m : ℤ) + 1 + 1) ((r : ℤ) + 1) : ℤ) := by parley_side
      all_goals parley_side
  -- 2. calculation
  have s2 : (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose k (r : ℤ) : ℤ) : ℤ)) = (LeanBridges.Counting.choose ((n : ℤ) + 1) ((r : ℤ) + 1) : ℤ) := by
    calc (∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), ((LeanBridges.Counting.choose k (r : ℤ) : ℤ) : ℤ)) = S (n : ℤ) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = (LeanBridges.Counting.choose ((n : ℤ) + 1) ((r : ℤ) + 1) : ℤ) := by first | linear_combination (norm := parley_norm) (s1 n) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s1 n); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s1 n) | exact_mod_cast ((s1 n)).symm | (have h := (s1 n); rify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); qify; linear_combination (norm := parley_norm) h) | (have h := (s1 n); parley_int_power h) | (have h := (s1 n); parley_side)
  all_goals exact s2

end Parley.Proofs.Hammack.SumOfBinomialsDownAColumn.SumOfBinomialsDownAColumn
