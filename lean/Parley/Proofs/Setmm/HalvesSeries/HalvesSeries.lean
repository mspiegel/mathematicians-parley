module

public import AlgebraTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Calculus
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove

/-! Written from proofs/setmm/halves-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.HalvesSeries.HalvesSeries

theorem halves_series :
    Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) = 1 := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. induction on m starting at 1
  have s2 : ∀ m : ℕ, 0 < m → (∑ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 / 2 ^ k : ℝ)) = 1 - 1 / 2 ^ m := by
    intro m h_m
    replace h_m : 1 ≤ m := h_m
    induction m, h_m using Nat.le_induction with
    | base =>
      -- 2.1. calculation
      have s2_1 : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ k : ℝ)) = 1 - 1 / 2 ^ 1 := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (1 / 2 ^ k : ℝ)) = 1 / 2 ^ 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ))); parley_side)
          _ = 1 - 1 / 2 ^ 1 := by norm_num
      all_goals parley_side
    | succ m hK2 hIH =>
      -- 2.2. mun:sum-extended a := 1, n := m, from 1
      have r73_1 : (m : ℝ) ≥ 1 := by parley_order
      have s2_2 : (∑ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 / 2 ^ k : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m : ℤ), (1 / 2 ^ k : ℝ)) + 1 / 2 ^ (m + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (a := (1 : ℤ)) (n := (m : ℤ)) (by parley_side)); parley_side)
      -- 2.3. substitute Σ(k = 1 to m) 1/2^k = 1 − 1/2^m (IH) into line 2.2
      have s2_3 : (∑ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 / 2 ^ k : ℝ)) = 1 - 1 / 2 ^ m + 1 / 2 ^ (m + 1) := by parley_subst_at hIH s2_2
      -- 2.4. mun:exponent-step a := 2
      have s2_4 : (2 ^ (m + 1) : ℝ) = 2 ^ m * 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℝ)) (m := m)); parley_side)
      -- 2.5. substitute 2^(m + 1) = 2^m·2 (line 2.4)
      have s2_5 : (1 / 2 ^ (m + 1) : ℝ) = 1 / (2 ^ m * 2) := by parley_subst s2_4
      -- 2.6. calculation
      have s2_6 : (∑ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 / 2 ^ k : ℝ)) = 1 - 1 / 2 ^ (m + 1) := by
        calc (∑ k ∈ Finset.Icc (1 : ℤ) ((m : ℤ) + 1), (1 / 2 ^ k : ℝ)) = 1 - 1 / 2 ^ m + 1 / 2 ^ (m + 1) := by parley_side
          _ = 1 - 1 / 2 ^ m + 1 / (2 ^ m * 2) := by parley_subst s2_5
          _ = 1 - 1 / (2 ^ m * 2) := by parley_ring
          _ = 1 - 1 / 2 ^ (m + 1) := by parley_subst s2_5
      all_goals parley_side
  -- 3. proof
  have s3 : ∀ ε : ℝ, ε > 0 → (∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) - 1) < ε)) := by
    intro ε
    intro hA1
    -- 3.1. obtain N: thm:archimedean x := ε, from A1
    obtain ⟨N, s3_1a, s3_1b⟩ := (Parley.Items.Stdlib.Numbers.thm_archimedean (x := ε) (by parley_side))
    -- 3.2. proof
    have s3_2 : ∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) - 1) < ε := by
      intro n hK4
      intro hA2
      -- 3.2.1. mun:power-nat a := 2, m := n
      have s3_2_1 : (0 : ℤ) < 2 ^ n := by first | exact (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | exact ((Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_nat (a := 2) (by parley_side) (m := n)); parley_side)
      -- 3.2.2. thm:power-of-two-above
      have s3_2_2 : (n : ℝ) ≤ 2 ^ n := by first | linarith [(Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove.power_of_two_above (n := n) (by parley_side))] | (have h := (Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove.power_of_two_above (n := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove.power_of_two_above (n := n) (by parley_side)) | (have h := (Parley.Proofs.Setmm.HalvesSeries.PowerOfTwoAbove.power_of_two_above (n := n) (by parley_side)); parley_side)
      -- 3.2.3. transitivity, from A2, 3.2.2
      have s3_2_3 : (N : ℝ) ≤ 2 ^ n := by parley_order
      -- 3.2.4. mun:reciprocal-order x := N, y := 2^n, from 3.2.3
      have r115_1 : (N : ℝ) > 0 := by parley_order
      have r115_2 : (2 ^ n : ℝ) > 0 := by parley_order
      have s3_2_4 : 1 / 2 ^ n ≤ 1 / (N : ℝ) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (2 ^ n : ℝ)) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (2 ^ n : ℝ)) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (2 ^ n : ℝ)) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_reciprocal_order (x := (N : ℝ)) (by parley_side) (y := (2 ^ n : ℝ)) (by parley_side))).mp (by parley_side); parley_side)
      -- 3.2.5. transitivity, from 3.2.4, 3.1
      have s3_2_5 : 1 / 2 ^ n < ε := by parley_order
      -- 3.2.6. mun:reciprocal-positive x := 2^n
      have r123_1 : (2 ^ n : ℝ) > 0 := by parley_order
      have s3_2_6 : (1 / 2 ^ n : ℝ) > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_reciprocal_positive (x := (2 ^ n : ℝ)) (by parley_side)); parley_side)
      -- 3.2.7. inequalities
      have s3_2_7 : 1 - ε < 1 - 1 / 2 ^ n := by parley_order
      -- 3.2.8. inequalities
      have s3_2_8 : (-(1 / 2 ^ n) : ℝ) < 0 := by parley_order
      -- 3.2.9. transitivity, from 3.2.8, A1
      have s3_2_9 : -(1 / 2 ^ n) < ε := by parley_order
      -- 3.2.10. inequalities
      have s3_2_10 : 1 - 1 / 2 ^ n < 1 + ε := by parley_order
      -- 3.2.11. join 3.2.7, 3.2.10
      have s3_2_11 : 1 - ε < 1 - 1 / 2 ^ n ∧ 1 - 1 / 2 ^ n < 1 + ε := by parley_side
      -- 3.2.12. mun:abs-difference-lt x := 1 − 1/2^n, c := 1, δ := ε, from 3.2.11
      have s3_2_12 : abs (1 - 1 / 2 ^ n - 1) < ε := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := (1 - 1 / 2 ^ n : ℝ)) (c := (1 : ℝ)) (δ := ε))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_abs_difference_lt (x := (1 - 1 / 2 ^ n : ℝ)) (c := (1 : ℝ)) (δ := ε))).mpr (by parley_side); parley_side)
      -- 3.2.13. substitute
      have s3_2_13 : abs ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) - 1) < ε := by
        have c1 : 1 - 1 / 2 ^ n = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) := by first | linear_combination (norm := parley_norm) (s2 n (by parley_side)) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (s2 n (by parley_side)) | exact_mod_cast ((s2 n (by parley_side))).symm | (have h := (s2 n (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (s2 n (by parley_side)); parley_int_power h) | (have h := (s2 n (by parley_side)); parley_side)
        have row1 : abs ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) - 1) < ε := by parley_subst_at c1 s3_2_12
        exact row1
      all_goals parley_side
    -- 3.3. exhibit, from 3.2
    have s3_3 : ∃ N : ℕ, 0 < N ∧ (∀ n : ℕ, 0 < n → (n : ℝ) ≥ (N : ℝ) → abs ((∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) - 1) < ε) := ⟨N, by parley_side, by parley_side⟩
    all_goals parley_side
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. def:tends-to L := 1, from 3, 4
  have s5 : Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ) : ℝ)) Filter.atTop (nhds 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Calculus.def_tends_to (x := (fun n : ℤ => ∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)))).mpr (by parley_side); parley_side)
  -- 6. def:series-sum, from 1, 5
  have s6 : Filter.limUnder Filter.atTop (fun n : ℕ => ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (1 / 2 ^ k : ℝ)) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Calculus.def_series_sum (t := (fun k : ℤ => (1 / 2 ^ k : ℝ))) (L := (1 : ℝ)) (by parley_side)); parley_side)
  all_goals exact s6

end Parley.Proofs.Setmm.HalvesSeries.HalvesSeries
