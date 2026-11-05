module

public import ArithTactics
public import ComplexTactics
public import OrderTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.AmGm.AmGmPower

/-! Written from proofs/wiedijk/am-gm.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.AmGm.AmGm

theorem am_gm (n : ℕ) (hH1 : 0 < n) (a : ℤ → ℝ) (hH3 : ∀ k : ℤ, k ∈ Finset.Icc 1 (n : ℤ) → a k ≥ 0) :
    (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) ^ (1 / (n : ℝ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) / (n : ℝ) := by
  set P : ℝ := ∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ) with hD1
  set M : ℝ := (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) / (n : ℝ) with hD2
  -- 1. thm:am-gm-power, from D1, D2, H3
  have s1 : P ≤ M ^ n := by
    try simp only [hD1, hD2] at *
    try push_cast at *
    first | linarith [(Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) (by parley_side))] | (have h := (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) (by parley_side)) | (have h := (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) (by parley_side)); parley_side)
  -- 2. mun:product-range-nonneg a := 1, b := n, from D1, H3
  have s2 : P ≥ 0 := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_side)
  -- 3. mun:sum-nonneg a := 1, b := n, from H3
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := (n : ℤ)) (by parley_side)); parley_side)
  -- 4. mun:quotient-nonneg, from D2, H1, 3
  have s4 : M ≥ 0 := by
    try simp only [hD2] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)); parley_side)
  set r : ℝ := P ^ (1 / (n : ℝ)) with hD3
  -- 5. mun:root-power x := P, from D3
  have s5 : r ^ n = P := by
    try simp only [hD3] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_side)
  -- 6. contradiction
  have s6 : r ≤ M := by
    by_contra hc_hS
    have hS : ¬ r ≤ M := by parley_suppose hc_hS
    -- 6.1. inequalities, from S
    have s6_1 : M < r := by parley_order
    -- 6.2. mun:power-less, from 4, 6.1
    have s6_2 : M ^ n < r ^ n := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 6.3. substitute r^n = P (line 5) into line 6.2
    have s6_3 : M ^ n < P := by parley_subst_at s5 s6_2
    -- 6.4. inequalities, from 6.3
    have s6_4 : ¬ P ≤ M ^ n := by parley_side
    all_goals parley_side
  -- 7. calculation
  have s7 : (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) ^ (1 / (n : ℝ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) / (n : ℝ) := by
    calc (∏ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) ^ (1 / (n : ℝ)) = P ^ (1 / (n : ℝ)) := by first | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = r := by first | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      _ ≤ M := by parley_side
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (n : ℤ), (a k : ℝ)) / (n : ℝ) := by first | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  all_goals exact s7

end Parley.Proofs.Wiedijk.AmGm.AmGm
