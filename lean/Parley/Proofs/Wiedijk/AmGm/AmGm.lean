module

public import ArithTactics
public import ComplexTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.AmGm.AmGmPower

/-! Written from proofs/wiedijk/am-gm.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.AmGm.AmGm

set_option maxHeartbeats 400000 in
theorem am_gm (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (hH3 : ∀ k : ℤ, k ∈ Finset.Icc 1 n → a k ≥ 0) :
    (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ^ (1 / (n : ℝ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) := by
  set P : ℝ := ∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ) with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Sums.mun_product_real (t := a) (a := (1 : ℤ)) (b := n)) | exact ((Parley.Items.Stdlib.Sums.mun_product_real (t := a) (a := (1 : ℤ)) (b := n))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_product_real (t := a) (a := (1 : ℤ)) (b := n)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_real (t := a) (a := (1 : ℤ)) (b := n)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_real (t := a) (a := (1 : ℤ)) (b := n)); parley_side)
  set M : ℝ := (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) with hD2
  have hD2_kind : True := by parley_side
  -- 1. thm:am-gm-power, from D1, D2, H3
  have s1 : P ≤ M ^ n.toNat := by
    try simp only [hD1, hD2] at *
    try push_cast at *
    first | (have h := (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) hH3); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) hH3)] | (have h := (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) hH3) | (have h := (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) hH3); parley_side)
  -- 2. mun:product-range-nonneg a := 1, b := n, from D1, H3
  have s2 : P ≥ 0 := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_side)
  -- 3. mun:sum-nonneg a := 1, b := n, from H3
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side))] | (have h := (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := n) (by parley_side)); parley_side)
  -- 4. mun:quotient-nonneg, from D2, H1, 3
  have s4 : M ≥ 0 := by
    try simp only [hD2] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side)); parley_side)
  set r : ℝ := P ^ (1 / (n : ℝ)) with hD3
  have hD3_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ))) | exact ((Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ)))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ))) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ))) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_real (x := P) (by parley_side) (y := 1 / (n : ℝ))); parley_side)
  -- 5. mun:root-power x := P, from D3
  have s5 : r ^ n.toNat = P := by
    try simp only [hD3] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_side)
  -- 6. contradiction
  have s6 : r ≤ M := by
    by_contra hc_hS
    have hS : ¬ r ≤ M := by parley_suppose hc_hS
    -- 6.1. inequalities, from S
    have s6_1 : M < r := by parley_order
    -- 6.2. mun:power-less, from 4, 6.1
    have s6_2 : M ^ n.toNat < r ^ n.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 6.3. substitute r^n = P (line 5) into line 6.2
    have s6_3 : M ^ n.toNat < P := by parley_subst_at s5 s6_2
    -- 6.4. inequalities, from 6.3
    have s6_4 : ¬ P ≤ M ^ n.toNat := by parley_side
    all_goals parley_side
  -- 7. calculation
  have s7 : (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ^ (1 / (n : ℝ)) ≤ (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) := by
    calc (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ^ (1 / (n : ℝ)) = P ^ (1 / (n : ℝ)) := by first | (simp (disch := omega) only [hD1]; done) | (simp (disch := omega) only [hD1]; push_cast; norm_num; done) | parley_side
      _ = r := by first | (simp (disch := omega) only [hD3]; done) | (simp (disch := omega) only [hD3]; push_cast; norm_num; done) | parley_side
      _ ≤ M := by parley_side
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) := by first | (simp (disch := omega) only [hD2]; done) | (simp (disch := omega) only [hD2]; push_cast; norm_num; done) | parley_side
  all_goals exact s7

end Parley.Proofs.Wiedijk.AmGm.AmGm
