module

public import ComplexTactics
public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
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
  have hD1_kind : True := by trivial
  set M : ℝ := (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) with hD2
  have hD2_kind : True := by parley_side
  -- 1. thm:am-gm-power, from D1, D2, H3
  have s1 : P ≤ M ^ n.toNat := by
    try simp only [hD1, hD2] at *
    try push_cast at *
    exact (Parley.Proofs.Wiedijk.AmGm.AmGmPower.am_gm_power (n := n) (by parley_side) (a := a) (by parley_side))
  -- 2. mun:product-range-nonneg a := 1, b := n, from D1, H3
  have s2 : P ≥ 0 := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Sums.mun_product_range_nonneg (t := a) (a := (1 : ℤ)) (b := n) hH3)
  -- 3. mun:sum-nonneg a := 1, b := n, from H3
  have s3 : (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ≥ 0 := by exact (Parley.Items.Stdlib.Sums.mun_sum_nonneg (t := a) (a := (1 : ℤ)) (b := n) hH3)
  -- 4. mun:quotient-nonneg, from D2, H1, 3
  have s4 : M ≥ 0 := by
    try simp only [hD2] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := ∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) (y := (n : ℝ)) (by parley_side) (by parley_side))
  set r : ℝ := P ^ (1 / (n : ℝ)) with hD3
  have hD3_kind : True := by trivial
  -- 5. mun:root-power x := P, from D3
  have s5 : r ^ n.toNat = P := by
    try simp only [hD3] at *
    try push_cast at *
    (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := (P : ℂ)) (n := n) (by parley_side)); parley_of_complex h)
  -- 6. contradiction
  have s6 : r ≤ M := by
    by_contra hS
    -- 6.1. inequalities, from S
    have s6_1 : M < r := by parley_order
    -- 6.2. mun:power-less, from 4, 6.1
    have s6_2 : M ^ n.toNat < r ^ n.toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_less (x := M) (y := r) (n := n) (by parley_side) (by parley_side) (by parley_side))
    -- 6.3. substitute r^n = P (line 5) into line 6.2
    have s6_3 : M ^ n.toNat < P := by (have h := Eq.subst (motive := (fun t : ℝ => M ^ n.toNat < t)) s5 s6_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 6.4. inequalities, from 6.3
    have s6_4 : ¬ P ≤ M ^ n.toNat := by parley_side
    exact s6_4 s1
  -- 7. calculation
  calc (∏ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) ^ (1 / (n : ℝ)) = P ^ (1 / (n : ℝ)) := by simp (disch := omega) only [hD1]
    _ = r := by simp (disch := omega) only [hD3]
    _ ≤ M := by exact s6
    _ = (∑ k ∈ Finset.Icc (1 : ℤ) n, (a k : ℝ)) / (n : ℝ) := by simp (disch := omega) only [hD2]

end Parley.Proofs.Wiedijk.AmGm.AmGm
