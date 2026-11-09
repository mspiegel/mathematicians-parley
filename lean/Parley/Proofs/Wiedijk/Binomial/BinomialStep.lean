module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Counting
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/binomial.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Binomial.BinomialStep

set_option maxHeartbeats 1000000 in
theorem binomial_step (x : ℝ) (y : ℝ) (m : ℤ) (hH3 : 0 ≤ m) :
    (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) * (x + y) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by
  set t : ℤ → ℝ := fun k => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat with hD1
  set p : ℤ → ℝ := fun k => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat with hD2
  set q : ℤ → ℝ := fun k => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat with hD3
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. mun:function-into, from 1
  -- 3. proof
  -- what this block shows, Lean's types give
  -- 4. mun:function-into, from 3
  -- 5. proof
  -- what this block shows, Lean's types give
  -- 6. mun:function-into, from 5
  -- 7. mun:sum-real a := 0, b := m
  -- 8. proof
  have s8 : ∀ k : ℤ, k ∈ Finset.Icc 0 m → x * t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 8.1. D1, from J
    have s8_1 : t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat := by simp (disch := omega) only [hD1]
    -- 8.2. algebra
    have s8_2 : m - k + 1 = m + 1 - k := by parley_ring
    -- 8.3. calculation
    have r87_1 : 0 ≤ m - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m) (k := k) hJ)
    have s8_3 : x ^ (m - k) * x = x ^ (m + 1 - k) := by
      calc x ^ (m - k) * x = x ^ (m - k + 1) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); parley_side)
        _ = x ^ (m + 1 - k) := by
            have s8_2_w : (m : ℝ) - (k : ℝ) + 1 = (m : ℝ) + 1 - (k : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s8_2; push_cast at h; linear_combination (norm := parley_norm) h
            first | parley_subst s8_2_w | parley_subst s8_2
    -- 8.4. calculation
    have r93_1 : 0 ≤ m - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m) (k := k) hJ)
    calc x * t k = x * ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat) := by parley_subst s8_1
      _ = (LeanBridges.Counting.choose m k : ℝ) * (x ^ (m - k) * x) * y ^ k.toNat := by parley_ring
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by parley_subst s8_3
  -- 9. inequalities
  have s9 : m < m + 1 := by parley_order
  -- 10. def:C n := m, k := m + 1, from 9
  have s10 : (LeanBridges.Counting.choose m (m + 1) : ℤ) = 0 := (Parley.Items.Stdlib.Counting.def_C_3 (n := m) (by parley_side) (k := m + 1)) s9
  -- 11. algebra
  have s11 : m + 1 - (m + 1) = 0 := by parley_ring
  -- 12. calculation
  have s12 : (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat = 0 := by
    calc (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat = (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ 0 * y ^ (m + 1).toNat := by
          have s11_w : (m : ℝ) + 1 - ((m : ℝ) + 1) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s11; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s11_w | parley_subst s11
      _ = 0 * x ^ 0 * y ^ (m + 1).toNat := by
          have s10_w : (LeanBridges.Counting.choose m (m + 1) : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s10; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s10_w | parley_subst s10
      _ = 0 := by parley_ring
  -- 13. mun:sum-last n := m
  have s13 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) + (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat := (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m) (by parley_side))
  -- 14. substitute C(m, m + 1)·x^((m + 1) − (m + 1))·y^(m + 1) = 0 (line 12) into line 13
  have s14 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) + 0 := by parley_subst_at s12 s13
  -- 15. calculation
  have s15 : x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by
    calc x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, (x * t k : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_scaled (t := t) (a := (0 : ℤ)) (b := m) (c := x))
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => x * t k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m) s8)
  -- 16. substitute x·(Σ(k = 0 to m) t(k)) = Σ(k = 0 to m) C(m, k)·x^((m + 1) − k)·y^k (line 15) into line 14
  have s16 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by parley_subst_at s15 s14
  -- 17. proof
  have s17 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m + 1) → p k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 17.1. D2, from J
    simp (disch := omega) only [hD2]
  -- 18. calculation
  have s18 : x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) := by
    calc x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by first | parley_side | parley_line_toNat s16
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17); parley_side)
  -- 19. proof
  have s19 : ∀ k : ℤ, k ∈ Finset.Icc 0 m → y * t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 19.1. D1, from J
    have s19_1 : t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat := by simp (disch := omega) only [hD1]
    -- 19.2. mun:exponent-step a := y, m := k
    have s19_2 : y ^ (k + 1).toNat = y ^ k.toNat * y := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := y) (m := k) (by parley_side))
    -- 19.3. calculation
    have r155_1 : 0 ≤ m - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m) (k := k) hJ)
    calc y * t k = y * ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat) := by parley_subst s19_1
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * (y ^ k.toNat * y) := by parley_ring
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat := by parley_subst s19_2
  -- 20. proof
  have s20 : ∀ k : ℤ, k ∈ Finset.Icc 1 (m + 1) → (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1) = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 20.1. algebra
    have s20_1 : m - (k - 1) = m + 1 - k := by parley_ring
    -- 20.2. algebra
    have s20_2 : k - 1 + 1 = k := by parley_ring
    -- 20.3. calculation
    calc (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1) = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ (k - 1 + 1) := by
          have s20_1_w : (m : ℝ) - ((k : ℝ) - 1) = (m : ℝ) + 1 - (k : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s20_1; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s20_1_w | parley_subst s20_1
      _ = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
          have s20_2_w : (k : ℝ) - 1 + 1 = (k : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s20_2; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s20_2_w | parley_subst s20_2
  -- 21. calculation
  have s21 : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℤ) = 0 := by
    calc (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose m (-1 : ℤ) : ℤ) := by norm_num
      _ = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_1 (n := m) (by parley_side))
  -- 22. calculation
  have s22 : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 = 0 := by
    calc (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 = 0 * x ^ (m + 1).toNat * y ^ 0 := by
          have s21_w : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s21; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s21_w | parley_subst s21
      _ = 0 := by parley_ring
  -- 23. mun:sum-first n := m + 1
  have s23 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 + (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); parley_side)
  -- 24. substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23
  have s24 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by parley_subst_at s22 s23
  -- 25. proof
  have s25 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m + 1) → q k = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 25.1. D3, from J
    simp (disch := omega) only [hD3]
  -- 26. calculation
  have s26 : y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (q k : ℝ)) := by
    calc y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, (y * t k : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_scaled (t := t) (a := (0 : ℤ)) (b := m) (c := y))
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat : ℝ)) := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => y * t k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) s19)
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1) : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_side)
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (1 : ℤ)) (b := m + 1) s20)
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by first | parley_side | parley_line_toNat s24
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (q k : ℝ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25)).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); simp (disch := omega) only [← zpow_natCast, Int.toNat_of_nonneg] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); simp +contextual (disch := (simp only [Finset.mem_Icc] at *; first | omega | positivity | nlinarith)) only [parley_zpow_toNat] at h ⊢; first | exact h | exact_mod_cast h | linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25); parley_side)
  -- 27. proof
  have s27 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m + 1) → p k + q k = (LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 27.1. D2, from J
    have s27_1 : p k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by simp (disch := omega) only [hD2]
    -- 27.2. D3, from J
    have s27_2 : q k = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by simp (disch := omega) only [hD3]
    -- 27.3. thm:pascal n := m
    have s27_3 : (LeanBridges.Counting.choose m k : ℤ) + (LeanBridges.Counting.choose m (k - 1) : ℤ) = (LeanBridges.Counting.choose (m + 1) k : ℤ) := by exact (Parley.Items.Stdlib.Counting.thm_pascal (n := m) (by parley_side) (k := k))
    -- 27.4. calculation
    have r226_1 : 0 ≤ m + 1 - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m + 1) (k := k) hJ)
    calc p k + q k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat + q k := by parley_subst s27_1
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat + (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by parley_subst s27_2
      _ = ((LeanBridges.Counting.choose m k : ℝ) + (LeanBridges.Counting.choose m (k - 1) : ℝ)) * x ^ (m + 1 - k) * y ^ k.toNat := by parley_ring
      _ = (LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
          have s27_3_w : (LeanBridges.Counting.choose m k : ℝ) + (LeanBridges.Counting.choose m (k - 1) : ℝ) = (LeanBridges.Counting.choose (m + 1) k : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s27_3; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s27_3_w | parley_subst s27_3
  -- 28. proof
  have s28 : ∀ k : ℤ, k ∈ Finset.Icc 0 m → t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 28.1. D1, from J
    simp (disch := omega) only [hD1]
  -- 29. mun:sum-termwise a := 0, b := m, from 28
  have s29 : (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m) s28)
  -- 30. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) * (x + y) = (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) * (x + y) := by parley_subst s29
    _ = x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) + y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by parley_ring
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) + y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by parley_subst s18
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) + (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (q k : ℝ)) := by parley_subst s26
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k + q k : ℝ)) := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_add (t := p) (u := q) (a := (0 : ℤ)) (b := m + 1)).symm
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => p k + q k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s27)

end Parley.Proofs.Wiedijk.Binomial.BinomialStep
