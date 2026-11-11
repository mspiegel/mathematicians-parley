module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import OrderTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
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
public import Mathlib.Tactic.Positivity.Finset
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
  set t : ℤ → ℝ := fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat with hD1
  set p : ℤ → ℝ := fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat with hD2
  set q : ℤ → ℝ := fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat with hD3
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
      calc x ^ (m - k) * x = x ^ (m - k + 1) := by (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := x) (m := m - k) (by parley_side)); simp only [parley_zpow_toNat (n := m - k) (h := r87_1), parley_zpow_toNat (n := m - k + 1) (h := add_nonneg (r87_1) (by norm_num))] at h ⊢; exact_mod_cast h.symm)
        _ = x ^ (m + 1 - k) := by (have h := congrArg (fun u : ℤ => x ^ u) s8_2; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 8.4. calculation
    have r93_1 : 0 ≤ m - k := by exact (Parley.Items.Stdlib.Sums.mun_range_difference (a := (0 : ℤ)) (n := m) (k := k) hJ)
    calc x * t k = x * ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat) := by (have h := congrArg (fun u : ℝ => x * u) s8_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose m k : ℝ) * (x ^ (m - k) * x) * y ^ k.toNat := by parley_ring
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by (have h := congrArg (fun u : ℝ => (LeanBridges.Counting.choose m k : ℝ) * u * y ^ k.toNat) s8_3; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 9. inequalities
  have s9 : m < m + 1 := by parley_order
  -- 10. def:C n := m, k := m + 1, from 9
  have s10 : (LeanBridges.Counting.choose m (m + 1) : ℤ) = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_3 (n := m) (by parley_side) (k := m + 1)) s9
  -- 11. algebra
  have s11 : m + 1 - (m + 1) = 0 := by parley_ring
  -- 12. calculation
  have s12 : (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat = 0 := by
    calc (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat = (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ 0 * y ^ (m + 1).toNat := by (have h := congrArg (fun u : ℤ => (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ u * y ^ (m + 1).toNat) s11; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 0 * x ^ 0 * y ^ (m + 1).toNat := by
          have e_w : (LeanBridges.Counting.choose m (m + 1) : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s10; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun u : ℝ => u * x ^ 0 * y ^ (m + 1).toNat) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 0 := by parley_ring
  -- 13. mun:sum-last n := m
  have s13 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) + (LeanBridges.Counting.choose m (m + 1) : ℝ) * x ^ (m + 1 - (m + 1)) * y ^ (m + 1).toNat := by exact (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m) (by parley_side))
  -- 14. substitute C(m, m + 1)·x^((m + 1) − (m + 1))·y^(m + 1) = 0 (line 12) into line 13
  have s14 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) + 0 := by (have h := Eq.subst (motive := (fun u : ℝ => (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) + u)) s12 s13; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 15. calculation
  have s15 : x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by
    calc x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, (x * t k : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_scaled (t := t) (a := (0 : ℤ)) (b := m) (c := x))
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => x * t k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m) s8)
  -- 16. substitute x·(Σ(k = 0 to m) t(k)) = Σ(k = 0 to m) C(m, k)·x^((m + 1) − k)·y^k (line 15) into line 14
  have s16 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by (have h := Eq.subst (motive := (fun u : ℝ => (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = u + 0)) (s15).symm s14; push_cast [add_zero] at h ⊢; all_goals exact_mod_cast h)
  -- 17. proof
  have s17 : ∀ k : ℤ, k ∈ Finset.Icc 0 (m + 1) → p k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 17.1. D2, from J
    simp (disch := omega) only [hD2]
  -- 18. calculation
  have s18 : x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) := by
    calc x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by parley_side
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) := by
          have hI : (∑ c ∈ Finset.Icc (0 : ℤ) (m + 1), (p c : ℝ)) = (∑ c ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m c : ℝ) * x ^ (m + 1 - c) * y ^ c.toNat : ℝ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := p) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s17))
          exact hI
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
    calc y * t k = y * ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat) := by (have h := congrArg (fun u : ℝ => y * u) s19_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * (y ^ k.toNat * y) := by parley_ring
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat := by (have h := congrArg (fun u : ℝ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * u) (s19_2).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
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
    calc (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1) = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ (k - 1 + 1) := by (have h := congrArg (fun u : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ u * y ^ (k - 1 + 1)) s20_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by (have h := congrArg (fun u : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ u) s20_2; simp only [parley_zpow_toNat (n := k) (h := le_trans (by norm_num) (Finset.mem_Icc.mp hJ).1)] at h ⊢; exact_mod_cast h)
  -- 21. calculation
  have s21 : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℤ) = 0 := by
    calc (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℤ) = (LeanBridges.Counting.choose m (-1 : ℤ) : ℤ) := by norm_num
      _ = 0 := by exact (Parley.Items.Stdlib.Counting.def_C_1 (n := m) (by parley_side))
  -- 22. calculation
  have s22 : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 = 0 := by
    calc (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 = 0 * x ^ (m + 1).toNat * y ^ 0 := by
          have e_w : (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s21; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun u : ℝ => u * x ^ (m + 1).toNat * y ^ 0) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = 0 := by parley_ring
  -- 23. mun:sum-first n := m + 1
  have s23 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (LeanBridges.Counting.choose m (0 - 1 : ℤ) : ℝ) * x ^ (m + 1).toNat * y ^ 0 + (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by (have h := (Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (n := m + 1) (by parley_side)); simp only [parley_zpow_toNat (n := m + 1) (h := add_nonneg (hH3) (by norm_num)), sub_zero, zero_add, Int.reduceToNat] at h ⊢; exact_mod_cast h)
  -- 24. substitute C(m, 0 − 1)·x^(m + 1)·y^0 = 0 (line 22) into line 23
  have s24 : (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by (have h := Eq.subst (motive := (fun u : ℝ => (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) = u + (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)))) s22 s23; push_cast [zero_add] at h ⊢; all_goals exact_mod_cast h)
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
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => y * t k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) s19)
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1) : ℝ)) := by (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ (k + 1).toNat)) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); have hb1 : ∀ k ∈ Finset.Icc (1 : ℤ) (m + 1), y ^ (k - 1 + 1) = y ^ ((k - 1 + 1)).toNat := fun k hk => parley_zpow_toNat (y) ((k - 1 + 1)) (by linarith [(Finset.mem_Icc.mp hk).1]); simp +contextual only [hb1, zero_add] at h ⊢; exact_mod_cast h)
      _ = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m - (k - 1)) * y ^ (k - 1 + 1))) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (1 : ℤ)) (b := m + 1) s20)
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by parley_side
      _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (q k : ℝ)) := by
          have hI : (∑ c ∈ Finset.Icc (0 : ℤ) (m + 1), (q c : ℝ)) = (∑ c ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (c - 1) : ℝ) * x ^ (m + 1 - c) * y ^ c.toNat : ℝ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_termwise (t := q) (u := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s25))
          exact hI
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
    calc p k + q k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat + q k := by (have h := congrArg (fun u : ℝ => u + q k) s27_1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat + (LeanBridges.Counting.choose m (k - 1) : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by (have h := congrArg (fun u : ℝ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat + u) s27_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = ((LeanBridges.Counting.choose m k : ℝ) + (LeanBridges.Counting.choose m (k - 1) : ℝ)) * x ^ (m + 1 - k) * y ^ k.toNat := by parley_ring
      _ = (LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat := by
          have e_w : (LeanBridges.Counting.choose m k : ℝ) + (LeanBridges.Counting.choose m (k - 1) : ℝ) = (LeanBridges.Counting.choose (m + 1) k : ℝ) := by have h := congrArg (fun x : ℤ => (x : ℝ)) s27_3; push_cast at h; linear_combination (norm := parley_norm) h
          (have h := congrArg (fun u : ℝ => u * x ^ (m + 1 - k) * y ^ k.toNat) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 28. proof
  have s28 : ∀ k : ℤ, k ∈ Finset.Icc 0 m → t k = (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 28.1. D1, from J
    simp (disch := omega) only [hD1]
  -- 29. mun:sum-termwise a := 0, b := m, from 28
  have s29 : (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := t) (u := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m) s28)
  -- 30. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℝ) * x ^ (m - k) * y ^ k.toNat : ℝ)) * (x + y) = (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) * (x + y) := by (have h := congrArg (fun u : ℝ => u * (x + y)) (s29).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = x * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) + y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by parley_ring
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) + y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ)) := by (have h := congrArg (fun u : ℝ => u + y * (∑ k ∈ Finset.Icc (0 : ℤ) m, (t k : ℝ))) s18; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) + (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (q k : ℝ)) := by (have h := congrArg (fun u : ℝ => (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k : ℝ)) + u) s26; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), (p k + q k : ℝ)) := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_add (t := p) (u := q) (a := (0 : ℤ)) (b := m + 1)).symm
    _ = (∑ k ∈ Finset.Icc (0 : ℤ) (m + 1), ((LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat : ℝ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => p k + q k)) (u := (fun k : ℤ => (LeanBridges.Counting.choose (m + 1) k : ℝ) * x ^ (m + 1 - k) * y ^ k.toNat)) (a := (0 : ℤ)) (b := m + 1) s27)

end Parley.Proofs.Wiedijk.Binomial.BinomialStep
