module

public import AlgebraTactics
public import Functions
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/wiedijk/geometric-series.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum

theorem geometric_sum (a : ℝ) (hH2 : a ≠ 1) (n : ℤ) (hH3 : 0 ≤ n) :
    (∑ j ∈ Finset.Icc (0 : ℤ) n, (a ^ j.toNat : ℝ)) = (1 - a ^ (n + 1).toNat) / (1 - a) := by
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) = (1 - a ^ (k + 1).toNat) / (1 - a) := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = 1 := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) := rfl
          _ = a ^ 0 := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => a ^ j.toNat)) (a := (0 : ℤ)))
          _ = 1 := by parley_ring
      -- 1.2. calculation
      have r26_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      have s1_2 : (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = (1 - a) / (1 - a) := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (a ^ j.toNat : ℝ)) = 1 := s1_1
          _ = (1 - a) / (1 - a) := by parley_ring
      simpa only [zero_add, pow_one, Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd, Int.cast_zero] using s1_2
    | succ k hK hIH =>
      -- 1.3. calculation
      have s1_3 : (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by
        calc (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) := rfl
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := by exact (Parley.Items.Stdlib.Sums.mun_sum_last (t := (fun j : ℤ => a ^ j.toNat)) (n := k) hK)
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := rfl
      -- 1.4. mun:exponent-step m := k + 1
      have s1_4 : a ^ (k + 1 + 1).toNat = a ^ (k + 1).toNat * a := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := a) (m := k + 1) (add_nonneg (hK) (by norm_num)))
      -- 1.5. calculation
      have r45_1 : 1 - a ≠ 0 := by intro h; exact hH2 (by linear_combination (norm := parley_norm) (-1) * h)
      calc (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (a ^ j.toNat : ℝ)) = (∑ j ∈ Finset.Icc (0 : ℤ) k, (a ^ j.toNat : ℝ)) + a ^ (k + 1).toNat := s1_3
        _ = (1 - a ^ (k + 1).toNat) / (1 - a) + a ^ (k + 1).toNat := by (have h := congrArg (fun t : ℝ => t + a ^ (k + 1).toNat) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (1 - a ^ (k + 1).toNat * a) / (1 - a) := by parley_ring
        _ = (1 - a ^ (k + 1 + 1).toNat) / (1 - a) := by (have h := congrArg (fun t : ℝ => (1 - t) / (1 - a)) s1_4.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. instantiate k := n in line 1
  exact (s1 n hH3)

end Parley.Proofs.Wiedijk.GeometricSeries.GeometricSum
