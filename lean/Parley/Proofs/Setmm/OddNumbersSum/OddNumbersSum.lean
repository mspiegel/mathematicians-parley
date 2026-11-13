module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Order.ZeroLEOne
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
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/setmm/odd-numbers-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum

theorem odd_numbers_sum (N : ℤ) (hH1 : 0 ≤ N) :
    (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) = N ^ 2 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (2 * j - 1 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → S k = k ^ 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (2 * j - 1 : ℤ)) := by simp (disch := omega) only [hD1]
        _ = 2 * 1 - 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)))
        _ = 1 ^ 2 := by norm_num
    | succ k hK hIH =>
      -- 1.2. calculation
      have r29_1 : k ≥ 1 := by exact lt_of_lt_of_le zero_lt_one hK
      have s1_2 : S (k + 1) = S k + (2 * (k + 1) - 1) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (2 * j - 1 : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (2 * j - 1 : ℤ)) + (2 * (k + 1) - 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 2 * j - 1)) (a := (1 : ℤ)) (n := k) r29_1)
          _ = S k + (2 * (k + 1) - 1) := by simp (disch := omega) only [hD1]
      -- 1.3. calculation
      calc S (k + 1) = S k + (2 * (k + 1) - 1) := s1_2
        _ = k ^ 2 + (2 * (k + 1) - 1) := by (have h := congrArg (fun t : ℤ => t + (2 * (k + 1) - 1)) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (k + 1) ^ 2 := by parley_ring
  -- 2. def:nat0 n := N
  have s2 : 0 < N ∨ N = 0 := by
    have hI : 0 < N ∨ N = 0 := by parley_instance (((Parley.Items.Stdlib.Numbers.def_nat0 (n := N))).mp ⟨N, hH1, rfl⟩)
    exact hI
  -- 3. cases, from 2
  rcases s2 with hC1 | hC2
  · skip
    -- 3.1. D1, from C1
    have s3_1 : (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) = S N := by simp (disch := omega) only [hD1]
    -- 3.2. calculation
    calc (∑ k ∈ Finset.Icc (1 : ℤ) N, (2 * k - 1 : ℤ)) = S N := s3_1
      _ = N ^ 2 := by exact (s1 N hC1)
  · skip
    -- 3.3. mun:sum-single a := 0
    have s3_3 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 2 * 0 - 1 := by exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun k : ℤ => 2 * k - 1)) (a := (0 : ℤ)))
    -- 3.4. mun:sum-first n := 0
    have s3_4 : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 2 * 0 - 1 + (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) := by
      have hI : (∑ a ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 * a - 1 : ℤ)) = 2 * 0 - 1 + (∑ a ∈ Finset.Icc (0 + 1 : ℤ) (0 : ℤ), (2 * a - 1 : ℤ)) := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_first (t := (fun k : ℤ => 2 * k - 1)) (n := (0 : ℤ)) (by norm_num)))
      simpa only [Int.cast_one, Int.cast_zero, zero_add] using hI
    -- 3.5. algebra, from 3.3, 3.4
    have s3_5 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by linear_combination (norm := parley_norm) s3_3 + (-1) * s3_4
    -- 3.6. calculation
    have s3_6 : (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 ^ 2 := by
      calc (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := s3_5
        _ = 0 ^ 2 := by norm_num
    -- 3.7. substitute N = 0 (C2) into line 3.6
    (have h := Eq.subst (motive := (fun t : ℤ => (∑ k ∈ Finset.Icc (1 : ℤ) t, (2 * k - 1 : ℤ)) = t ^ 2)) hC2.symm s3_6; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Setmm.OddNumbersSum.OddNumbersSum
