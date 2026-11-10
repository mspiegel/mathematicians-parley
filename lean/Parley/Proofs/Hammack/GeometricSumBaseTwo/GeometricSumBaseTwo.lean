module

public import AlgebraTactics
public import Functions
public import InstanceTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
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

/-! Written from proofs/hammack/geometric-sum-base-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo

theorem geometric_sum_base_two (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat : ℤ)) = 2 ^ (n + 1).toNat - 1 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (0 : ℤ) m, (2 ^ j.toNat : ℤ) with hD1
  -- 1. induction on k starting at 0
  have s1 : ∀ k : ℤ, 0 ≤ k → S k = 2 ^ (k + 1).toNat - 1 := by
    intro k h_k
    replace h_k : 0 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      have s1_1 : S 0 = 2 ^ 1 - 1 := by
        calc S 0 = (∑ j ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
          _ = 2 ^ 0 := by
              have hI : (∑ k ∈ Finset.Icc (0 : ℤ) (0 : ℤ), (2 ^ k.toNat : ℤ)) = 2 ^ 0 := by parley_instance_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ))))
              exact hI
          _ = 2 ^ 1 - 1 := by norm_num
      simpa only [zero_add, Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd] using s1_1
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : k ≥ 0 := by parley_side
      have s1_2 : S (k + 1) = S k + 2 ^ (k + 1).toNat := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (0 : ℤ) (k + 1), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (0 : ℤ) k, (2 ^ j.toNat : ℤ)) + 2 ^ (k + 1).toNat := by
              have hI : (∑ b ∈ Finset.Icc (0 : ℤ) (k + 1), (2 ^ b.toNat : ℤ)) = (∑ b ∈ Finset.Icc (0 : ℤ) k, (2 ^ b.toNat : ℤ)) + 2 ^ (k + 1).toNat := by parley_instance_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (0 : ℤ)) (n := k) r28_1))
              exact hI
          _ = S k + 2 ^ (k + 1).toNat := by simp (disch := omega) only [hD1]
      -- 1.3. mun:exponent-step a := 2, m := k + 1
      have s1_3 : (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (by parley_side))
      -- 1.4. calculation
      calc S (k + 1) = S k + 2 ^ (k + 1).toNat := by exact s1_2
        _ = 2 ^ (k + 1).toNat - 1 + 2 ^ (k + 1).toNat := by (have h := congrArg (fun t : ℤ => t + 2 ^ (k + 1).toNat) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 2 ^ (k + 1).toNat * 2 - 1 := by parley_ring
        _ = 2 ^ (k + 1 + 1).toNat - 1 := by (have h := congrArg (fun t : ℤ => t - 1) (s1_3).symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat : ℤ)) = S n := by simp (disch := omega) only [hD1]
    _ = 2 ^ (n + 1).toNat - 1 := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.GeometricSumBaseTwo.GeometricSumBaseTwo
