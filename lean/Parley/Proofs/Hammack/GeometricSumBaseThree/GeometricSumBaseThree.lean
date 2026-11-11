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
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
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

/-! Written from proofs/hammack/geometric-sum-base-three.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.GeometricSumBaseThree.GeometricSumBaseThree

theorem geometric_sum_base_three (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (3 ^ k.toNat : ℚ)) = (3 ^ (n + 1).toNat - 3) / 2 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (3 ^ j.toNat : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → (S k : ℚ) = (3 ^ (k + 1).toNat - 3) / 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc (S 1 : ℚ) = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (3 ^ j.toNat : ℚ)) := by simp (disch := omega) only [hD1]; push_cast; norm_num
        _ = 3 ^ 1 := by
            have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (3 ^ k.toNat : ℚ)) = 3 ^ 1 := by parley_instance ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (3 ^ j.toNat : ℚ))) (a := (1 : ℤ))))
            exact hI
        _ = (3 ^ (1 + 1) - 3) / 2 := by norm_num
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + 3 ^ (k + 1).toNat := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (3 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (3 ^ j.toNat : ℤ)) + 3 ^ (k + 1).toNat := by
              have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), (3 ^ b.toNat : ℤ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, (3 ^ b.toNat : ℤ)) + 3 ^ (k + 1).toNat := by parley_instance_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (3 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1))
              exact hI
          _ = S k + 3 ^ (k + 1).toNat := by simp (disch := omega) only [hD1]
      -- 1.3. mun:exponent-step a := 3, m := k + 1
      have s1_3 : (3 ^ (k + 1 + 1).toNat : ℤ) = 3 ^ (k + 1).toNat * 3 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (3 : ℤ)) (m := k + 1) (by parley_side))
      -- 1.4. calculation
      calc (S (k + 1) : ℚ) = (S k : ℚ) + 3 ^ (k + 1).toNat := by parley_side
        _ = (3 ^ (k + 1).toNat - 3) / 2 + 3 ^ (k + 1).toNat := by (have h := congrArg (fun t : ℚ => t + 3 ^ (k + 1).toNat) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = (3 ^ (k + 1).toNat * 3 - 3) / 2 := by parley_ring
        _ = (3 ^ (k + 1 + 1).toNat - 3) / 2 := by
            have e_w : (3 ^ (k + 1).toNat * 3 : ℚ) = 3 ^ (k + 1 + 1).toNat := by have h := congrArg (fun x : ℤ => (x : ℚ)) s1_3.symm; push_cast at h; linear_combination (norm := parley_norm) h
            (have h := congrArg (fun t : ℚ => (t - 3) / 2) e_w; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (3 ^ k.toNat : ℚ)) = (S n : ℚ) := by simp (disch := omega) only [hD1]; push_cast; norm_num
    _ = (3 ^ (n + 1).toNat - 3) / 2 := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.GeometricSumBaseThree.GeometricSumBaseThree
