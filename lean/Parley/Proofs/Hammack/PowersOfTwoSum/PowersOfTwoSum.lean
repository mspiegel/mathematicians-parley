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
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
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

/-! Written from proofs/hammack/powers-of-two-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PowersOfTwoSum.PowersOfTwoSum

theorem powers_of_two_sum (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, (2 ^ k.toNat : ℤ)) = 2 ^ (n + 1).toNat - 2 := by
  set S : ℤ → ℤ := fun m : ℤ => ∑ j ∈ Finset.Icc (1 : ℤ) m, (2 ^ j.toNat : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → S k = 2 ^ (k + 1).toNat - 2 := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
        _ = 2 ^ 1 := by
            have hI : (∑ k ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (2 ^ k.toNat : ℤ)) = 2 ^ 1 := by parley_instance_cast ((Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ))))
            exact hI
        _ = 2 ^ (1 + 1) - 2 := by norm_num
    | succ k hK hIH =>
      -- 1.2. calculation
      have r28_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + 2 ^ (k + 1).toNat := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (2 ^ j.toNat : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (2 ^ j.toNat : ℤ)) + 2 ^ (k + 1).toNat := by
              have hI : (∑ b ∈ Finset.Icc (1 : ℤ) (k + 1), (2 ^ b.toNat : ℤ)) = (∑ b ∈ Finset.Icc (1 : ℤ) k, (2 ^ b.toNat : ℤ)) + 2 ^ (k + 1).toNat := by parley_instance_cast ((Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => (2 ^ j.toNat : ℚ))) (a := (1 : ℤ)) (n := k) r28_1))
              exact hI
          _ = S k + 2 ^ (k + 1).toNat := by simp (disch := omega) only [hD1]
      -- 1.3. mun:exponent-step m := k + 1
      have s1_3 : (2 ^ (k + 1 + 1).toNat : ℤ) = 2 ^ (k + 1).toNat * 2 := by exact (Parley.Items.Stdlib.Numbers.mun_exponent_step (a := (2 : ℤ)) (m := k + 1) (add_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hK)) (by norm_num)))
      -- 1.4. calculation
      calc S (k + 1) = S k + 2 ^ (k + 1).toNat := by exact s1_2
        _ = 2 ^ (k + 1).toNat - 2 + 2 ^ (k + 1).toNat := by (have h := congrArg (fun t : ℤ => t + 2 ^ (k + 1).toNat) hIH; push_cast at h ⊢; all_goals exact_mod_cast h)
        _ = 2 ^ (k + 1).toNat * 2 - 2 := by parley_ring
        _ = 2 ^ (k + 1 + 1).toNat - 2 := by (have h := congrArg (fun t : ℤ => t - 2) s1_3.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 2. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) n, (2 ^ k.toNat : ℤ)) = S n := by simp (disch := omega) only [hD1]
    _ = 2 ^ (n + 1).toNat - 2 := by exact (s1 n hH1)

end Parley.Proofs.Hammack.PowersOfTwoSum.PowersOfTwoSum
