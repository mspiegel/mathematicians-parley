module

public import AlgebraTactics
public import Functions
public import SubstTactics
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
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-eight-i-minus-five.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfEightIMinusFive.SumOfEightIMinusFive

theorem sum_of_eight_i_minus_five (n : ℤ) (hH1 : 0 < n) :
    (∑ i ∈ Finset.Icc (1 : ℤ) n, (8 * i - 5 : ℤ)) = 4 * n ^ 2 - n := by
  set S : ℤ → ℤ := fun m => ∑ j ∈ Finset.Icc (1 : ℤ) m, (8 * j - 5 : ℤ) with hD1
  -- 1. induction on k starting at 1
  have s1 : ∀ k : ℤ, 0 < k → S k = 4 * k ^ 2 - k := by
    intro k h_k
    replace h_k : 1 ≤ k := by omega
    induction k, h_k using LeanBridges.Functions.le_induction with
    | base =>
      -- 1.1. calculation
      calc S 1 = (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (8 * j - 5 : ℤ)) := by simp (disch := omega) only [hD1]
        _ = 8 * 1 - 5 := (Parley.Items.Stdlib.Sums.mun_sum_single (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)))
        _ = 4 * 1 ^ 2 - 1 := by norm_num
    | succ k hK hIH =>
      -- 1.2. calculation
      have r27_1 : k ≥ 1 := by parley_side
      have s1_2 : S (k + 1) = S k + (8 * (k + 1) - 5) := by
        calc S (k + 1) = (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (8 * j - 5 : ℤ)) := by simp (disch := omega) only [hD1]
          _ = (∑ j ∈ Finset.Icc (1 : ℤ) k, (8 * j - 5 : ℤ)) + (8 * (k + 1) - 5) := (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun j : ℤ => 8 * j - 5)) (a := (1 : ℤ)) (n := k) r27_1)
          _ = S k + (8 * (k + 1) - 5) := by simp (disch := omega) only [hD1]
      -- 1.3. calculation
      calc S (k + 1) = S k + (8 * (k + 1) - 5) := by parley_side
        _ = 4 * k ^ 2 - k + (8 * (k + 1) - 5) := by parley_subst hIH
        _ = 4 * (k + 1) ^ 2 - (k + 1) := by parley_ring
  -- 2. calculation
  calc (∑ i ∈ Finset.Icc (1 : ℤ) n, (8 * i - 5 : ℤ)) = S n := by simp (disch := omega) only [hD1]
    _ = 4 * n ^ 2 - n := by exact (s1 n (by parley_side))

end Parley.Proofs.Hammack.SumOfEightIMinusFive.SumOfEightIMinusFive
