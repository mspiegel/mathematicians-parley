module

public import ArithTactics
public import Counting
public import FactorialTactics
public import InstanceTactics
public import NormTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Parley.Items.Stdlib.Numbers
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.Binomial.Binomial

/-! Written from proofs/hammack/binomial-sum-with-powers-of-two.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo

theorem binomial_sum_with_powers_of_two (n : ℤ) (hH1 : 0 ≤ n) :
    (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℤ) : ℤ)) = 3 ^ n.toNat := by
  -- 1. proof
  -- what this block shows, Lean's types give
  -- 2. membership
  -- 3. proof
  have s3 : ∀ k : ℤ, k ∈ Finset.Icc 0 n → (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat = 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ) := by
    intro k hJ
    try push_cast at hJ
    try have hJ_bounds := Finset.mem_Icc.mp hJ
    -- 3.1. mun:one-power m := n − k
    have s3_1 : (1 ^ (n - k) : ℚ) = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_one_power (m := n - k))
    -- 3.2. algebra, from 3.1
    linear_combination (norm := parley_norm) (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ)) * s3_1
  -- 4. arithmetic
  have s4 : (1 + 2 : ℤ) = 3 := by parley_arith
  -- 5. calculation
  try qify
  calc (∑ k ∈ Finset.Icc (0 : ℤ) n, (2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ) : ℚ)) = (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat : ℚ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => 2 ^ k.toNat * (LeanBridges.Counting.choose n k : ℚ))) (u := (fun k : ℤ => (LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat)) (a := (0 : ℤ)) (b := n) (by parley_side))
    _ = (1 + 2) ^ n.toNat := by
        have hI : (1 + 2) ^ n.toNat = (∑ k ∈ Finset.Icc (0 : ℤ) n, ((LeanBridges.Counting.choose n k : ℚ) * 1 ^ (n - k) * 2 ^ k.toNat : ℚ)) := by parley_instance_real ((Parley.Proofs.Wiedijk.Binomial.Binomial.binomial (x := (1 : ℝ)) (y := (2 : ℝ)) (n := n) hH1))
        exact hI.symm
    _ = 3 ^ n.toNat := by (have h := congrArg (fun t : ℤ => t ^ n.toNat) s4; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.BinomialSumWithPowersOfTwo.BinomialSumWithPowersOfTwo
