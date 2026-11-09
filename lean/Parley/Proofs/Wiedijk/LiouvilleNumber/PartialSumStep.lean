module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Wiedijk.LiouvilleNumber.TermsReal

/-! Written from proofs/wiedijk/liouville-number.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep

theorem partial_sum_step (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by
  -- 1. thm:terms-real m := n + 1
  -- 2. mun:sum-extended a := 1, from 1
  have r218_1 : n ≥ 1 := by parley_order
  have s2 : (∑ k ∈ Finset.Icc (1 : ℤ) (n + 1), (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) = (∑ k ∈ Finset.Icc (1 : ℤ) n, (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ)) + 1 / 2 ^ LeanBridges.Counting.factorial (n + 1) := by exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := (fun k : ℤ => (1 / 2 ^ LeanBridges.Counting.factorial k : ℚ))) (a := (1 : ℤ)) (n := n) r218_1)
  -- 3. algebra, from D0, 2
  linear_combination (norm := parley_field) s2

end Parley.Proofs.Wiedijk.LiouvilleNumber.PartialSumStep
