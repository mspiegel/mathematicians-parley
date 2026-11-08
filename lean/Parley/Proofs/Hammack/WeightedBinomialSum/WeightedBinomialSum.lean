module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.WeightedBinomialSum

theorem weighted_binomial_sum (n : ℤ) (hH1 : 0 < n) :
    (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) * (LeanBridges.Counting.choose n k : ℚ) : ℚ)) = (n : ℚ) * 2 ^ (n - 1) := by
  -- 1. thm:weighted-row-sum m := n − 1
  have r172_1 : 0 ≤ n - 1 := by exact (Parley.Items.Stdlib.Numbers.mun_nat_minus_one (n := n) (by parley_side))
  have s1 : (∑ k ∈ Finset.Icc (1 : ℤ) (n - 1 + 1), ((k : ℚ) * (LeanBridges.Counting.choose (n - 1 + 1) k : ℚ) : ℚ)) = ((n : ℚ) - 1 + 1) * 2 ^ (n - 1) := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)) | exact_mod_cast ((Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side))).symm | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); parley_int_power h) | (have h := (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum.weighted_row_sum (m := n - 1) (by parley_side)); parley_side)
  -- 2. substitute
  have c1 : n - 1 + 1 = n := by parley_ring
  have c1_w : (n : ℚ) - 1 + 1 = (n : ℚ) := by have h := congrArg (fun x : ℤ => (x : ℚ)) c1; push_cast at h; linear_combination (norm := parley_norm) h
  have row1 : (∑ k ∈ Finset.Icc (1 : ℤ) n, ((k : ℚ) * (LeanBridges.Counting.choose n k : ℚ) : ℚ)) = (n : ℚ) * 2 ^ (n - 1) := by first | parley_put_at c1_w s1 | parley_put_at c1 s1 | parley_subst_at c1_w s1 | parley_subst_at c1 s1
  exact row1

end Parley.Proofs.Hammack.WeightedBinomialSum.WeightedBinomialSum
