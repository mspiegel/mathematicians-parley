module

public import Counting
public import FactorialTactics
public import NormTactics
public import PowerTactics
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
public import Parley.Items.Stdlib.Sums
public import Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum
public import Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm

/-! Written from proofs/hammack/weighted-binomial-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum

set_option maxHeartbeats 400000 in
theorem weighted_row_sum (m : ℤ) (hH1 : 0 ≤ m) :
    (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (k * (LeanBridges.Counting.choose (m + 1) k : ℤ) : ℤ)) = (m + 1) * 2 ^ m.toNat := by
  -- 1. thm:weighted-term
  have s1 : ∀ k : ℤ, k ∈ Finset.Icc 1 (m + 1) → k * (LeanBridges.Counting.choose (m + 1) k : ℤ) = (m + 1) * (LeanBridges.Counting.choose m (k - 1) : ℤ) := by intro k h_k; (exact (Parley.Proofs.Hammack.WeightedBinomialSum.WeightedTerm.weighted_term (m := m) (by parley_side) (k := k) (by parley_side)))
  -- 2. proof
  -- what this block shows, Lean's types give
  -- 3. proof
  -- what this block shows, Lean's types give
  -- 4. proof
  -- what this block shows, Lean's types give
  -- 5. proof
  -- what this block shows, Lean's types give
  -- 6. calculation
  have s6 : (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℤ) : ℤ)) = 2 ^ m.toNat := by
    calc (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (0 : ℤ) m, ((LeanBridges.Counting.choose m k : ℤ) : ℤ)) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))) | exact_mod_cast ((Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ)))).symm | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sums.mun_sum_shift (t := (fun k : ℤ => (LeanBridges.Counting.choose m k : ℤ))) (a := (0 : ℤ)) (b := m) (c := (1 : ℤ))); parley_side)
      _ = 2 ^ m.toNat := by exact (Parley.Proofs.Hammack.WeightedBinomialSum.BinomialRowSum.binomial_row_sum (m := m) (by parley_side))
  -- 7. calculation
  calc (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), (k * (LeanBridges.Counting.choose (m + 1) k : ℤ) : ℤ)) = (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((m + 1) * (LeanBridges.Counting.choose m (k - 1) : ℤ) : ℤ)) := by exact (Parley.Items.Stdlib.Sums.mun_sum_termwise (t := (fun k : ℤ => k * (LeanBridges.Counting.choose (m + 1) k : ℤ))) (u := (fun k : ℤ => (m + 1) * (LeanBridges.Counting.choose m (k - 1) : ℤ))) (a := (1 : ℤ)) (b := m + 1) s1)
    _ = (m + 1) * (∑ k ∈ Finset.Icc (1 : ℤ) (m + 1), ((LeanBridges.Counting.choose m (k - 1) : ℤ) : ℤ)) := by linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sums.mun_sum_scaled (t := (fun k : ℤ => (LeanBridges.Counting.choose m (k - 1) : ℤ))) (a := (1 : ℤ)) (b := m + 1) (c := m + 1)).symm
    _ = (m + 1) * 2 ^ m.toNat := by (have h := congrArg (fun t : ℤ => (m + 1) * t) s6; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Hammack.WeightedBinomialSum.WeightedRowSum
