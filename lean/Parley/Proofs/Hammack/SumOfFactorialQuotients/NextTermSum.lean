module

public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.NextTermSum

theorem next_term_sum (k : ℤ) (hH1 : 0 < k) (t : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (k + 1), (t j : ℝ)) = (∑ j ∈ Finset.Icc (1 : ℤ) k, (t j : ℝ)) + t (k + 1) := by
  -- 1. mun:sum-extended a := 1, n := k
  have r40_1 : k ≥ 1 := by parley_side
  exact (Parley.Items.Stdlib.Sums.mun_sum_extended (t := t) (a := (1 : ℤ)) (n := k) r40_1)

end Parley.Proofs.Hammack.SumOfFactorialQuotients.NextTermSum
