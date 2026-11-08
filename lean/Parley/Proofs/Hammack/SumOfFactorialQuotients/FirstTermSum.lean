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
public import Mathlib.Tactic.Positivity.Finset
public import Parley.Items.Stdlib.Sums

/-! Written from proofs/hammack/sum-of-factorial-quotients.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.SumOfFactorialQuotients.FirstTermSum

theorem first_term_sum (t : ℤ → ℝ) :
    (∑ j ∈ Finset.Icc (1 : ℤ) (1 : ℤ), (t j : ℝ)) = t 1 := by
  -- 1. mun:sum-single a := 1
  exact (Parley.Items.Stdlib.Sums.mun_sum_single (t := t) (a := (1 : ℤ)))

end Parley.Proofs.Hammack.SumOfFactorialQuotients.FirstTermSum
