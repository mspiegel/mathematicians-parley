module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
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

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.SumEmptyRange

theorem sum_empty_range :
    (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by
  -- 1. mun:sums-sum-empty-range a := 1, b := 0
  have r16_1 : (0 : ℤ) < 1 := by parley_arith
  exact (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) r16_1)

end Parley.Tests.Stdlib.Sums.SumEmptyRange
