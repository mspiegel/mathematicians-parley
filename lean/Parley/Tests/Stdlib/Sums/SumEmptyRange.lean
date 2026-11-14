module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.SumEmptyRange

theorem sum_empty_range :
    (∑ k ∈ Finset.Icc (1 : ℤ) (0 : ℤ), (2 * k - 1 : ℤ)) = 0 := by
  -- 1. mun:sums-sum-empty-range a := 1, b := 0
  have r16_1 : (0 : ℤ) < 1 := by norm_num
  exact (Parley.Items.Stdlib.Sums.mun_sum_empty_range (t := (fun k : ℤ => 2 * k - 1)) (a := (1 : ℤ)) (b := (0 : ℤ)) (by norm_num))

end Parley.Tests.Stdlib.Sums.SumEmptyRange
