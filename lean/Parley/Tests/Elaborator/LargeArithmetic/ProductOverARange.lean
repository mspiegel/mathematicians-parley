module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.BigOperators
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.ProductOverARange

theorem product_over_a_range :
    (∏ k ∈ Finset.Icc (0 : ℤ) (3 : ℤ), (7 - k : ℤ)) ≤ 840 := by
  -- 1. arithmetic
  have s1 : (∏ k ∈ Finset.Icc (0 : ℤ) (3 : ℤ), (7 - k : ℤ)) ≤ 840 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.ProductOverARange
