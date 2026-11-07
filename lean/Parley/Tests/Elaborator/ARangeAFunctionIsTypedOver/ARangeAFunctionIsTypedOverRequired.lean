module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-range-a-function-is-typed-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOverRequired

theorem a_range_a_function_is_typed_over_required (n : ℤ) (hH1 : 0 < n) (a : ℤ → ℝ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    a k + 0 = a k := by
  -- 1. algebra
  have s1 : a k + 0 = a k := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ARangeAFunctionIsTypedOver.ARangeAFunctionIsTypedOverRequired
