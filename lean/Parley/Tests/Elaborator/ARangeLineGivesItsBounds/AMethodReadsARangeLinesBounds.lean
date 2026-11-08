module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/a-range-line-gives-its-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AMethodReadsARangeLinesBounds

theorem a_method_reads_a_range_lines_bounds (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (2 : ℤ) n) :
    0 < k := by
  -- 1. inequalities, from H2
  parley_order

end Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AMethodReadsARangeLinesBounds
