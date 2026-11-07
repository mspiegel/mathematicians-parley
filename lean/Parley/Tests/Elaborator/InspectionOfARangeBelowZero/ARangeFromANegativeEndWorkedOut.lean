module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/inspection-of-a-range-below-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeFromANegativeEndWorkedOut

theorem a_range_from_a_negative_end_worked_out (n : ℤ) (n : ℤ) (hH2 : n ∈ Finset.Icc (0 - 4 : ℤ) (0 : ℤ)) :
    ((((n = -4 ∨ n = -3) ∨ n = -2) ∨ n = -1) ∨ n = 0) := by
  -- 1. inspection, from H2
  have s1 : (((n = -4 ∨ n = -3) ∨ n = -2) ∨ n = -1) ∨ n = 0 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeFromANegativeEndWorkedOut
