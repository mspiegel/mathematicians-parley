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

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfFive

theorem one_of_a_range_of_five (k : ℤ) (hH1 : k ∈ Finset.Icc (0 : ℤ) (4 : ℤ)) :
    ((((k = 4 ∨ k = 0) ∨ 2 = k) ∨ k = 1) ∨ k = 1 + 2) := by
  -- 1. inspection, from H1
  have s1 : (((k = 4 ∨ k = 0) ∨ 2 = k) ∨ k = 1) ∨ k = 1 + 2 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfFive
