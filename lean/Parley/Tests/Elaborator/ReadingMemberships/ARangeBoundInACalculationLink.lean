module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInACalculationLink

theorem a_range_bound_in_a_calculation_link (n : ℤ) (m : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) (hH4 : n ≤ m) :
    k ≤ m := by
  -- 1. calculation
  have s1 : k ≤ m := by
    calc k ≤ n := by parley_side
      _ ≤ m := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInACalculationLink
