module

public import LeanBridges

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInACalculationLink

theorem a_range_bound_in_a_calculation_link (n : ℤ) (m : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) (hH4 : n ≤ m) :
    k ≤ m := by
  -- 1. calculation
  have s1 : k ≤ m := by
    calc k ≤ n := by parley_side
      _ ≤ m := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInACalculationLink
