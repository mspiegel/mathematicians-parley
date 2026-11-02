module

public import LeanBridges

/-! Written from tests/elaborator/inspection-of-a-range-below-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeBelowZero

theorem a_range_below_zero (n : ℤ) (n : ℤ) (hH2 : n ∈ Finset.Icc (-2 : ℤ) (0 : ℤ)) :
    ((n = -2 ∨ n = -1) ∨ n = 0) := by
  -- 1. inspection, from H2
  have s1 : (n = -2 ∨ n = -1) ∨ n = 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeBelowZero
