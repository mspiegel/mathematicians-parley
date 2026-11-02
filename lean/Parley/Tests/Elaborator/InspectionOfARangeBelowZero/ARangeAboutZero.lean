module

public import LeanBridges

/-! Written from tests/elaborator/inspection-of-a-range-below-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeAboutZero

theorem a_range_about_zero (n : ℤ) (n : ℤ) (hH2 : n ∈ Finset.Icc (-1 : ℤ) (1 : ℤ)) :
    ((n = -1 ∨ n = 0) ∨ n = 1) := by
  -- 1. inspection, from H2
  have s1 : (n = -1 ∨ n = 0) ∨ n = 1 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionOfARangeBelowZero.ARangeAboutZero
