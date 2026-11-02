module

public import Tactics

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfTwo

theorem one_of_a_range_of_two (x : ℤ) (hH1 : x ∈ Finset.Icc (1 : ℤ) (2 : ℤ)) :
    (x = 1 ∨ x = 2) := by
  -- 1. inspection, from H1
  have s1 : x = 1 ∨ x = 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfTwo
