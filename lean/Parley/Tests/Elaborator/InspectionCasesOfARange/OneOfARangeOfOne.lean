module

public import Parley.Library

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfOne

theorem one_of_a_range_of_one (k : ℤ) (hH1 : k ∈ Finset.Icc (2 : ℤ) (2 : ℤ)) :
    2 = k := by
  -- 1. inspection, from H1
  have s1 : 2 = k := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeOfOne
