module

public import LeanBridges

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingleton

theorem one_of_a_singleton (x : ℤ) (hH1 : x ∈ ({(3 : ℤ)} : Set ℤ)) :
    x = 3 := by
  -- 1. inspection, from H1
  have s1 : x = 3 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingleton
