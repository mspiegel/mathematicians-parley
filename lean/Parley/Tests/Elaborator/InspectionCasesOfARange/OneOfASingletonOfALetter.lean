module

public import Tactics

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingletonOfALetter

theorem one_of_a_singleton_of_a_letter (a : ℝ) (x : ℝ) (hH2 : x ∈ ({a} : Set ℝ)) :
    x = a := by
  -- 1. inspection, from H2
  have s1 : x = a := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfASingletonOfALetter
