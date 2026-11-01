module

public import Parley.Library

/-! Written from tests/elaborator/inspection-cases-of-a-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeEndingInAQuotient

theorem one_of_a_range_ending_in_a_quotient (k : ℤ) (H1 : 1 - 2 + 1 ≤ (k : ℚ) ∧ (k : ℚ) ≤ 6 / 3) :
    ((k = 0 ∨ k = 1) ∨ k = 2) := by
  -- 1. inspection, from H1
  have s1 : (k = 0 ∨ k = 1) ∨ k = 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.InspectionCasesOfARange.OneOfARangeEndingInAQuotient
