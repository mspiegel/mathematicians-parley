module

public import LeanBridges

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne

theorem a_double_less_one (C : ℝ) :
    C + C - C = C := by
  -- 1. algebra
  have s1 : C + C - C = C := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne
