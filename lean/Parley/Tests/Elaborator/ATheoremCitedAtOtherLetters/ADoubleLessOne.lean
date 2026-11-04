module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/a-theorem-cited-at-other-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne

theorem a_double_less_one (C : ℝ) :
    C + C - C = C := by
  -- 1. algebra
  have s1 : C + C - C = C := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ATheoremCitedAtOtherLetters.ADoubleLessOne
