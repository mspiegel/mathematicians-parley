module

public import Tactics

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInMembership

theorem a_for_all_line_in_membership (hH1 : True) :
    True := by
  -- 1. proof
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInMembership
