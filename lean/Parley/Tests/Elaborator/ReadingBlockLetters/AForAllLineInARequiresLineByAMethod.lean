module

public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInARequiresLineByAMethod

theorem a_for_all_line_in_a_requires_line_by_a_method (hH1 : ∀ x : ℝ, x ^ 2 + 1 > 0) :
    True := by
  -- 1. proof
  -- what this block shows, Lean's types give
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInARequiresLineByAMethod
