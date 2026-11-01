module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsAFirstRow

theorem a_second_sentence_as_a_first_row (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : b > 0) :
    b + 1 > 1 := by
  -- 1. inequalities
  have s1 : b + 1 > 1 := by parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceAsAFirstRow
