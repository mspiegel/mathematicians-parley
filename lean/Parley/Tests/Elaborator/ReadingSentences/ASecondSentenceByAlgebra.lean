module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra

theorem a_second_sentence_by_algebra (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  have s1 : b * b = 4 := by linear_combination (b + 2) * H3b
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra
