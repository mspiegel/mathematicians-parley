module

public import LeanBridges

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra

theorem a_second_sentence_by_algebra (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  have s1 : b * b = 4 := by linear_combination (norm := parley_norm) (b + 2) * hH3b
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByAlgebra
