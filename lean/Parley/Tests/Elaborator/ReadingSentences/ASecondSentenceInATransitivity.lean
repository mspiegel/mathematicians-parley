module

public import LeanBridges

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInATransitivity

theorem a_second_sentence_in_a_transitivity (a : ℝ) (b : ℝ) (c : ℝ) (hH4a : a = 1) (hH4b : b ≤ c) (hH5 : c < 0) :
    b < 0 := by
  -- 1. transitivity, from H4, H5
  have s1 : b < 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInATransitivity
