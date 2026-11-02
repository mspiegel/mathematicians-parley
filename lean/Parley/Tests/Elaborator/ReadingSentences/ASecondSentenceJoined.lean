module

public import LeanBridges

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceJoined

theorem a_second_sentence_joined (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    b = 2 := by
  -- 1. restate H3
  have s1 : b = 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceJoined
