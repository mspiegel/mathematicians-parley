module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership

theorem a_second_sentence_by_membership (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : True) :
    True := by
  -- 1. membership, from H3
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership
