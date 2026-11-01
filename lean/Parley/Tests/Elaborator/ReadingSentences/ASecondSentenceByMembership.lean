module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership

theorem a_second_sentence_by_membership (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : True) :
    True := by
  -- 1. membership, from H3
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceByMembership
