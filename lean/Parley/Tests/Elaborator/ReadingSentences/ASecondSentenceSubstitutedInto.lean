module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceSubstitutedInto

theorem a_second_sentence_substituted_into (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : a < b) (H4 : b = 2) :
    a < 2 := by
  -- 1. substitute b = 2 (H4) into H3
  have s1 : a < 2 := by parley_subst_at H4 H3a
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceSubstitutedInto
