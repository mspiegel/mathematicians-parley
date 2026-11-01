module

public import Parley.Library

/-! Written from tests/elaborator/an-assume-line-of-several-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnAssumeLineOfSeveralSentences

theorem an_assume_line_of_several_sentences (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : b = 2) :
    a + b = 3 := by
  -- 1. substitute a = 1 (H3)
  have s1 : a + b = 1 + b := by parley_subst H3a
  -- 2. substitute b = 2 (H3)
  have s2 : 1 + b = 1 + 2 := by parley_subst H3b
  -- 3. calculation
  have s3 : a + b = 3 := by
    calc a + b = 1 + b := by parley_side
      _ = 1 + 2 := by parley_side
      _ = 3 := by norm_num
  all_goals parley_side

end Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnAssumeLineOfSeveralSentences
