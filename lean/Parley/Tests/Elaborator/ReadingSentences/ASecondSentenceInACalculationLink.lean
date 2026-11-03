module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInACalculationLink

theorem a_second_sentence_in_a_calculation_link (a : ℝ) (b : ℝ) (hH3a : a = 1) (hH3b : b = 2) :
    b = 1 + 1 := by
  -- 1. calculation
  have s1 : b = 1 + 1 := by
    calc b = 2 := by parley_side
      _ = 1 + 1 := by norm_num
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInACalculationLink
