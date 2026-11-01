module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceContradicted

theorem a_second_sentence_contradicted (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : b ≠ 2) :
    (b = 2 → a = 0) := by
  -- 1. proof
  have s1 : b = 2 → a = 0 := by
    intro K1
    -- 1.1. restate K1
    have s1_1 : b = 2 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceContradicted
