module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated

theorem a_second_sentence_instantiated (a : ℝ) (b : ℝ) (H3a : a = 1) (H3b : ∀ x : ℝ, x * 0 = 0) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  have s1 : b * 0 = 0 := by linear_combination (H3a)
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.ASecondSentenceInstantiated
