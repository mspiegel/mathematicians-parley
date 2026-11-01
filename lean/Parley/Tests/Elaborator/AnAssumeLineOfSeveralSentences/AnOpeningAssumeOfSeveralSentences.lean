module

public import Parley.Library

/-! Written from tests/elaborator/an-assume-line-of-several-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnOpeningAssumeOfSeveralSentences

theorem an_opening_assume_of_several_sentences (a : ℝ) (b : ℝ) :
    (a = 1 ∧ b = 2 → a + b = 3) := by
  -- 1. proof
  have s1 : a = 1 ∧ b = 2 → a + b = 3 := by
    intro hK1
    -- 1.1. substitute a = 1 (K1)
    have s1_1 : a + b = 1 + b := by parley_subst hK1.1
    -- 1.2. substitute b = 2 (K1)
    have s1_2 : 1 + b = 1 + 2 := by parley_subst hK1.2
    -- 1.3. calculation
    have s1_3 : a + b = 3 := by
      calc a + b = 1 + b := by parley_side
        _ = 1 + 2 := by parley_side
        _ = 3 := by norm_num
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AnAssumeLineOfSeveralSentences.AnOpeningAssumeOfSeveralSentences
