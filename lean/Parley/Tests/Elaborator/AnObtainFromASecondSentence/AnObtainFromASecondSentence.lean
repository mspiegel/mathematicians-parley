module

public import LeanBridges
public import Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven

/-! Written from tests/elaborator/an-obtain-from-a-second-sentence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnObtainFromASecondSentence.AnObtainFromASecondSentence

theorem an_obtain_from_a_second_sentence :
    (∃ j : ℤ, 4 = 2 * j) := by
  -- 1. obtain j: thm:four-positive-and-even
  obtain ⟨j, s1⟩ := Parley.Tests.Elaborator.AnObtainFromASecondSentence.FourPositiveAndEven.four_positive_and_even.2
  -- 2. exhibit, from 1
  have s2 : ∃ j : ℤ, 4 = 2 * j := ⟨j, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.AnObtainFromASecondSentence.AnObtainFromASecondSentence
