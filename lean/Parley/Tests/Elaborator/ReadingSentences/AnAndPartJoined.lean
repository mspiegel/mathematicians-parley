module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartJoined

theorem an_and_part_joined (a : ℝ) (b : ℝ) (H3 : a = 1 ∧ b = 2) :
    b = 2 := by
  -- 1. restate H3
  have s1 : b = 2 := by parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartJoined
