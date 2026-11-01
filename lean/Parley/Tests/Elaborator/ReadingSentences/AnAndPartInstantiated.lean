module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated

theorem an_and_part_instantiated (a : ℝ) (b : ℝ) (H3 : a = 1 ∧ (∀ x : ℝ, x * 0 = 0)) :
    b * 0 = 0 := by
  -- 1. instantiate x := b in H3
  have s1 : b * 0 = 0 := by linear_combination (H3)
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInstantiated
