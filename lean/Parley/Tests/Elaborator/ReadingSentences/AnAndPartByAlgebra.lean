module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra

theorem an_and_part_by_algebra (a : ℝ) (b : ℝ) (H3 : a = 1 ∧ b = 2) :
    b * b = 4 := by
  -- 1. algebra, from H3
  have s1 : b * b = 4 := by linear_combination (b + 2) * H3.2
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartByAlgebra
