module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartByMembership

theorem an_and_part_by_membership (a : ℝ) (b : ℝ) (H3 : a = 1 ∧ True) :
    True := by
  -- 1. membership, from H3
  parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartByMembership
