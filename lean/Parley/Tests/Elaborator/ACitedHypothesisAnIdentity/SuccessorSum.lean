module

public import Tactics

/-! Written from tests/elaborator/a-cited-hypothesis-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum

theorem successor_sum (i : ℤ) (hH1 : 0 ≤ i) (j : ℤ) (hH2 : 0 < j) (hH3 : j = i + 1) :
    2 * j = 2 * i + 2 := by
  -- 1. algebra, from H3
  have s1 : 2 * j = 2 * i + 2 := by linear_combination (norm := parley_norm) (2) * hH3
  all_goals exact s1

end Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum
