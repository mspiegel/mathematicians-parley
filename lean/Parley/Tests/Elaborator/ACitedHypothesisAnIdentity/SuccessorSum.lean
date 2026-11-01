module

public import Parley.Library

/-! Written from tests/elaborator/a-cited-hypothesis-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum

theorem successor_sum (i : ℕ) (j : ℕ) (hH2 : 0 < j) (hH3 : (j : ℤ) = (i : ℤ) + 1) :
    2 * (j : ℤ) = 2 * (i : ℤ) + 2 := by
  -- 1. algebra, from H3
  have s1 : 2 * (j : ℤ) = 2 * (i : ℤ) + 2 := by linear_combination (2) * hH3
  all_goals parley_side

end Parley.Tests.Elaborator.ACitedHypothesisAnIdentity.SuccessorSum
