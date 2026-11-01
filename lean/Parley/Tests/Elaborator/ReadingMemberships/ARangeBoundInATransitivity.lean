module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInATransitivity

theorem a_range_bound_in_a_transitivity (n : ℤ) (m : ℤ) (k : ℤ) (H3 : k ∈ Finset.Icc 1 n) (H4 : n < m) :
    k < m := by
  -- 1. transitivity, from H3, H4
  have s1 : k < m := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInATransitivity
