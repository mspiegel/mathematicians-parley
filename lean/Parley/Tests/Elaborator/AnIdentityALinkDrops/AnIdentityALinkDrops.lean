module

public import Parley.Library

/-! Written from tests/elaborator/an-identity-a-link-drops.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityALinkDrops.AnIdentityALinkDrops

theorem an_identity_a_link_drops (b : ℤ → ℝ) (k : ℤ) (hH3 : b k * 1 ^ k = b k * 1) :
    b k * 1 ^ k = b k := by
  -- 1. calculation
  have s1 : b k * 1 ^ k = b k := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AnIdentityALinkDrops.AnIdentityALinkDrops
