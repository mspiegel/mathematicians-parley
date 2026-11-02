module

public import Tactics

/-! Written from tests/elaborator/an-order-claimed-with-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnOrderClaimedWithAnIdentity.AnOrderClaimedWithAnIdentity

theorem an_order_claimed_with_an_identity (x : ℝ) (y : ℝ) (hH3 : x = y) :
    x ≤ (y / 1) ^ 1 := by
  -- 1. inequalities
  have s1 : x ≤ (y / 1) ^ 1 := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.AnOrderClaimedWithAnIdentity.AnOrderClaimedWithAnIdentity
