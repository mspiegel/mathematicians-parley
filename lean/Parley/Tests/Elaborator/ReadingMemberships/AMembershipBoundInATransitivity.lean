module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity

theorem a_membership_bound_in_a_transitivity (c : ℤ) (hH1 : 0 ≤ c) (m : ℤ) (hH3 : c ≤ m) :
    0 ≤ m := by
  -- 1. transitivity, from H1, H3
  exact le_trans hH1 hH3

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity
