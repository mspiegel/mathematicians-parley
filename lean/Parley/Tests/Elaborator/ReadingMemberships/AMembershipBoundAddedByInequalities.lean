module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities

theorem a_membership_bound_added_by_inequalities (k : ℤ) (hH1 : 0 < k) :
    k + 1 ≥ 2 := by
  -- 1. inequalities, from H1
  parley_order

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities
