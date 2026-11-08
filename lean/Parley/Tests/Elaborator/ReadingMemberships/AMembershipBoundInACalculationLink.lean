module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink

theorem a_membership_bound_in_a_calculation_link (k : ℤ) (hH1 : 0 < k) (m : ℤ) (hH3 : k ≤ m) :
    0 < m := by
  -- 1. calculation
  calc (0 : ℤ) < k := by parley_side
    _ ≤ m := by parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink
