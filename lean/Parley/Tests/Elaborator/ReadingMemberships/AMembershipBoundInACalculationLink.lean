module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink

theorem a_membership_bound_in_a_calculation_link (k : ℤ) (hH1 : 0 < k) (m : ℤ) (hH3 : k ≤ m) :
    0 < m := by
  -- 1. calculation
  calc (0 : ℤ) < k := hH1
    _ ≤ m := hH3

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink
