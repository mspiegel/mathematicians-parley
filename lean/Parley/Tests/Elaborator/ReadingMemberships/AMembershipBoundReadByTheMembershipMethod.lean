module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByTheMembershipMethod

theorem a_membership_bound_read_by_the_membership_method (x : ℝ) (hH2 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) :
    True := by
  -- 1. membership, from H2
  exact trivial

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByTheMembershipMethod
