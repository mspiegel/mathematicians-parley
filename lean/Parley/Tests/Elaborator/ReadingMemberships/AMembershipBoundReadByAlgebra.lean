module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByAlgebra

theorem a_membership_bound_read_by_algebra (x : ℝ) (hH2 : ∃ m : ℤ, 0 < m ∧ (m : ℝ) = x) :
    x / x = 1 := by
  -- 1. algebra, from H2
  have s1 : x / x = 1 := by obtain ⟨_, _, rfl⟩ := hH2; parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByAlgebra
