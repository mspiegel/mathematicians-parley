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

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted

theorem a_membership_bound_contradicted (k : ℤ) (hH1 : 0 < k) :
    ¬ k ≤ 0 := by
  -- 1. contradiction
  intro hS
  -- 1.1. inequalities, from S
  have s1_1 : ¬ k > 0 := by linarith only [hS]
  exact s1_1 hH1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted
