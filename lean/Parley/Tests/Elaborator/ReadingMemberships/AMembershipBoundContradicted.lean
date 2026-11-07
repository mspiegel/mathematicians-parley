module

public import ArithTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted

theorem a_membership_bound_contradicted (k : ℤ) (hH1 : 0 < k) :
    ¬ k ≤ 0 := by
  -- 1. contradiction
  have s1 : ¬ k ≤ 0 := by
    by_contra hc_hS
    have hS : k ≤ 0 := by parley_suppose hc_hS
    -- 1.1. inequalities, from S
    have s1_1 : ¬ k > 0 := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted
