module

public import AlgebraTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember

theorem algebra_at_a_member (n : ℤ) (hH1 : 0 < n) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 n → i + i = 2 * i) := by
  -- 1. algebra
  have s1 : ∀ i : ℤ, i ∈ Finset.Icc 1 n → i + i = 2 * i := by intro i h_i; parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember
