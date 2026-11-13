module

public import AlgebraTactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/algebra-and-inequalities-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember

theorem algebra_at_a_member (n : ℤ) (hH1 : 0 < n) :
    (∀ i : ℤ, i ∈ Finset.Icc 1 n → i + i = 2 * i) := by
  -- 1. algebra
  intro i h_i; parley_ring

end Parley.Tests.Elaborator.AlgebraAndInequalitiesAtAMember.AlgebraAtAMember
