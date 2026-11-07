module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-order-claimed-with-an-identity.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnOrderClaimedWithAnIdentity.AnOrderClaimedWithAnIdentity

theorem an_order_claimed_with_an_identity (x : ℝ) (y : ℝ) (hH3 : x = y) :
    x ≤ (y / 1) ^ 1 := by
  -- 1. inequalities
  have s1 : x ≤ (y / 1) ^ 1 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.AnOrderClaimedWithAnIdentity.AnOrderClaimedWithAnIdentity
