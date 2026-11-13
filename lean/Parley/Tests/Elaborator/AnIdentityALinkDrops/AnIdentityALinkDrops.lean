module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-identity-a-link-drops.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIdentityALinkDrops.AnIdentityALinkDrops

theorem an_identity_a_link_drops (b : ℤ → ℝ) (k : ℤ) (hH3 : b k * 1 ^ k = b k * 1) :
    b k * 1 ^ k = b k := by
  -- 1. calculation
  exact by simpa only [mul_one] using hH3

end Parley.Tests.Elaborator.AnIdentityALinkDrops.AnIdentityALinkDrops
