module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-power-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero

theorem a_power_said_not_zero (n : ℤ) (hH1 : 0 < n) (ε : ℝ) (x : ℝ) (hH4 : x ^ n.toNat > 0) (hH5 : 1 / x ^ n.toNat < ε) :
    1 - ε < 1 - 1 / x ^ n.toNat := by
  -- 1. inequalities
  have r10_1 : x ^ n.toNat ≠ 0 := by parley_side
  parley_order

end Parley.Tests.Elaborator.APowerSaidNotZero.APowerSaidNotZero
