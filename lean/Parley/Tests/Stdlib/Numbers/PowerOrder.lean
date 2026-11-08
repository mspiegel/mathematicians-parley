module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOrder

theorem power_order (a : ℝ) (m : ℤ) (n : ℤ) (hH4 : a > 1) :
    (m < n ↔ a ^ m < a ^ n) := by
  -- 1. mun:numbers-power-order, from H4
  exact (Parley.Items.Stdlib.Numbers.mun_power_order (a := a) (m := m) (n := n) (by parley_side))

end Parley.Tests.Stdlib.Numbers.PowerOrder
