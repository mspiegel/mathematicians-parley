module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerCancel

theorem power_cancel (a : ℝ) (m : ℤ) (n : ℤ) (hH4 : a > 1) :
    (a ^ m = a ^ n ↔ m = n) := by
  -- 1. mun:numbers-power-cancel, from H4
  have s1 : a ^ m = a ^ n ↔ m = n := by exact (Parley.Items.Stdlib.Numbers.mun_power_cancel (a := a) (m := m) (n := n) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerCancel
