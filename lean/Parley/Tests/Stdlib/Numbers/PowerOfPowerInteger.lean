module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfPowerInteger

theorem power_of_power_integer (z : ℂ) (hH2 : z ≠ 0) (j : ℤ) (k : ℤ) :
    z ^ (j * k) = (z ^ j) ^ k := by
  -- 1. mun:numbers-power-of-power-integer a := z, m := j, n := k, from H2
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_power_integer (a := z) (by parley_side) (m := j) (n := k))

end Parley.Tests.Stdlib.Numbers.PowerOfPowerInteger
