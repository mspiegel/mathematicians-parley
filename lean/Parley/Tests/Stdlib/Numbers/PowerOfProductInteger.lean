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

namespace Parley.Tests.Stdlib.Numbers.PowerOfProductInteger

theorem power_of_product_integer (y : ℂ) (hH2 : y ≠ 0) (z : ℂ) (hH4 : z ≠ 0) (k : ℤ) :
    (y * z) ^ k = y ^ k * z ^ k := by
  -- 1. mun:numbers-power-of-product-integer a := y, b := z, n := k, from H2, H4
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k))

end Parley.Tests.Stdlib.Numbers.PowerOfProductInteger
