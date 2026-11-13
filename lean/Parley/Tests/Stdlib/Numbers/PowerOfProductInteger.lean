module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfProductInteger

theorem power_of_product_integer (y : ℂ) (hH2 : y ≠ 0) (z : ℂ) (hH4 : z ≠ 0) (k : ℤ) :
    (y * z) ^ k = y ^ k * z ^ k := by
  -- 1. mun:numbers-power-of-product-integer a := y, b := z, n := k, from H2, H4
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) hH2 (b := z) hH4 (n := k))

end Parley.Tests.Stdlib.Numbers.PowerOfProductInteger
