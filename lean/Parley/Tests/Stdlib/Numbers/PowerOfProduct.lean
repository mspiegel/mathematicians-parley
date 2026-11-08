module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfProduct

theorem power_of_product (y : ℂ) (z : ℂ) (k : ℤ) (hH3 : 0 ≤ k) :
    (y * z) ^ k.toNat = y ^ k.toNat * z ^ k.toNat := by
  -- 1. mun:numbers-power-of-product a := y, b := z, n := k
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k) (by parley_side))

end Parley.Tests.Stdlib.Numbers.PowerOfProduct
