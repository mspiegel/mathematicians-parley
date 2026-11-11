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

namespace Parley.Tests.Stdlib.Numbers.PowerOfPower

theorem power_of_power (z : ℂ) (j : ℤ) (hH2 : 0 ≤ j) (k : ℤ) (hH3 : 0 ≤ k) :
    z ^ (j * k).toNat = (z ^ j.toNat) ^ k.toNat := by
  -- 1. mun:numbers-power-of-power a := z, m := j, n := k
  exact (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) hH2 (n := k) hH3)

end Parley.Tests.Stdlib.Numbers.PowerOfPower
