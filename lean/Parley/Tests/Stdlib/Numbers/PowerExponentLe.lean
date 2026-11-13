module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerExponentLe

theorem power_exponent_le (c : ℝ) (j : ℤ) (hH2 : 0 ≤ j) (k : ℤ) (hH3 : 0 ≤ k) (hH4 : 1 ≤ c) (hH5 : j ≤ k) :
    c ^ j.toNat ≤ c ^ k.toNat := by
  -- 1. mun:numbers-power-exponent-le a := c, m := j, n := k, from H4, H5
  exact (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) hH2 (n := k) hH3 hH4 hH5)

end Parley.Tests.Stdlib.Numbers.PowerExponentLe
