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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentSum

theorem exponent_sum (a : ℝ) (m : ℤ) (hH2 : 0 ≤ m) (n : ℤ) (hH3 : 0 ≤ n) :
    a ^ (m + n).toNat = a ^ m.toNat * a ^ n.toNat := by
  -- 1. mun:numbers-exponent-sum
  exact (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) hH2 (n := n) hH3)

end Parley.Tests.Stdlib.Numbers.ExponentSum
