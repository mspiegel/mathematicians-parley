module

public import Tactics
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerNat0

theorem power_nat0 (a : ℤ) (hH1 : 0 ≤ a) (m : ℤ) (hH2 : 0 ≤ m) :
    0 ≤ a ^ (m + 1).toNat := by
  -- 1. mun:numbers-power-nat0 m := m + 1
  have s1 : 0 ≤ a ^ (m + 1).toNat := by exact (Parley.Items.Stdlib.Numbers.mun_power_nat0 (a := a) (by parley_side) (m := m + 1) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerNat0
