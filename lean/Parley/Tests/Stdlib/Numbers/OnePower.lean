module

public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.OnePower

theorem one_power (m : ℤ) :
    (1 ^ m : ℚ) = 1 := by
  -- 1. mun:numbers-one-power
  have s1 : (1 ^ m : ℚ) = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_one_power (m := m))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.OnePower
