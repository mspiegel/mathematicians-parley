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

namespace Parley.Tests.Stdlib.Numbers.MinusOneEvenPower

theorem minus_one_even_power (n : ℤ) :
    ((-1) ^ (2 * n) : ℚ) = 1 := by
  -- 1. mun:numbers-minus-one-even-power
  have s1 : ((-1) ^ (2 * n) : ℚ) = 1 := by exact (Parley.Items.Stdlib.Numbers.mun_minus_one_even_power (n := n))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.MinusOneEvenPower
