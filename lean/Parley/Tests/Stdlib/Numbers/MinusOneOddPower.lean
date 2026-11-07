module

public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MinusOneOddPower

theorem minus_one_odd_power (n : ℤ) (hH2 : Odd n) :
    ((-1) ^ n : ℚ) = -1 := by
  -- 1. mun:numbers-minus-one-odd-power, from H2
  have s1 : ((-1) ^ n : ℚ) = -1 := by exact (Parley.Items.Stdlib.Numbers.mun_minus_one_odd_power (n := n) hH2)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.MinusOneOddPower
