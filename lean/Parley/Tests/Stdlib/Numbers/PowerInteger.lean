module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerInteger

theorem power_integer (a : ℤ) (m : ℤ) (hH2 : 0 ≤ m) :
    True := by
  -- 1. mun:numbers-power-integer m := m + 1
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.PowerInteger
