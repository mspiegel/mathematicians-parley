module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntegerStep

theorem integer_step (m : ℤ) (n : ℤ) (hH3 : m < n) :
    m + 1 ≤ n := by
  -- 1. mun:numbers-integer-step, from H3
  exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) hH3)

end Parley.Tests.Stdlib.Numbers.IntegerStep
