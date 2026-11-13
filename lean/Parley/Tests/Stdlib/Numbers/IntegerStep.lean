module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.IntegerStep

theorem integer_step (m : ℤ) (n : ℤ) (hH3 : m < n) :
    m + 1 ≤ n := by
  -- 1. mun:numbers-integer-step, from H3
  exact (Parley.Items.Stdlib.Numbers.mun_integer_step (m := m) (n := n) hH3)

end Parley.Tests.Stdlib.Numbers.IntegerStep
