module

public import Mathlib.Basic.Real.Basic
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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-function-on-a-longer-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange

theorem a_function_on_a_longer_range (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℝ) (m : ℤ) (hH3 : 0 < m) :
    True := by
  -- 1. mun:product-real a := 1, b := m, from H4
  exact trivial

end Parley.Tests.Elaborator.AFunctionOnALongerRange.AFunctionOnALongerRange
