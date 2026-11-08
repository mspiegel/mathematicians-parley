module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeSingle

theorem range_single (m : ℤ) :
    (Set.Icc m m : Set ℤ) = ({m} : Set ℤ) := by
  -- 1. mun:sums-range-single
  exact (Parley.Items.Stdlib.Sums.mun_range_single (m := m))

end Parley.Tests.Stdlib.Sums.RangeSingle
