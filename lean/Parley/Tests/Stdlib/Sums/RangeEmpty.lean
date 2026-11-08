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

namespace Parley.Tests.Stdlib.Sums.RangeEmpty

theorem range_empty :
    (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ := by
  -- 1. mun:sums-range-empty
  exact Parley.Items.Stdlib.Sums.mun_range_empty

end Parley.Tests.Stdlib.Sums.RangeEmpty
