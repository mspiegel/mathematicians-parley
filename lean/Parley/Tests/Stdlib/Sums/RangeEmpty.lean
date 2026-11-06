module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeEmpty

theorem range_empty :
    (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ := by
  -- 1. mun:sums-range-empty
  have s1 : (Set.Icc (1 : ℤ) (0 : ℤ) : Set ℤ) = ∅ := by first | exact Parley.Items.Stdlib.Sums.mun_range_empty | exact (Parley.Items.Stdlib.Sums.mun_range_empty).symm | simpa using Parley.Items.Stdlib.Sums.mun_range_empty | exact_mod_cast Parley.Items.Stdlib.Sums.mun_range_empty | (have h := Parley.Items.Stdlib.Sums.mun_range_empty; parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeEmpty
