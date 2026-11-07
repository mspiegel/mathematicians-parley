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
  have s1 : (Set.Icc m m : Set ℤ) = ({m} : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_single (m := m)) | exact ((Parley.Items.Stdlib.Sums.mun_range_single (m := m))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_single (m := m)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_single (m := m)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_single (m := m)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeSingle
