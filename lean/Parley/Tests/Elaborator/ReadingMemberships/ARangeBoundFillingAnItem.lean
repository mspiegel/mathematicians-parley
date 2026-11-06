module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem

theorem a_range_bound_filling_an_item (n : ℤ) (hH1 : 0 ≤ n) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ n - k := by
  -- 1. mun:difference-nat0, from H2
  have s1 : 0 ≤ n - k := by first | exact (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (by parley_side) (n := n) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (by parley_side) (n := n) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (by parley_side) (n := n) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (by parley_side) (n := n) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_difference_nat0 (m := k) (by parley_side) (n := n) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFillingAnItem
