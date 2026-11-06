module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFoldingADefinition

theorem a_range_bound_folding_a_definition (n : ℤ) (m : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) (hH4 : k ≤ m) :
    k ∈ Finset.Icc (1 : ℤ) m := by
  -- 1. def:range-between a := 1, b := m, from H3, H4
  have s1 : k ∈ Finset.Icc (1 : ℤ) m := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (1 : ℤ)) (b := m))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := (1 : ℤ)) (b := m))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundFoldingADefinition
