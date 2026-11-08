module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition

theorem a_membership_bound_folding_a_definition (m : ℤ) (hH1 : 0 ≤ m) (j : ℤ) (hH2 : 0 < j) (hH3 : j ≤ m) :
    j ∈ Finset.Icc (1 : ℤ) m := by
  -- 1. def:range-between k := j, a := 1, b := m, from H2, H3
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m))).mpr (by parley_side); parley_side)

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition
