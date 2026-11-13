module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
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

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition

theorem a_membership_bound_folding_a_definition (m : ℤ) (hH1 : 0 ≤ m) (j : ℤ) (hH2 : 0 < j) (hH3 : j ≤ m) :
    j ∈ Finset.Icc (1 : ℤ) m := by
  -- 1. def:range-between k := j, a := 1, b := m, from H2, H3
  exact ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m))).mpr ⟨hH2, hH3⟩

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition
