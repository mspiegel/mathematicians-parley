module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition

theorem a_membership_bound_folding_a_definition (m : ℕ) (j : ℕ) (hH2 : 0 < j) (hH3 : (j : ℤ) ≤ (m : ℤ)) :
    (j : ℤ) ∈ Finset.Icc (1 : ℤ) (m : ℤ) := by
  -- 1. def:range-between k := j, a := 1, b := m, from H2, H3
  have s1 : (j : ℤ) ∈ Finset.Icc (1 : ℤ) (m : ℤ) := ((Parley.Items.Stdlib.Sums.def_range_between (k := (j : ℤ)) (a := (1 : ℤ)) (b := (m : ℤ)))).mpr (by parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundFoldingADefinition
