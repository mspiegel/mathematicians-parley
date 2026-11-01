module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted

theorem a_range_bound_contradicted (n : ℤ) (k : ℤ) (H2 : k ∈ Finset.Icc 1 n) :
    ¬ n < k := by
  -- 1. contradiction
  have s1 : ¬ n < k := by
    by_contra hc_S
    have S : n < k := by parley_suppose hc_S
    -- 1.1. inequalities, from S
    have s1_1 : ¬ k ≤ n := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted
