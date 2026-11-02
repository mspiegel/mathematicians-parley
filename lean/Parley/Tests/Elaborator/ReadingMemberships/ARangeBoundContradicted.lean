module

public import LeanBridges

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted

theorem a_range_bound_contradicted (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    ¬ n < k := by
  -- 1. contradiction
  have s1 : ¬ n < k := by
    by_contra hc_hS
    have hS : n < k := by parley_suppose hc_hS
    -- 1.1. inequalities, from S
    have s1_1 : ¬ k ≤ n := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundContradicted
