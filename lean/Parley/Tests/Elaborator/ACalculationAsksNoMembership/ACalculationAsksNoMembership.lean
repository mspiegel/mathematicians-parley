module

public import Parley.Library

/-! Written from tests/elaborator/a-calculation-asks-no-membership.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership

theorem a_calculation_asks_no_membership (k : ℕ) (hH1 : 0 < k) (y : ℝ) (hH3 : y ≤ 2 * (Nat.factorial k : ℝ)) (hH4 : 2 * (Nat.factorial k : ℤ) < 2 * (Nat.factorial k : ℤ) * 2) :
    y < 2 * (Nat.factorial k : ℝ) * 2 := by
  -- 1. calculation
  have s1 : y < 2 * (Nat.factorial k : ℝ) * 2 := by
    calc y ≤ 2 * (Nat.factorial k : ℝ) := by parley_side
      _ < 2 * (Nat.factorial k : ℝ) * 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ACalculationAsksNoMembership.ACalculationAsksNoMembership
