module

public import Tactics

/-! Written from tests/elaborator/cited-conjunction.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedConjunction.DividedByACitedNatural

theorem divided_by_a_cited_natural (a : ℕ) (hH1 : 0 < a) (k : ℤ) (hH3 : (0 < k ∧ (∃ m : ℕ, 0 < m ∧ (m : ℚ) = (a : ℚ) / (k : ℚ))) ∧ (a : ℤ) > 1) :
    ((a : ℚ) / (k : ℚ)) ^ 2 = (a : ℚ) ^ 2 / (k : ℚ) ^ 2 := by
  -- 1. algebra, from H3
  have s1 : ((a : ℚ) / (k : ℚ)) ^ 2 = (a : ℚ) ^ 2 / (k : ℚ) ^ 2 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.CitedConjunction.DividedByACitedNatural
