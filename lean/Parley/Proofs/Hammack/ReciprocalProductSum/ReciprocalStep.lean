module

public import Parley.Library

/-! Written from proofs/hammack/reciprocal-product-sum.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep

theorem reciprocal_step (m : ℕ) (hH1 : 0 < m) :
    1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
  -- 1. algebra
  have s1 : 1 / (m : ℚ) - 1 / ((m : ℚ) + 1) = 1 / ((m : ℚ) * ((m : ℚ) + 1)) := by parley_ring
  -- 2. calculation
  have s2 : 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / ((m : ℚ) + 1) := by
    calc 1 - 1 / (m : ℚ) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 - 1 / (m : ℚ) + (1 / (m : ℚ) - 1 / ((m : ℚ) + 1)) := by parley_subst s1
      _ = 1 - 1 / ((m : ℚ) + 1) := by parley_ring
  all_goals parley_side

end Parley.Proofs.Hammack.ReciprocalProductSum.ReciprocalStep
