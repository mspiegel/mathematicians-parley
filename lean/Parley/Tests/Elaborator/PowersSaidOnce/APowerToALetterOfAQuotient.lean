module

public import Tactics

/-! Written from tests/elaborator/powers-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient

theorem a_power_to_a_letter_of_a_quotient (b : ℕ) (x : ℝ) :
    x * ((b : ℝ) / 5) ^ b = ((b : ℝ) / 5) ^ b * x := by
  -- 1. algebra
  have s1 : x * ((b : ℝ) / 5) ^ b = ((b : ℝ) / 5) ^ b * x := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient
