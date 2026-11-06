module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/powers-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient

theorem a_power_to_a_letter_of_a_quotient (b : ℤ) (hH1 : 0 ≤ b) (x : ℝ) :
    x * ((b : ℝ) / 5) ^ b.toNat = ((b : ℝ) / 5) ^ b.toNat * x := by
  -- 1. algebra
  have s1 : x * ((b : ℝ) / 5) ^ b.toNat = ((b : ℝ) / 5) ^ b.toNat * x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.PowersSaidOnce.APowerToALetterOfAQuotient
