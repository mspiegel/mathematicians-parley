module

public import Counting
public import Tactics

/-! Written from tests/elaborator/powers-said-once.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial

theorem a_power_whose_base_holds_a_factorial (b : ℕ) (x : ℝ) (z : ℂ) :
    (x : ℂ) * (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b = (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b * (x : ℂ) := by
  -- 1. algebra
  have s1 : (x : ℂ) * (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b = (z - (LeanBridges.Counting.factorial (4 : ℤ) : ℂ)) ^ b * (x : ℂ) := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.PowersSaidOnce.APowerWhoseBaseHoldsAFactorial
