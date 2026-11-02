module

public import LeanBridges

/-! Written from tests/elaborator/cited-equation-divisor-a-power.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.CitedEquationDivisorAPower.TheClaimDividesByAPower

theorem the_claim_divides_by_a_power (t : ℝ) (F : ℝ) (hH3 : t ≠ 0) (hH4 : F * t ^ 2 = 1) :
    F = 1 / t ^ 2 := by
  -- 1. algebra, from H4
  have r26_1 : t ≠ 0 := by parley_side
  have s1 : F = 1 / t ^ 2 := by linear_combination (norm := parley_field) ((1) / ((t ^ 2))) * hH4
  all_goals parley_side

end Parley.Tests.Elaborator.CitedEquationDivisorAPower.TheClaimDividesByAPower
