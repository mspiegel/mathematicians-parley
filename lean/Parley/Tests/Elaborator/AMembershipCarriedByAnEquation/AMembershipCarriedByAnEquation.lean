module

public import Tactics

/-! Written from tests/elaborator/a-membership-carried-by-an-equation.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMembershipCarriedByAnEquation.AMembershipCarriedByAnEquation

theorem a_membership_carried_by_an_equation (a : ℤ → ℝ) (b : ℤ → ℝ) (x : ℂ) (hH4 : x = (a 0 : ℂ) + (b 0 : ℂ)) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H1, H2, H4
  have s1 : ∃ m : ℝ, (m : ℂ) = x := ⟨a 0 + b 0, by first | (push_cast; linarith [hH4]) | (rw [hH4]; push_cast; ring) | (rw [← hH4]; push_cast; ring) | exact hH4 | exact hH4.symm⟩
  all_goals parley_side

end Parley.Tests.Elaborator.AMembershipCarriedByAnEquation.AMembershipCarriedByAnEquation
