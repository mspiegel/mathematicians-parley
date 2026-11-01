module

public import Parley.Library

/-! Written from tests/elaborator/an-instance-asking-the-fewest-conditions.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions

theorem an_instance_asking_the_fewest_conditions (H1 : (∀ x : ℝ, x > 0 → x + 0 = x) ∧ (∀ x : ℝ, x + 0 = x)) (a : ℝ) :
    a + 0 = a := by
  -- 1. instantiate x := a in H1, from H2
  have s1 : a + 0 = a := by linear_combination (H1.2 a)
  all_goals parley_side

end Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions
