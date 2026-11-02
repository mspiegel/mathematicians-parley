module

public import Parley.Library

/-! Written from tests/elaborator/an-instance-asking-the-fewest-conditions.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions

theorem an_instance_asking_the_fewest_conditions (hH1 : (∀ x : ℝ, x > 0 → x + 0 = x) ∧ (∀ x : ℝ, x + 0 = x)) (a : ℝ) :
    a + 0 = a := by
  -- 1. instantiate x := a in H1, from H2
  have s1 : a + 0 = a := by first | linear_combination (norm := parley_norm) (hH1.2 a) | (have h := (hH1.2 a); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | exact_mod_cast (hH1.2 a) | exact_mod_cast ((hH1.2 a)).symm | (have h := (hH1.2 a); rify; linear_combination (norm := parley_norm) h) | (have h := (hH1.2 a); qify; linear_combination (norm := parley_norm) h)
  all_goals parley_side

end Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions
