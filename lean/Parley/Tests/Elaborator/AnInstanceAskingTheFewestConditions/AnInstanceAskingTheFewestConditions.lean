module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/an-instance-asking-the-fewest-conditions.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions

theorem an_instance_asking_the_fewest_conditions (hH1 : (∀ x : ℝ, x > 0 → x + 0 = x) ∧ (∀ x : ℝ, x + 0 = x)) (a : ℝ) :
    a + 0 = a := by
  -- 1. instantiate x := a in H1, from H2
  exact (hH1.2 a)

end Parley.Tests.Elaborator.AnInstanceAskingTheFewestConditions.AnInstanceAskingTheFewestConditions
