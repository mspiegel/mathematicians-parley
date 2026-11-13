module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself

theorem an_instance_whose_condition_is_itself (a : ℤ) (b : ℤ) (hH3 : ∀ k : ℤ, k = a + b → a ≤ k) :
    a ≤ a + b := by
  -- 1. instantiate k := a + b in H3
  exact (hH3 (a + b) rfl)

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself
