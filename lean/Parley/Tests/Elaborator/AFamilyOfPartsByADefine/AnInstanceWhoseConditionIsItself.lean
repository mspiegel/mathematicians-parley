module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-family-of-parts-by-a-define.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself

theorem an_instance_whose_condition_is_itself (a : ℤ) (b : ℤ) (hH3 : ∀ k : ℤ, k = a + b → a ≤ k) :
    a ≤ a + b := by
  -- 1. instantiate k := a + b in H3
  exact (hH3 (a + b) rfl)

end Parley.Tests.Elaborator.AFamilyOfPartsByADefine.AnInstanceWhoseConditionIsItself
