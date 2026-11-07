module

public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Tests.Notations.Powers.ARealPowerUnderABinder

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerUnderABinderCited

theorem a_real_power_under_a_binder_cited :
    (∀ z : ℝ, (2 : ℝ) ^ z > 0) := by
  -- 1. thm:a-real-power-under-a-binder
  have s1 : ∀ z : ℝ, (2 : ℝ) ^ z > 0 := by first | exact Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder | exact (Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder).symm | simpa using Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder | exact_mod_cast Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder | (have h := Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder; parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.ARealPowerUnderABinderCited
