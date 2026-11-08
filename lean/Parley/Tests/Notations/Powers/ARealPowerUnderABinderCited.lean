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
  exact Parley.Tests.Notations.Powers.ARealPowerUnderABinder.a_real_power_under_a_binder

end Parley.Tests.Notations.Powers.ARealPowerUnderABinderCited
