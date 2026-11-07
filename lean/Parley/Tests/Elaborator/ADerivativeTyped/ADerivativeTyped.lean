module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic

/-! Written from tests/elaborator/a-derivative-typed.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADerivativeTyped.ADerivativeTyped

theorem a_derivative_typed (f : ℝ → ℝ) (hH2 : True) :
    True := by
  -- 1. restate H2
  all_goals parley_side

end Parley.Tests.Elaborator.ADerivativeTyped.ADerivativeTyped
