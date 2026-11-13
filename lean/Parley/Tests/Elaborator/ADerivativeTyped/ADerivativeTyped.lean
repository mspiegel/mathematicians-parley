module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/a-derivative-typed.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADerivativeTyped.ADerivativeTyped

theorem a_derivative_typed (f : ℝ → ℝ) :
    True := by
  -- 1. restate H2
  exact trivial

end Parley.Tests.Elaborator.ADerivativeTyped.ADerivativeTyped
