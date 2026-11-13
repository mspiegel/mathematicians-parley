module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/constant-left-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant

theorem one_equation_and_a_constant (s : ℝ) (hH2 : s = 1) :
    s ≥ 0 := by
  -- 1. inequalities
  have s1 : s ≥ 1 := by linarith only [hH2]
  -- 2. inequalities, from 1
  linarith only [s1]

end Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant
