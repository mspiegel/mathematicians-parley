module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/constant-left-over.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant

theorem one_equation_and_a_constant (s : ℝ) (hH2 : s = 1) :
    s ≥ 0 := by
  -- 1. inequalities
  have s1 : s ≥ 1 := by parley_order
  -- 2. inequalities, from 1
  have s2 : s ≥ 0 := by parley_order
  all_goals exact s2

end Parley.Tests.Elaborator.ConstantLeftOver.OneEquationAndAConstant
